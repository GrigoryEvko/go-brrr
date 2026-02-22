//! Benchmarks for the F* parser hot paths.
//!
//! Run with: cargo bench --bench parser_bench
//!
//! Covers:
//! - `parse_fstar_file`: full file parsing into declaration blocks
//! - `strip_comments_and_strings`: comment/string removal (used in reference extraction)
//! - `extract_references`: identifier dependency extraction
//! - `is_header_line` / `get_declaration_info`: per-line classification (called for every line)
//! - `is_standalone_options` / `is_push_options` / `is_pop_options`: directive detection

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::collections::HashSet;

use brrr_lint::lint::parser;

/// Synthetic F* file content with realistic patterns from HACL*/EverParse.
/// ~100 lines covering module header, opens, options, val/let/type declarations,
/// comments, mutual recursion, Low* buffer types, and effect annotations.
const MEDIUM_FSTAR_CONTENT: &str = r#"module Bench.Example

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Specification of the hash function. *)
val hash_spec : a:hash_alg -> input:bytes -> Tot (lbytes (hash_length a))

(** Implementation state type -- abstract. *)
noeq type state_s (a: hash_alg) = {
  block: lbuffer uint8 (block_len a);
  hash_buf: lbuffer uint8 (hash_len a);
  total_len: UInt64.t;
}

type state (a: hash_alg) = B.pointer (state_s a)

[@@"opaque_to_smt"]
val alloc : a:hash_alg -> ST (state a)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    live h1 (B.deref h1 s).block /\
    live h1 (B.deref h1 s).hash_buf /\
    fresh_loc (loc_buffer s) h0 h1)

#push-options "--fuel 1"

(* Helper lemma for modular arithmetic *)
val mod_lemma : a:nat -> b:pos -> Lemma
  (ensures (a % b < b))
  [SMTPat (a % b)]
let mod_lemma a b = ()

#pop-options

inline_for_extraction noextract
let update_block (#a: hash_alg) (st: state a) (block: lbuffer uint8 (block_len a)) : Stack unit
  (requires fun h ->
    live h st /\ live h block /\
    disjoint (B.deref h st).block block)
  (ensures fun h0 _ h1 ->
    modifies (loc_buffer st) h0 h1)
=
  push_frame ();
  let h0 = ST.get () in
  let s = B.index st 0ul in
  (* Inner computation: copy block into state *)
  let dst = s.block in
  B.blit block 0ul dst 0ul (block_len a);
  let total = s.total_len in
  let new_total = FStar.UInt64.(total +^ 1UL) in
  B.upd st 0ul ({ s with total_len = new_total });
  pop_frame ()

(** Mutual recursion example. *)
type expr =
  | ELit : int -> expr
  | EAdd : expr -> expr -> expr
  | ESeq : stmt -> expr -> expr
and stmt =
  | SExpr : expr -> stmt
  | SLet  : string -> expr -> stmt -> stmt

val eval : expr -> Tot int (decreases expr)
let rec eval e =
  match e with
  | ELit n -> n
  | EAdd a b -> eval a + eval b
  | ESeq s rest -> exec s; eval rest
and exec (s: stmt) : Tot unit (decreases s) =
  match s with
  | SExpr e -> let _ = eval e in ()
  | SLet _ e body -> let _ = eval e in exec body

// Final utility
let hash_length (a: hash_alg) : n:nat{n > 0} =
  match a with
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64
"#;

/// Large synthetic content: repeat the medium content multiple times.
fn make_large_content(repeat: usize) -> String {
    let mut content = String::from("module Bench.Large\n\nopen FStar.All\n\n");
    let body_lines: Vec<&str> = MEDIUM_FSTAR_CONTENT
        .lines()
        .skip(2) // skip module header
        .collect();
    let body = body_lines.join("\n");
    for i in 0..repeat {
        // Mangle names to avoid duplicate declarations
        content.push_str(&body.replace("hash_spec", &format!("hash_spec_{}", i))
                              .replace("state_s", &format!("state_s_{}", i))
                              .replace("alloc", &format!("alloc_{}", i))
                              .replace("mod_lemma", &format!("mod_lemma_{}", i))
                              .replace("update_block", &format!("update_block_{}", i))
                              .replace("eval", &format!("eval_{}", i))
                              .replace("exec", &format!("exec_{}", i))
                              .replace("hash_length", &format!("hash_length_{}", i)));
        content.push('\n');
    }
    content
}

fn bench_parse_fstar_file(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_fstar_file");

    group.bench_function("medium_100_lines", |b| {
        b.iter(|| parser::parse_fstar_file(black_box(MEDIUM_FSTAR_CONTENT)))
    });

    let large = make_large_content(10);
    group.bench_with_input(
        BenchmarkId::new("large", format!("{}_lines", large.lines().count())),
        &large,
        |b, content| b.iter(|| parser::parse_fstar_file(black_box(content))),
    );

    group.finish();
}

fn bench_strip_comments_and_strings(c: &mut Criterion) {
    let mut group = c.benchmark_group("strip_comments_and_strings");

    let text_no_comments = "val foo : int -> int\nlet foo x = x + 1\n".repeat(50);
    group.bench_with_input(
        BenchmarkId::new("no_comments", text_no_comments.len()),
        &text_no_comments,
        |b, t| b.iter(|| parser::strip_comments_and_strings(black_box(t))),
    );

    let text_with_comments = r#"(* Module documentation
   spanning multiple lines *)
val foo : int -> int (* inline comment *)
let foo x =
  (* nested (* deep *) comment *)
  let y = "string with (* markers *)" in
  x + 1
"#.repeat(20);
    group.bench_with_input(
        BenchmarkId::new("with_comments", text_with_comments.len()),
        &text_with_comments,
        |b, t| b.iter(|| parser::strip_comments_and_strings(black_box(t))),
    );

    group.finish();
}

fn bench_extract_references(c: &mut Criterion) {
    let mut group = c.benchmark_group("extract_references");

    let text = r#"val process : #a:hash_alg -> st:state a -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h st /\ live h input /\ disjoint st input)
    (ensures fun h0 _ h1 -> modifies (loc_buffer st) h0 h1)
let process #a st input =
  let h0 = ST.get () in
  let s = B.index st 0ul in
  B.blit input 0ul s.block 0ul (block_len a);
  FStar.Math.Lemmas.lemma_mod_plus (UInt64.v s.total_len) 1 (block_len a)
"#;
    let exclude: HashSet<String> = ["process"].iter().map(|s| s.to_string()).collect();

    group.bench_function("lowstar_declaration", |b| {
        b.iter(|| parser::extract_references(black_box(text), black_box(&exclude)))
    });

    group.finish();
}

fn bench_per_line_classification(c: &mut Criterion) {
    let mut group = c.benchmark_group("per_line_classification");

    let lines = vec![
        "val foo : int -> int",
        "let foo x = x + 1",
        "type mytype = int",
        "open FStar.HyperStack.ST",
        "module ST = FStar.HyperStack.ST",
        "#set-options \"--z3rlimit 50\"",
        "#push-options \"--fuel 1\"",
        "#pop-options",
        "  let inner = x + 1 in",  // indented -- should be skipped
        "(* block comment *)",
        "// line comment",
        "inline_for_extraction noextract",
        "[@@\"opaque_to_smt\"]",
        "and b = B of a",
        "class hashable (a:Type) = { hash_fn: a -> nat }",
        "instance hashable_int : hashable int = { hash_fn = fun x -> x }",
        "exception ParseError of string",
    ];

    group.bench_function("is_header_line", |b| {
        b.iter(|| {
            for line in &lines {
                black_box(parser::is_header_line(black_box(line)));
            }
        })
    });

    group.bench_function("get_declaration_info", |b| {
        b.iter(|| {
            for line in &lines {
                black_box(parser::get_declaration_info(black_box(line)));
            }
        })
    });

    group.bench_function("is_standalone_options", |b| {
        b.iter(|| {
            for line in &lines {
                black_box(parser::is_standalone_options(black_box(line)));
            }
        })
    });

    group.bench_function("is_push_pop_options", |b| {
        b.iter(|| {
            for line in &lines {
                black_box(parser::is_push_options(black_box(line)));
                black_box(parser::is_pop_options(black_box(line)));
            }
        })
    });

    group.finish();
}

fn bench_count_comment_opens_closes(c: &mut Criterion) {
    let mut group = c.benchmark_group("count_comment_opens_closes");

    let simple = "let foo x = x + 1";
    let nested = r#"(* outer (* inner *) "string" outer *) let x = 1"#;

    group.bench_function("no_comments", |b| {
        b.iter(|| parser::count_comment_opens_closes(black_box(simple)))
    });

    group.bench_function("nested_comments", |b| {
        b.iter(|| parser::count_comment_opens_closes(black_box(nested)))
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_fstar_file,
    bench_strip_comments_and_strings,
    bench_extract_references,
    bench_per_line_classification,
    bench_count_comment_opens_closes,
);
criterion_main!(benches);
