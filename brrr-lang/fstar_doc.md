
● I'll launch 15 elite-bug-hunter agents in parallel, each writing a comprehensive documentation chapter for a specific part of the F* codebase.                                                                                                  02:26 AM  claude-opus-4-5-20251101

● elite-bug-hunter(F* Ch1: Compiler Architecture)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering COMPILER ARCHITECTURE OVERVIEW.

       Explore the F* codebase at /home/grigory/Downloads/FStar/src/ extensively.

       Focus on:
       1. Read FStarC.Main.fst completely - document the entry point, command-line parsing, compilation orchestration
       2. Read FStarC.Universal.fst completely - document the high-level compilation pipeline
       3. Read FStarC.Dependencies.fst and FStarC.CheckedFiles.fst - understand module caching
       4. Trace the complete compilation flow: source file → parsing → desugaring → type checking → extraction
       5. Document the 3-stage bootstrap process (stage0, stage1, stage2)
       6. Explain how F* self-hosts (compiles itself)

       Your chapter should include:
       - Architecture diagram (text-based)
       - Phase-by-phase explanation with file references
       - Key data structures passed between phases
       - Configuration and options handling
       - Error propagation strategy
       - When/how users interact with each phase

       Read at least 10 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive information to write the documentation chapter. Here is the complete chapter:

       ---
       F* COMPILER ARCHITECTURE OVERVIEW

       Chapter Overview

       This chapter provides a comprehensive technical documentation of the F* compiler architecture, covering the complete compilation pipeline from source files to verified modules and extracted code. F* is a self-hosting proof assistant and functional programming language,
       meaning the compiler is itself written in F* and bootstrapped through a multi-stage process.

       ---
       1. HIGH-LEVEL ARCHITECTURE DIAGRAM

                                     F* COMPILER ARCHITECTURE
           +===========================================================================+
           |                                                                           |
           |   SOURCE FILES (.fst/.fsti)                                               |
           |         |                                                                 |
           |         v                                                                 |
           |   +-------------+     +------------------+     +---------------------+    |
           |   |   PARSER    |---->|   DESUGARING     |---->|   TYPE CHECKER      |    |
           |   | (ParseIt)   |     | (ToSyntax)       |     | (TypeChecker.Tc)    |    |
           |   +-------------+     +------------------+     +---------------------+    |
           |         |                     |                        |                  |
           |         v                     v                        v                  |
           |   +-----------+        +------------+          +---------------+          |
           |   | AST.modul |        | Syntax.modul|          | Syntax.modul  |          |
           |   | (Parser)  |        | (desugared)|          | (type-checked)|          |
           |   +-----------+        +------------+          +---------------+          |
           |                                                        |                  |
           |                                                        v                  |
           |                               +-----------------------------------------+ |
           |                               |         SMT ENCODING                    | |
           |                               |    (SMTEncoding.Encode)                 | |
           |                               +-----------------------------------------+ |
           |                                                        |                  |
           |                                                        v                  |
           |                               +-----------------------------------------+ |
           |                               |          Z3 SOLVER                      | |
           |                               |    (SMTEncoding.Solver)                 | |
           |                               +-----------------------------------------+ |
           |                                                        |                  |
           |                                                        v                  |
           |   +------------------------------------------------------------------+   |
           |   |                       EXTRACTION                                 |   |
           |   |  +------------+  +-----------+  +----------+  +---------------+  |   |
           |   |  |   OCaml    |  |  FSharp   |  |  Krml    |  |    Plugin     |  |   |
           |   |  | (.ml)      |  | (.fs)     |  | (.krml)  |  | (.cmxs)       |  |   |
           |   |  +------------+  +-----------+  +----------+  +---------------+  |   |
           |   +------------------------------------------------------------------+   |
           |                                                                           |
           |   +------------------------------------------------------------------+   |
           |   |                    CHECKED FILES CACHE                           |   |
           |   |  - Parsing data (stage 1)                                        |   |
           |   |  - Type checking result + SMT decls (stage 2)                    |   |
           |   |  - Dependency hashes for invalidation                            |   |
           |   +------------------------------------------------------------------+   |
           |                                                                           |
           +===========================================================================+

           ENVIRONMENT THREADING:

           +--------+     +--------+     +--------+     +--------+
           | DsEnv  |---->| TcEnv  |---->| UEnv   |---->| TcEnv  |
           | (desugar)    | (typecheck)  | (extract)    | (final)|
           +--------+     +--------+     +--------+     +--------+

       ---
       2. ENTRY POINT: FStarC.Main

       The compiler entry point is defined in /home/grigory/Downloads/FStar/src/fstar/FStarC.Main.fst. This module orchestrates the entire compilation process.

       2.1 Main Function Structure

       // FStarC.Main.fst:500-514
       let main () =
         try
           let _, time = Timing.record_ms go in
           if FStarC.Options.query_stats()
           then print2_error "TOTAL TIME %s ms: %s\n"
                     (show time)
                     (String.concat " " (FStarC.Getopt.cmdline()));
           print_stats();
           cleanup ();
           exit 0
         with
         | e ->
           handle_error e;
           print_stats();
           exit 1

       The main function:
       1. Calls go() which dispatches to the appropriate mode
       2. Records execution time for profiling
       3. Handles exceptions through handle_error
       4. Ensures cleanup of subprocesses (Z3 instances)

       2.2 Command-Line Parsing and Mode Dispatch

       // FStarC.Main.fst:52-54
       let process_args () : parse_cmdline_res & list string =
         Options.parse_cmd_line ()

       The go_normal() function (lines 152-459) handles the primary dispatch logic:

       // FStarC.Main.fst:210-246 (key dispatch cases)
       match res with
         | _ when Options.help () ->
           Options.display_usage();
           exit 0

         | Success when Options.dep () <> None ->
           // Dependency analysis mode
           load_native_tactics ();
           let _, deps = Parser.Dep.collect filenames ... in
           Parser.Dep.print deps;
           report_errors []

         | Success when Options.print () || Options.print_in_place () ->
           // Pretty-printing mode
           Prettyprint.generate printing_mode filenames

         | Success ->
           // Normal batch or interactive mode
           if Options.interactive () then
             Interactive.Ide.interactive_mode filename
           else begin
             // Batch mode: full compilation
             let tcrs, env, cleanup = Universal.batch_mode_tc fly_deps filenames dep_graph in
             ...
           end

       2.3 Key Operational Modes

       | Mode        | Flag      | Description                                   |
       |-------------|-----------|-----------------------------------------------|
       | Batch       | (default) | Type-check files, verify, optionally extract  |
       | Interactive | --ide     | LSP-like IDE support for incremental checking |
       | Dependency  | --dep     | Compute and print module dependencies         |
       | Print       | --print   | Pretty-print source files                     |
       | Lax         | --lax     | Skip SMT verification                         |

       ---
       3. HIGH-LEVEL PIPELINE: FStarC.Universal

       The /home/grigory/Downloads/FStar/src/fstar/FStarC.Universal.fst module provides the high-level compilation orchestration.

       3.1 Batch Mode Type Checking

       // FStarC.Universal.fst:869-887
       let batch_mode_tc fly_deps filenames dep_graph =
         if !dbg_dep then begin
           Format.print_string "Auto-deps kicked in; here's some info.\n";
           Format.print1 "Here's the list of filenames we will process: %s\n"
             (String.concat " " filenames);
         end;
         let env = FStarC.Extraction.ML.UEnv.new_uenv (init_env dep_graph) in
         let all_mods, mllibs, env = tc_fold_interleave fly_deps ([], [], env) filenames in
         if FStarC.Errors.get_err_count() = 0 then
           emit dep_graph mllibs;
         let solver_refresh env =
             snd <|
             with_tcenv_of_env env (fun tcenv ->
                tcenv.solver.finish();
               (), tcenv)
         in
         all_mods, env, solver_refresh

       The batch mode:
       1. Creates initial environment from dependency graph
       2. Folds over all files using tc_fold_interleave
       3. Emits extracted code if no errors
       4. Returns results and cleanup function

       3.2 Environment Initialization

       // FStarC.Universal.fst:832-863
       let init_env deps : TcEnv.env =
         let solver =
           if Options.lax()
           then SMT.dummy
           else {SMT.solver with
             preprocess=FStarC.Tactics.Hooks.preprocess;
             spinoff_strictly_positive_goals=Some FStarC.Tactics.Hooks.spinoff_strictly_positive_goals;
             handle_smt_goal=FStarC.Tactics.Hooks.handle_smt_goal
           } in
         let env =
             TcEnv.initial_env
               deps
               TcTerm.tc_term
               TcTerm.typeof_tot_or_gtot_term
               TcTerm.typeof_tot_or_gtot_term_fastpath
               TcTerm.universe_of
               Rel.teq_nosmt_force
               Rel.subtype_nosmt_force
               solver
               Const.prims_lid
               (NBE.normalize (FStarC.Tactics.Interpreter.primitive_steps ()))
               core_check
         in
         (* Set up tactics callbacks *)
         let env = { env with synth_hook = FStarC.Tactics.Hooks.synthesize } in
         let env = { env with splice = FStarC.Tactics.Hooks.splice} in
         ...
         env.solver.init env;
         env

       The environment is initialized with:
       - SMT solver interface (or dummy for lax mode)
       - Type checker callbacks (tc_term, typeof_tot_or_gtot_term, etc.)
       - NBE (Normalization by Evaluation) normalizer
       - Tactics hooks for metaprogramming

       3.3 Single File Processing

       // FStarC.Universal.fst:401-604
       let rec tc_one_file_internal
               (fly_deps:bool)
               (env:uenv)
               (interface_fn:option string)
               (fn:string)
           : tc_result & option MLSyntax.mlmodule & uenv =
         Stats.record "tc_one_file" fun () ->
         GenSym.reset_gensym();
         ...

       Each file goes through:
       1. Cache check: Try to load from .checked file
       2. Parsing: Parser.Driver.parse_file
       3. Desugaring: Desugar.ast_modul_to_modul
       4. Type checking: Tc.check_module
       5. SMT encoding: SMTEncoding.Encode.encode_modul
       6. Extraction (optional): Extraction.ML.Modul.extract
       7. Cache storage: Write .checked file

       ---
       4. PHASE 1: PARSING

       4.1 Parser Driver

       // FStarC.Parser.Driver.fst:54-65
       let parse_file fn =
           match ParseIt.parse None (Filename fn) with
           | ASTFragment (Inl ast, comments) ->
               ast, comments
           | ASTFragment (Inr _ , _) ->
               let msg = Format.fmt1 "%s: expected a module\n" fn in
               raise_error r Errors.Fatal_ModuleExpected msg
           | ParseError (e, msg, r) ->
               raise_error r e msg
           | Term _ ->
               failwith "Impossible: parsing a Filename always results in an ASTFragment"

       The parser produces an AST defined in /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.AST.fsti.

       4.2 Parser AST Structure

       // FStarC.Parser.AST.fsti:46-111 (key term constructors)
       type term' =
         | Wild
         | Const     of sconst
         | Op        of ident & list term
         | Var       of lid
         | Name      of lid
         | Abs       of list pattern & term
         | App       of term & term & imp
         | Let       of local_let_qualifier & list (option attributes_ & (pattern & term)) & term
         | Match     of term & option ident & option match_returns_annotation & list branch
         | Ascribed  of term & term & option term & bool
         | Product   of list binder & term    (* function space *)
         | Refine    of binder & term
         | Quote     of term & quote_kind
         ...

       and term = {tm:term'; range:range; level:level}

       Key characteristics:
       - Unstratified: A single term type contains expressions, types, kinds
       - Source locations: Every node carries a range
       - Levels: Terms tagged with Un | Expr | Type_level | Kind | Formula

       4.3 Module Structure

       // FStarC.Parser.AST.fsti:273-285
       type modul =
         | Module of { mname:lid; decls:list decl; no_prelude:bool }
         | Interface of { mname:lid; decls:list decl; no_prelude:bool }

       ---
       5. PHASE 2: DESUGARING (ToSyntax)

       The desugaring phase transforms Parser.AST to Syntax.Syntax, performing name resolution, macro expansion, and syntactic transformations.

       5.1 Desugaring Interface

       // FStarC.ToSyntax.ToSyntax.fsti:40-43
       val ast_modul_to_modul:          AST.modul -> withenv Syntax.modul
       val decls_to_sigelts:            list AST.decl -> withenv sigelts
       val partial_ast_modul_to_modul:  option S.modul -> AST.modul -> withenv Syntax.modul

       The withenv type threads the desugaring environment:

       // FStarC.Syntax.DsEnv.fsti
       type withenv 'a = env -> 'a & env

       5.2 Core Syntax AST

       The desugared syntax is defined in /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti:

       // FStarC.Syntax.Syntax.fsti:123-174 (core term constructors)
       type term' =
         | Tm_bvar       of bv                // bound variable (de Bruijn index)
         | Tm_name       of bv                // local constant (unique name)
         | Tm_fvar       of fv                // fully qualified top-level reference
         | Tm_uinst      of term & universes  // universe instantiation
         | Tm_constant   of sconst
         | Tm_type       of universe
         | Tm_abs        { bs:binders; body:term; rc_opt:option residual_comp }
         | Tm_arrow      { bs:binders; comp:comp }
         | Tm_refine     { b:bv; phi:term }
         | Tm_app        { hd:term; args:args }
         | Tm_match      { scrutinee:term; ret_opt:option match_returns_ascription;
                           brs:list branch; rc_opt:option residual_comp }
         | Tm_ascribed   { tm:term; asc:ascription; eff_opt:option lident }
         | Tm_let        { lbs:letbindings; body:term }
         | Tm_uvar       of ctx_uvar_and_subst   // unification variable
         | Tm_delayed    { tm:term; substs:subst_ts }  // delayed substitution
         | Tm_meta       { tm:term; meta:metadata }
         | Tm_lazy       of lazyinfo
         | Tm_quoted     of term & quoteinfo
         | Tm_unknown

       Key differences from Parser AST:
       - De Bruijn indices for bound variables (Tm_bvar)
       - Explicit universe handling (Tm_uinst, Tm_type)
       - Unification variables (Tm_uvar)
       - Delayed substitutions (Tm_delayed)

       5.3 Interleaving Interface and Implementation

       // FStarC.Universal.fst:91-123
       let parse (fly_deps:bool) (env:uenv) (interface_fn: option string) (fn:string)
         : lident & either FStarC.Parser.AST.modul FStarC.Syntax.Syntax.modul & uenv =
         let ast, _ = Parser.Driver.parse_file fn in
         let ast, env = match interface_fn with
           | None -> ast, env
           | Some interface_fn ->
               let pre_ast, _ = Parser.Driver.parse_file interface_fn in
               match pre_ast, ast with
               | Parser.AST.Interface {mname=lid1; decls=decls1},
                 Parser.AST.Module {mname=lid2; decls=decls2}
                 when Ident.lid_equals lid1 lid2 ->
                 let _, env =
                   with_dsenv_of_env env
                     (FStarC.ToSyntax.Interleave.initialize_interface lid1 decls1)
                 in
                 with_dsenv_of_env env
                   (FStarC.ToSyntax.Interleave.interleave_module ast true)
               ...

       When both .fsti (interface) and .fst (implementation) exist for a module, they are interleaved: interface declarations are merged with implementation definitions.

       ---
       6. PHASE 3: TYPE CHECKING

       The type checker is the core of F*. It lives in /home/grigory/Downloads/FStar/src/typechecker/.

       6.1 Type Checker Environment

       // FStarC.TypeChecker.Env.fsti:165-200 (env record, partial)
       and env = {
         solver         :solver_t;           (* SMT solver interface *)
         range          :Range.t;            (* current source location *)
         curmodule      :lident;             (* current module name *)
         gamma          :list binding;       (* local typing environment *)
         gamma_sig      :list sig_binding;   (* signature elements *)
         gamma_cache    :SMap.t cached_elt;  (* memo table *)
         modules        :list modul;         (* checked modules *)
         expected_typ   :option (typ & bool);(* expected type from context *)
         sigtab         :SMap.t sigelt;      (* long-names to sigelts *)
         effects        :effects;            (* effect lattice *)
         generalize     :bool;               (* generalize let bindings? *)
         top_level      :bool;               (* top-level term? *)
         admit          :bool;               (* admit VCs? *)
         phase1         :bool;               (* two-phase typing *)
         
         (* Callbacks *)
         tc_term :env -> term -> term & lcomp & guard_t;
         typeof_tot_or_gtot_term :env -> term -> must_tot -> term & typ & guard_t;
         universe_of :env -> term -> universe;
         ...
       }

       The environment carries:
       - Local and global binding information
       - Effect lattice for monadic computations
       - SMT solver interface
       - Callbacks for recursive checking

       6.2 Module Type Checking

       // FStarC.TypeChecker.Tc.fst:100-200 (partial, key functions)

       let tc_type_common (env:env) ((uvs, t):tscheme) (expected_typ:typ) (r:Range.t) :tscheme =
         let uvs, t = SS.open_univ_vars uvs t in
         let env = Env.push_univ_vars env uvs in
         let t = tc_check_trivial_guard env t expected_typ in
         if uvs = [] then
           let uvs, t = Gen.generalize_universes env t in
           TcUtil.check_uvars r t;
           uvs, t
         else uvs, t |> N.remove_uvar_solutions env |> SS.close_univ_vars uvs

       The type checker:
       1. Opens universe-polymorphic types
       2. Checks against expected types
       3. Generalizes universes when appropriate
       4. Verifies no unresolved unification variables remain

       6.3 Two-Phase Type Checking

       F* uses two-phase type checking for better error messages and incremental development:

       // FStarC.TypeChecker.Env.fsti:187
         phase1         :bool;   (* running in phase 1, phase 2 to come after *)

       Phase 1 performs lightweight checking, Phase 2 performs full verification.

       ---
       7. SMT ENCODING AND VERIFICATION

       7.1 SMT Encoding Pipeline

       // FStarC.Universal.fst:456-462 (within tc_source_file)
       let smt_decls =
         if not (Options.lax())
         then FStarC.SMTEncoding.Encode.encode_modul (tcenv_of_uenv env) modul
         else [], []

       The SMT encoding translates F* types and terms to SMT-LIB formulas understood by Z3.

       7.2 Solver Interface

       // FStarC.SMTEncoding.Solver.fsti:20-24
       val with_hints_db : string -> (unit -> 'a) -> 'a
       val flush_hints () : unit

       val dummy: FStarC.TypeChecker.Env.solver_t
       val solver: FStarC.TypeChecker.Env.solver_t

       Key SMT encoding files:
       - FStarC.SMTEncoding.Encode.fst (113KB) - Main encoding logic
       - FStarC.SMTEncoding.EncodeTerm.fst (80KB) - Term encoding
       - FStarC.SMTEncoding.Term.fst (52KB) - SMT term AST
       - FStarC.SMTEncoding.Z3.fst (29KB) - Z3 process management

       7.3 Hints Database

       F* maintains a hints database to speed up re-verification:

       // FStarC.Universal.fst:498-499
       SMT.with_hints_db (Pars.find_file fn) check_mod

       Hints cache Z3 proof state and are stored in .hints files.

       ---
       8. EXTRACTION

       8.1 Extraction Targets

       // FStarC.Options.fsti:32-38
       type codegen_t =
         | OCaml       // Extract to OCaml (.ml)
         | FSharp      // Extract to F# (.fs)
         | Krml        // Extract to Karamel IR (.krml)
         | Plugin      // Extract as F* plugin (.cmxs)
         | PluginNoLib // Plugin without library
         | Extension   // Extension format

       8.2 Extraction Pipeline

       // FStarC.Universal.fst:301-392 (emit function)
       let emit dep_graph (mllib : list (uenv & MLSyntax.mlmodule)) =
         let opt = Options.codegen () in
         if opt <> None then
           match opt with
           | Some Options.FSharp | Some Options.OCaml | Some Options.Plugin | Some Options.PluginNoLib ->
             let printer =
               if opt = Some Options.FSharp
               then FStarC.Extraction.ML.PrintFS.print_fs
               else FStarC.Extraction.ML.PrintML.print_ml
             in
             mllib |> List.iter (fun (_, mlmodule) ->
               let p, _ = mlmodule in
               let filename = ... in
               let ml = printer mlmodule in
               write_file filename ml)

           | Some Options.Krml ->
             let programs =
               mllib |> List.collect (fun (ue, m) -> Extraction.Krml.translate ue [m])
             in
             let bin: Extraction.Krml.binary_format = Extraction.Krml.current_version, programs in
             save_value_to_file oname bin

       Key extraction files:
       - FStarC.Extraction.ML.Modul.fst (53KB) - Module extraction
       - FStarC.Extraction.ML.Term.fst (97KB) - Term extraction
       - FStarC.Extraction.ML.Code.fst (32KB) - Code generation
       - FStarC.Extraction.Krml.fst (58KB) - Karamel extraction

       ---
       9. CHECKED FILES AND CACHING

       9.1 Cache Structure

       // FStarC.CheckedFiles.fst:43-66
       type checked_file_entry_stage1 = {
         version: int;           // cache format version
         digest: string;         // source file hash
         parsing_data: Parser.Dep.parsing_data
       }

       type checked_file_entry_stage2 = {
         deps_dig: list (string & string);  // dependency digests
         tc_res: tc_result                   // type checking result
       }

       9.2 Cache Version

       // FStarC.CheckedFiles.fst:38
       let cache_version_number = 76

       The cache version number (currently 76) must match between the compiler and cache files. It's incremented when the internal representation changes.

       9.3 Two-Stage Loading

       // FStarC.CheckedFiles.fst:88-97
       type tc_result_t =
         | Unknown                    // Not yet validated
         | Invalid of string          // Validation failed (reason)
         | Valid   of string          // Validated (digest)

       Cache loading is two-stage:
       1. Stage 1: Load parsing data (for dependency analysis)
       2. Stage 2: Load type checking result (when actually needed)

       This allows efficient dependency analysis without loading full type checking data.

       9.4 Cache Validation

       // FStarC.CheckedFiles.fst:165-242
       let hash_dependences (deps:Dep.deps) (fn:string) (deps_of_fn:list string)
         : either string (list (string & string)) =
         ...
         let rec hash_deps out = function
         | [] -> maybe_add_iface_hash out
         | fn::deps ->
           let cache_fn = Dep.cache_file_name fn in
           let digest = match try_find_in_cache cache_fn with
             | None -> Inl msg
             | Some (Invalid msg, _) -> Inl msg
             | Some (Valid dig, _)   -> Inr dig
             | Some (Unknown, _)     -> failwith "Impossible"
           in
           match digest with
           | Inl msg -> Inl msg
           | Inr dig -> hash_deps ((Dep.lowercase_module_name fn, dig) :: out) deps
         in
         hash_deps [] binary_deps

       Cache is invalidated when:
       - Source file digest changes
       - Any dependency's cache digest changes
       - Cache version number differs

       ---
       10. DEPENDENCY ANALYSIS

       10.1 Dependency Collection

       // FStarC.Dependencies.fst:32-42
       let find_deps_if_needed files
         (get_parsing_data_from_cache:string -> option Parser.Dep.parsing_data)
         = let all_files, deps = Parser.Dep.collect files get_parsing_data_from_cache in
           match all_files with
           | [] ->
               Errors.log_issue0 Errors.Error_DependencyAnalysisFailed
                 "Dependency analysis failed; reverting to using only the files provided";
               files, deps
           | _ ->
               List.rev all_files, deps

       10.2 Fly Dependencies Mode

       F* supports "fly deps" mode for interactive development:

       // FStarC.Main.fst:401-448
       let filenames, dep_graph, fly_deps =
         if FStarC.Parser.Dep.fly_deps_enabled()
         then (
           // Check if valid .checked file exists first
           match CheckedFiles.scan_deps_and_check_cache_validity fn with
           | Some (files, deps) ->
             files, deps, false  // Use cached deps
           | None ->
             // Compute deps on-the-fly
             let deps = FStarC.Parser.Dep.empty_deps [fn] in
             filenames, deps, true
         )
         else (
           // Full dependency analysis
           let files, deps =
             Dependencies.find_deps_if_needed filenames
               CheckedFiles.load_parsing_data_from_cache
           in
           files, deps, false
         )

       ---
       11. THE 3-STAGE BOOTSTRAP PROCESS

       F* is self-hosting: the compiler is written in F*, verified, and extracted to OCaml. This requires a bootstrap process.

       11.1 Bootstrap Stages

       From /home/grigory/Downloads/FStar/Makefile:

       # Stage 0: Pre-built compiler (committed to repo)
       FSTAR0_EXE ?= stage0/out/bin/fstar.exe

       # Stage 1: Compiler built by stage 0
       FSTAR1_BARE_EXE := stage1/dune/_build/default/fstarc-bare/fstarc1_bare.exe
       FSTAR1_FULL_EXE := stage1/dune/_build/default/fstarc-full/fstarc1_full.exe

       # Stage 2: Compiler built by stage 1  
       FSTAR2_BARE_EXE := stage2/dune/_build/default/fstarc-bare/fstarc2_bare.exe
       FSTAR2_FULL_EXE := stage2/dune/_build/default/fstarc-full/fstarc2_full.exe

       11.2 Bootstrap Flow

       Stage 0 (pre-built, committed)
           |
           | extracts src/ to OCaml
           v
       Stage 1 Bare (minimal compiler)
           |
           | extracts ulib/ plugins
           v
       Stage 1 Full (compiler + plugins)
           |
           | extracts src/ to OCaml (self-extraction)
           v
       Stage 2 Bare (minimal compiler)
           |
           | extracts ulib/ plugins
           v
       Stage 2 Full (compiler + plugins)
           |
           | extracts src/ to OCaml
           v
       Stage 3 (verification only - must match Stage 2)

       11.3 Build Commands

       # Build stage 1 bare compiler
       .bare1.src.touch: $(FSTAR0_EXE) .force
           env \
             SRC=src/ \
             FSTAR_EXE=$(FSTAR0_EXE) \
             CACHE_DIR=stage1/fstarc.checked/ \
             OUTPUT_DIR=stage1/fstarc.ml/ \
             CODEGEN=OCaml \
             TAG=fstarc \
             TOUCH=$@ \
             $(MAKE) -f mk/fstar-01.mk ocaml

       # Build stage 2 using stage 1
       .bare2.src.touch: $(FSTAR1_FULL_EXE) .force
           env \
             SRC=src/ \
             FSTAR_LIB=$(abspath ulib) \
             FSTAR_EXE=$(FSTAR1_FULL_EXE) \
             CACHE_DIR=stage2/fstarc.checked/ \
             OUTPUT_DIR=stage2/fstarc.ml/ \
             CODEGEN=OCaml \
             TAG=fstarc \
             TOUCH=$@ \
             $(MAKE) -f mk/fstar-12.mk ocaml

       11.4 Stage 3 Verification

       # Stage 3 extracts but doesn't build - verifies stage 2 = stage 3
       stage3-bare: $(FSTAR2_FULL_EXE) .force
           env \
             SRC=src/ \
             FSTAR_EXE=$(FSTAR2_FULL_EXE) \
             FSTAR_LIB=$(abspath ulib) \
             CACHE_DIR=stage3/fstarc.checked/ \
             OUTPUT_DIR=stage3/fstarc.ml/ \
             CODEGEN=OCaml \
             TAG=fstarc \
             $(MAKE) -f mk/fstar-12.mk ocaml

       stage3-diff: stage3-bare .force
           diff -r -x '*.ramon' stage2/fstarc.ml stage3/fstarc.ml

       The stage 3 diff verifies that:
       - Stage 2 compiler (built by stage 1) extracts to identical OCaml
       - This proves the bootstrap is stable (fixpoint reached)

       11.5 Bumping Stage 0

       bump-stage0: stage0_new
           $(call bold_msg, "BUMP!")
           rm -rf stage0
           mv stage0_new stage0
           echo 'out' >> stage0/.gitignore
           ...

       When F* developers make changes, they must:
       1. Build stage 2
       2. Verify stage 2 = stage 3 (bootstrap stability)
       3. Run make bump-stage0 to update the committed stage 0

       ---
       12. OPTIONS AND CONFIGURATION

       12.1 Option Types

       // FStarC.Options.fsti:46-78
       type option_val =
         | Bool of bool
         | String of string
         | Path of string
         | Int of int
         | List of list option_val
         | Unset

       type opt_type =
       | Const of option_val
       | IntStr of string
       | BoolStr
       | PathStr of string
       | SimpleStr of string
       | EnumStr of list string
       | OpenEnumStr of list string & string
       | PostProcessed of ((option_val -> option_val) & opt_type)
       | Accumulated of opt_type
       | ReverseAccumulated of opt_type
       | WithSideEffect of ((unit -> unit) & opt_type)

       12.2 Option Stack

       Options support push/pop for scoped changes:

       // FStarC.Options.fsti:90-96
       val push                        : unit -> unit
       val pop                         : unit -> unit
       val internal_push               : unit -> unit
       val internal_pop                : unit -> bool
       val depth                       : unit -> int
       val snapshot                    : unit -> (int & unit)
       val rollback                    : option int -> unit

       This enables:
       - Interactive mode checkpoints
       - #push-options / #pop-options pragmas
       - Scoped option changes

       ---
       13. ERROR HANDLING AND REPORTING

       13.1 Error Structure

       Errors carry structured information for display:

       // FStarC.Main.fst:488-498
       let handle_error (e:exn) : unit =
           if FStarC.Errors.handleable e then
             FStarC.Errors.err_exn e
           else begin
             print1_error "Unexpected error: %s\n" (Util.message_of_exn e);
             if Options.trace_error() then
               print1_error "Trace:\n%s\n" (Util.trace_of_exn e)
             else
               print_error "Please file a bug report..."
           end;
           report_errors []

       13.2 Error Propagation

       // FStarC.Main.fst:71-79
       let report_errors fmods =
         FStarC.Errors.report_all () |> ignore;
         let nerrs = FStarC.Errors.get_err_count() in
         if nerrs > 0 then begin
           finished_message fmods nerrs;
           print_stats ();
           cleanup ();
           exit 1
         end

       Errors are collected throughout compilation and reported at the end, allowing multiple errors to be shown per run.

       ---
       14. KEY DATA STRUCTURES SUMMARY

       | Structure        | File                           | Purpose                      |
       |------------------|--------------------------------|------------------------------|
       | Parser.AST.modul | FStarC.Parser.AST.fsti         | Parsed, pre-desugared module |
       | Syntax.modul     | FStarC.Syntax.Syntax.fsti      | Desugared module             |
       | DsEnv.env        | FStarC.Syntax.DsEnv.fsti       | Desugaring environment       |
       | TcEnv.env        | FStarC.TypeChecker.Env.fsti    | Type checking environment    |
       | uenv             | FStarC.Extraction.ML.UEnv.fsti | Extraction environment       |
       | tc_result        | FStarC.CheckedFiles.fsti       | Cached type checking result  |
       | deps             | FStarC.Parser.Dep.fsti         | Dependency graph             |

       ---
       15. COMPILATION FLOW SUMMARY

       1. Entry (FStarC.Main.main)
         - Parse command line
         - Dispatch to appropriate mode
       2. Dependency Analysis (FStarC.Parser.Dep.collect)
         - Scan files for open, include directives
         - Build dependency graph
         - Topologically sort files
       3. Per-File Processing (FStarC.Universal.tc_one_file_internal)
         - Check cache validity
         - Parse file (FStarC.Parser.Driver.parse_file)
         - Interleave with interface (FStarC.ToSyntax.Interleave)
         - Desugar (FStarC.ToSyntax.ToSyntax.ast_modul_to_modul)
         - Type check (FStarC.TypeChecker.Tc.check_module)
         - SMT encode (FStarC.SMTEncoding.Encode.encode_modul)
         - Extract if requested (FStarC.Extraction.ML.Modul.extract)
         - Store to cache
       4. Output
         - Emit extracted code
         - Report errors
         - Clean up (terminate Z3 processes)

       ---
       16. USER INTERACTION POINTS

       | Phase            | User Sees                   | Controlled By               |
       |------------------|-----------------------------|-----------------------------|
       | Parsing          | Syntax errors               | Source file                 |
       | Desugaring       | Name resolution errors      | open, include directives    |
       | Type Checking    | Type errors, proof failures | Source code, specifications |
       | SMT Verification | Verification conditions     | --z3rlimit, --fuel, etc.    |
       | Extraction       | Extraction warnings         | --codegen, --extract flags  |

       Users can influence compilation through:
       - Command-line options (--lax, --admit_smt_queries, etc.)
       - In-file pragmas (#push-options, #reset-options)
       - Attributes on definitions ([@@ normalize_term], etc.)
       - Tactic invocations (by (exact t), assert P by tac)

       ---
       This documentation covers the F* compiler architecture as found in the codebase at /home/grigory/Downloads/FStar/src/. The key insight is that F* is a sophisticated self-hosting compiler with a careful multi-stage bootstrap process, modular architecture separating
       parsing, desugaring, type checking, SMT encoding, and extraction, and sophisticated caching for incremental compilation.
  ⎿  Done (31 tool uses · 146.9k tokens · 4m 1s)

● elite-bug-hunter(F* Ch2: Parser & AST)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering PARSER AND ABSTRACT SYNTAX TREE.

       Explore /home/grigory/Downloads/FStar/src/parser/ extensively.

       Focus on:
       1. Read FStarC.Parser.AST.fst completely - document every AST node type
       2. Read FStarC.Parser.Dep.fst - understand dependency analysis
       3. Read FStarC.Parser.ToDocument.fst - understand pretty printing
       4. Examine FStarC_Parser_Parse.mly (OCaml grammar file) - document grammar structure
       5. Examine FStarC_Parser_LexFStar.ml - understand lexer tokens
       6. Document parse.conflicts - explain conflict resolution strategies

       Your chapter should include:
       - Complete AST node hierarchy with examples
       - Token types and their meanings
       - Grammar rules for key constructs (let, match, function, effect)
       - Source location tracking (range, pos types)
       - Error recovery strategies
       - How comments and attributes are preserved
       - Extension points for language features

       Read at least 8 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have gathered comprehensive information from the F* parser codebase. Let me write the detailed documentation chapter.

       ---
       F* PARSER AND ABSTRACT SYNTAX TREE: COMPREHENSIVE DOCUMENTATION

       Chapter Overview

       This chapter provides exhaustive documentation of the F* parser infrastructure, covering the complete Abstract Syntax Tree (AST) design, lexical analysis, grammar specification, dependency tracking, and pretty-printing facilities. The F* parser transforms source text into
       an intermediate representation that serves as input to the desugaring phase before type-checking.

       ---
       1. LEXICAL ANALYSIS: THE TOKENIZER

       1.1 Lexer Implementation

       The F* lexer is implemented using sedlex (a Unicode-aware lexer generator for OCaml) in /home/grigory/Downloads/FStar/src/ml/FStarC_Parser_LexFStar.ml. The lexer handles:

       - Unicode character categories (lowercase, uppercase, math symbols)
       - Keyword recognition via hashtable lookup
       - Operator tokenization with precedence handling
       - String and character literal parsing
       - Comment collection and preservation

       1.2 Token Categories

       From FStarC_Parser_LexFStar.ml:72-145, the token types are defined in several categories:

       Literal Tokens:
       STRING     - String literals ("hello")
       IDENT      - Lowercase identifiers (foo, bar_baz)
       NAME       - Uppercase identifiers (Foo, Bar_Baz)
       INT        - Integer literals (42)
       INT8/UINT8 - 8-bit integers (42y, 42uy)
       INT16/UINT16 - 16-bit integers (42s, 42us)
       INT32/UINT32 - 32-bit integers (42l, 42ul)
       INT64/UINT64 - 64-bit integers (42L, 42UL)
       SIZET      - Size type integers (42sz)
       REAL       - Real number literals (3.14R)
       CHAR       - Character literals ('a')

       Keyword Tokens (from lines 46-115):
       Hashtbl.add keywords "let"           LET         ;
       Hashtbl.add keywords "match"         MATCH       ;
       Hashtbl.add keywords "if"            IF          ;
       Hashtbl.add keywords "then"          THEN        ;
       Hashtbl.add keywords "else"          ELSE        ;
       Hashtbl.add keywords "fun"           FUN         ;
       Hashtbl.add keywords "function"      FUNCTION    ;
       Hashtbl.add keywords "forall"        FORALL      ;
       Hashtbl.add keywords "exists"        EXISTS      ;
       Hashtbl.add keywords "val"           VAL         ;
       Hashtbl.add keywords "type"          TYPE        ;
       Hashtbl.add keywords "effect"        EFFECT      ;
       Hashtbl.add keywords "module"        MODULE      ;
       Hashtbl.add keywords "open"          OPEN        ;
       Hashtbl.add keywords "include"       INCLUDE     ;
       Hashtbl.add keywords "friend"        FRIEND      ;
       (* ... and approximately 60 more keywords *)

       Unicode Support (lines 116-136):
       Hashtbl.add keywords "λ"             FUN         ;  (* Lambda *)
       Hashtbl.add keywords "α"             (IDENT "'a")  ;
       Hashtbl.add keywords "β"             (IDENT "'b")  ;
       Hashtbl.add keywords "∀"             FORALL;
       Hashtbl.add keywords "∃"             EXISTS;
       Hashtbl.add keywords "⊤"             NAME "True";
       Hashtbl.add keywords "⊥"             NAME "False";
       Hashtbl.add keywords "⟹"            IMPLIES;
       Hashtbl.add keywords "→"             RARROW;
       Hashtbl.add keywords "∧"             CONJUNCTION;
       Hashtbl.add keywords "∨"             DISJUNCTION;

       1.3 Operator Tokenization

       The lexer defines operator character classes for precedence parsing (lines 354-402):

       let op_char = [%sedlex.regexp? Chars "!$%&*+-.<>=?^|~:@#\\/"]

       let op_prefix  = [%sedlex.regexp? Chars "!~?"]
       let op_infix0a = [%sedlex.regexp? Chars "|"]    (* left associative *)
       let op_infix0b = [%sedlex.regexp? Chars "&"]    (* left associative *)
       let op_infix0c = [%sedlex.regexp? Chars "=<>"]  (* left associative *)
       let op_infix0d = [%sedlex.regexp? Chars "$"]    (* left associative *)
       let op_infix1  = [%sedlex.regexp? Chars "@^"]   (* right associative *)
       let op_infix2  = [%sedlex.regexp? Chars "+-"]   (* left associative *)
       let op_infix3  = [%sedlex.regexp? Chars "*/%"]  (* left associative *)

       1.4 Let Operators and Custom Control Flow

       F* supports custom let-operators, match-operators, and if-operators (lines 480-499):

       | "match", Plus op_char ->
          ensure_no_comment lexbuf (fun s ->
              match BatString.lchop ~n:5 s with
              | "" -> MATCH
              | s  -> MATCH_OP s)

       | "if", Plus op_char ->
          ensure_no_comment lexbuf (fun s ->
              match BatString.lchop ~n:2 s with
              | "" -> IF
              | s  -> IF_OP s)

       | "let", Plus op_char ->
          ensure_no_comment lexbuf (fun s ->
              match BatString.lchop ~n:3 s with
              | "" -> LET
              | s  -> LET_OP s)

       This enables syntax like let? x = ... or match* expr with ... for monadic or effect-handling constructs.

       ---
       2. ABSTRACT SYNTAX TREE DESIGN

       2.1 Core AST Principles

       The F* AST is defined in /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.AST.fst and its interface file. Key design principles from the header comment (lines 27-30):

       (* AST produced by the parser, before desugaring
          It is not stratified: a single type called "term" containing
          expressions, formulas, types, and so on *)

       This "unstratified" design means terms, types, kinds, and formulas share the same AST type, distinguished only by a level annotation.

       2.2 Term Levels

       From FStarC.Parser.AST.fsti:31:

       type level = | Un | Expr | Type_level | Kind | Formula

       - Un - Unspecified/unknown level
       - Expr - Expression level (runtime values)
       - Type_level - Type level
       - Kind - Kind level (types of types)
       - Formula - Logical formula level

       2.3 Complete Term Node Hierarchy

       The term' type encompasses all expression forms (FStarC.Parser.AST.fsti:46-109):

       Atomic Terms:
       | Wild                              (* Underscore wildcard _ *)
       | Const     of sconst              (* Literals: 42, "hello", true *)
       | Uvar      of ident               (* Universe variable *)
       | Var       of lid                 (* Qualified lowercase id: Foo.bar *)
       | Name      of lid                 (* Qualified uppercase id: Foo.Bar *)

       Operator Application:
       | Op        of ident & list term   (* Operator with arguments *)
       | Projector of lid & ident         (* Record projector: Rec?.field *)
       | Discrim   of lid                 (* Discriminator: Some? *)

       Data Construction:
       | Construct of lid & list (term & imp)  (* Data constructor application *)
       | Record    of option term & list (lid & term)  (* Record literal *)
       | Project   of term & lid               (* Field projection *)

       Function-Related:
       | Abs       of list pattern & term              (* fun p1 ... pn -> body *)
       | Function  of list branch & range              (* function | p1 -> e1 | ... *)
       | App       of term & term & imp                (* Function application *)

       Let Bindings:
       | Let       of local_let_qualifier & list (option attributes_ & (pattern & term)) & term
       | LetOperator   of list (ident & pattern & term) & term  (* let? x = e1 in e2 *)
       | LetOpen   of lid & term                        (* let open M in e *)
       | LetOpenRecord of term & term & term            (* let open r <: T in e *)

       Control Flow:
       | If    of term & option ident & option match_returns_annotation & term & term
       | Match of term & option ident & option match_returns_annotation & list branch
       | TryWith of term & list branch
       | Seq   of term & term              (* Sequencing: e1; e2 *)
       | Bind  of ident & term & term      (* Deprecated bind notation *)

       Type System:
       | Product   of list binder & term   (* Dependent function type: x:t -> t' *)
       | Sum       of list (either binder term) & term  (* Dependent tuple type *)
       | Refine    of binder & term        (* Refinement type: x:t{phi} *)
       | Ascribed  of term & term & option term & bool  (* Type ascription *)
       | NamedTyp  of ident & term         (* Named type annotation: (x:t) *)

       Quantifiers:
       | QForall   of list binder & patterns & term
       | QExists   of list binder & patterns & term
       | QuantOp   of ident & list binder & patterns & term  (* Custom quantifier *)

       Specification Constructs:
       | Requires  of term
       | Ensures   of term
       | Decreases of term
       | LexList   of list term            (* Lexicographic ordering for termination *)
       | WFOrder   of term & term          (* Well-founded relation *)

       Meta-programming:
       | Quote     of term & quote_kind    (* Quoted term for tactics *)
       | Antiquote of term                 (* Unquoting in quoted context *)
       | VQuote    of term                 (* Variable quotation `%foo *)

       Proof Constructs (Classical Sugar):
       | CalcProof of term & term & list calc_step
       | IntroForall of list binder & term & term
       | IntroExists of list binder & term & list term & term
       | IntroImplies of term & term & binder & term
       | IntroOr   of bool & term & term & term
       | IntroAnd  of term & term & term & term
       | ElimForall  of list binder & term & list term
       | ElimExists  of list binder & term & term & binder & term
       | ElimImplies of term & term & term
       | ElimOr    of term & term & term & binder & term & binder & term
       | ElimAnd   of term & term & term & binder & binder & term

       Miscellaneous:
       | Paren     of term                 (* Parenthesized expression *)
       | Labeled   of term & string & bool (* Labeled for error messages *)
       | Attributes of list term           (* Attribute list *)
       | ListLiteral of list term          (* [e1; e2; ...] *)
       | SeqLiteral of list term           (* seq![e1; e2; ...] *)
       | LitDoc of Pprint.document         (* For resugaring extensions *)

       2.4 Term Wrapper with Metadata

       Each term carries source location and level information (FStarC.Parser.AST.fsti:111):

       and term = {tm: term'; range: range; level: level}

       The hasRange type class instances enable position extraction:

       instance hasRange_term : hasRange term = {
         pos = (fun t -> t.range);
         setPos = (fun r t -> { t with range = r });
       }

       2.5 Pattern Hierarchy

       Patterns for match expressions and let bindings (FStarC.Parser.AST.fsti:130-144):

       and pattern' =
         | PatWild     of aqual & attributes_        (* Wildcard: _ *)
         | PatConst    of sconst                     (* Literal pattern *)
         | PatApp      of pattern & list pattern     (* Constructor application *)
         | PatVar      of ident & aqual & attributes_(* Variable binding *)
         | PatName     of lid                        (* Constructor name *)
         | PatList     of list pattern               (* [p1; p2; ...] *)
         | PatRest                                   (* .. for rest patterns *)
         | PatTuple    of list pattern & bool        (* Tuple (dependent flag) *)
         | PatRecord   of list (lid & pattern)       (* Record pattern *)
         | PatAscribed of pattern & (term & option term)  (* Type-ascribed *)
         | PatOr       of list pattern               (* Disjunctive pattern *)
         | PatOp       of ident                      (* Operator pattern *)
         | PatVQuote   of term                       (* Quoted variable *)

       and pattern = {pat: pattern'; prange: range}

       2.6 Binder Hierarchy

       Binders for function parameters and quantifiers (FStarC.Parser.AST.fsti:123-128):

       and binder' =
         | Variable  of ident              (* Unannotated: x *)
         | Annotated of ident & term       (* Annotated: x:t *)
         | NoName    of term               (* Anonymous: t *)

       and binder = {
         b: binder';
         brange: range;
         blevel: level;
         aqual: aqual;                     (* Argument qualifier *)
         battributes: attributes_
       }

       2.7 Argument Qualifiers and Implicits

       The aqual (argument qualifier) and imp (implicit) types control argument passing:

       and arg_qualifier =
         | Implicit       (* #arg - implicit argument *)
         | Equality       (* $arg - equality implicit *)
         | Meta of term   (* #[tactic] - meta argument *)
         | TypeClassArg   (* {| constraint |} - typeclass *)

       and aqual = option arg_qualifier

       and imp =
         | Hash           (* #e - implicit application *)
         | UnivApp        (* u#u - universe application *)
         | HashBrace of term  (* #[t] - meta application *)
         | Infix          (* Infix operator usage *)
         | Nothing        (* Explicit application *)

       2.8 Declaration Hierarchy

       Top-level declarations (FStarC.Parser.AST.fsti:253-286):

       type decl' =
         | TopLevelModule of lid
         | Open of lid & restriction
         | Friend of lid
         | Include of lid & restriction
         | ModuleAbbrev of ident & lid           (* module M = N.O.P *)
         | TopLevelLet of let_qualifier & list (pattern & term)
         | Tycon of bool & bool & list tycon     (* type definitions *)
         | Val of ident & term                   (* val declarations *)
         | Exception of ident & option term
         | NewEffect of effect_decl
         | LayeredEffect of effect_decl
         | SubEffect of lift
         | Polymonadic_bind of lid & lid & lid & term
         | Polymonadic_subcomp of lid & lid & term
         | Pragma of pragma
         | Assume of ident & term
         | Splice of bool & list ident & term    (* Meta-programming splice *)
         | DeclSyntaxExtension of string & string & range & range
         | UseLangDecls of string
         | DeclToBeDesugared of to_be_desugared
         | Unparseable

       and decl = {
         d: decl';
         drange: range;
         quals: qualifiers;
         attrs: attributes_;
         interleaved: bool;
       }

       2.9 Type Constructors (Tycon)

       Type definitions come in four forms (FStarC.Parser.AST.fsti:182-186):

       type tycon =
         | TyconAbstract of ident & list binder & option knd
         | TyconAbbrev   of ident & list binder & option knd & term
         | TyconRecord   of ident & list binder & option knd & attributes_ & tycon_record
         | TyconVariant  of ident & list binder & option knd &
                            list (ident & option constructor_payload & attributes_)

       Constructor payloads for variants:

       type constructor_payload =
         | VpOfNotation of typ     (* C of t *)
         | VpArbitrary of typ      (* C : t *)
         | VpRecord of (tycon_record & option typ)  (* C {fields} *)

       2.10 Qualifiers

       Declaration qualifiers (FStarC.Parser.AST.fsti:188-206):

       type qualifier =
         | Private
         | Noeq
         | Unopteq
         | Assumption
         | TotalEffect
         | Effect_qual
         | New
         | Inline                           (* Always unfold *)
         | Visible                          (* May unfold if needed *)
         | Unfold_for_unification_and_vcgen (* Unfold for SMT *)
         | Inline_for_extraction            (* Unfold only for extraction *)
         | Irreducible                      (* Never unfold *)
         | NoExtract
         | Reifiable
         | Reflectable
         | Opaque
         | Logic                            (* Deprecated *)

       ---
       3. GRAMMAR SPECIFICATION

       3.1 Grammar File Structure

       The Menhir grammar is in /home/grigory/Downloads/FStar/src/ml/FStarC_Parser_Parse.mly. From the header comment (lines 1-18):

       (*
        Menhir reports the following warnings:

          Warning: 5 states have shift/reduce conflicts.
          Warning: 6 shift/reduce conflicts were arbitrarily resolved.
          Warning: 221 end-of-stream conflicts were arbitrarily resolved.

        If you're editing this file, be sure to not increase the warnings,
        except if you have a really good reason.

        The shift-reduce conflicts are natural in an ML-style language. E.g.,
        there are S-R conflicts with dangling elses, with a non-delimited match 
        where the BAR is dangling etc.
       *)

       3.2 Precedence and Associativity

       The grammar declares operator precedence (lines 149-173):

       %nonassoc THEN
       %nonassoc ELSE

       %nonassoc ASSERT
       %nonassoc EQUALTYPE
       %nonassoc SUBTYPE
       %nonassoc BY

       %right COLON_COLON
       %right AMP

       %nonassoc COLON_EQUALS
       %left     OPINFIX0a          (* | operators *)
       %left     OPINFIX0b          (* & operators *)
       %left     OPINFIX0c EQUALS   (* = < > operators *)
       %left     OPINFIX0d          (* $ operators *)
       %left     PIPE_RIGHT         (* |> *)
       %right    PIPE_LEFT          (* <| *)
       %right    OPINFIX1           (* @ ^ operators *)
       %left     OPINFIX2 MINUS QUOTE  (* + - operators *)
       %left     OPINFIX3L          (* * / % operators - left assoc *)
       %right    OPINFIX3R          (* ** operator - right assoc *)
       %left     BACKTICK           (* Infix application *)
       %right    OPINFIX4           (* |-> and unicode ops *)

       3.3 Start Symbols

       The grammar provides three entry points (lines 174-179):

       %start inputFragment    (* Full file or interactive fragment *)
       %start term             (* Single term *)
       %start oneDeclOrEOF     (* Single declaration *)

       %type <FStarC_Parser_AST.inputFragment> inputFragment
       %type <(FStarC_Parser_AST.decl list * FStarC_Sedlexing.snap option) option> oneDeclOrEOF
       %type <FStarC_Parser_AST.term> term

       3.4 Declaration Productions

       Top-level declarations (lines 280-445):

       decl:
         | ASSUME lid=uident COLON phi=formula
             { [mk_decl (Assume(lid, phi)) (rr $loc) [ Qualifier Assumption ]] }

         | ds=list(decoration) decl=rawDecl
             { [mk_decl decl (rr $loc(decl)) ds] }

       Raw declaration forms (lines 379-445):

       rawDecl:
         | p=pragma
             { Pragma p }
         | OPEN uid=quident r=restriction
             { Open (uid, r) }
         | MODULE uid1=uident EQUALS uid2=quident
             { ModuleAbbrev(uid1, uid2) }
         | MODULE uid=quident
             { TopLevelModule uid }
         | TYPE tcdefs=separated_nonempty_list(AND,typeDecl)
             { Tycon (false, false, tcdefs) }
         | EFFECT uid=uident tparams=typars EQUALS t=typ
             { Tycon(true, false, [(TyconAbbrev(uid, tparams, None, t))]) }
         | LET q=letqualifier lbs=separated_nonempty_list(AND, letbinding)
             { TopLevelLet(q, focusLetBindings lbs r) }
         | VAL lid=lidentOrOperator bs=binders COLON t=typ
             { Val(lid, t) }

       3.5 Type Declarations

       Type definition grammar (lines 448-469):

       typeDecl:
         | lid=ident tparams=typars ascr_opt=ascribeKind? tcdef=typeDefinition
             { tcdef lid tparams ascr_opt }

       typeDefinition:
         |   { TyconAbstract }
         | EQUALS t=typ
             { TyconAbbrev }
         | EQUALS attrs_opt=ioption(binderAttributes) record_field_decls=recordDefinition
             { TyconRecord }
         | EQUALS ct_decls=list(constructorDecl)
             { TyconVariant }

       constructorDecl:
         | BAR attrs_opt=ioption(binderAttributes) uid=uident payload=option(constructorPayload)
           { uid, payload, none_to_empty_list attrs_opt }

       constructorPayload:
         | COLON t=typ                     { VpArbitrary t }
         | OF t=typ                        { VpOfNotation t }
         | fields=recordDefinition opt=option(COLON t=typ {t}) { VpRecord(fields, opt) }

       3.6 Let Binding Grammar

       Let binding productions (lines 510-523):

       letbinding:
         | focus_opt=maybeFocus lid=lidentOrOperator lbp=nonempty_list(patternOrMultibinder)
           ascr_opt=ascribeTyp? EQUALS tm=term
             {
               let pat = mk_pattern (PatVar(lid, None, [])) (rr $loc(lid)) in
               let pat = mk_pattern (PatApp (pat, flatten lbp)) (rr2 $loc(focus_opt) $loc(lbp)) in
               match ascr_opt with
               | None -> (focus_opt, (pat, tm))
               | Some t -> (focus_opt, (mk_pattern (PatAscribed(pat, t)) pos, tm))
             }
         | focus_opt=maybeFocus pat=tuplePattern ascr=ascribeTyp eq=EQUALS tm=term
             { focus_opt, (mk_pattern (PatAscribed(pat, ascr)) pos, tm) }
         | focus_opt=maybeFocus pat=tuplePattern EQUALS tm=term
             { focus_opt, (pat, tm) }

       3.7 Effect Declarations

       Effect definition grammar (lines 529-569):

       newEffect:
         | ed=effectRedefinition
         | ed=effectDefinition
           { ed }

       effectRedefinition:
         | lid=uident EQUALS t=simpleTerm
           { RedefineEffect(lid, [], t) }

       effectDefinition:
         | LBRACE lid=uident bs=binders COLON typ=tmArrow(tmNoEq)
                  WITH eds=separated_nonempty_list(SEMICOLON, effectDecl)
           RBRACE
           { DefineEffect(lid, bs, typ, eds) }

       layeredEffectDefinition:
         | LBRACE lid=uident bs=binders WITH r=tmNoEq RBRACE
           { (* Constructs Product type and parses record of combinators *) }

       3.8 Pattern Grammar

       Pattern productions (lines 672-748):

       disjunctivePattern:
         | pats=separated_nonempty_list(BAR, tuplePattern) { pats }

       tuplePattern:
         | pats=separated_nonempty_list(COMMA, constructorPattern)
             { match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) }

       constructorPattern:
         | pat=constructorPattern COLON_COLON pats=constructorPattern
             { mk_pattern (consPat pat pats) }
         | uid=quident args=nonempty_list(atomicPattern)
             { mk_pattern (PatApp (head_pat, args)) }
         | pat=atomicPattern
             { pat }

       atomicPattern:
         | DOT_DOT                         { PatRest }
         | LPAREN pat=tuplePattern COLON t=simpleArrow phi_opt=refineOpt RPAREN
             { mkRefinedPattern pat t phi_opt }
         | LBRACK pats=list(SEMICOLON, tuplePattern) RBRACK
             { PatList pats }
         | LBRACE record_pat=list(SEMICOLON, fieldPattern) RBRACE
             { PatRecord record_pat }
         | UNDERSCORE                      { PatWild (None, []) }
         | c=constant                      { PatConst c }
         | qual_id=aqualifiedWithAttrs(lident)
             { PatVar (lid, aqual, attrs) }
         | uid=quident                     { PatName uid }

       3.9 Term Grammar

       Term production hierarchy (lines 916-1000):

       term:
         | e=noSeqTerm
             { e }
         | e1=noSeqTerm SEMICOLON e2=term
             { mk_term (Seq(e1, e2)) }
         | e1=noSeqTerm op=SEMICOLON_OP e2=term
             { (* LetOperator or Bind *) }
         | x=lidentOrUnderscore LONG_LEFT_ARROW e1=noSeqTerm SEMICOLON e2=term
             { mk_term (Bind(x, e1, e2)) }

       noSeqTerm:
         | t=typ  { t }
         | e=tmIff SUBTYPE t=tmIff
             { mk_term (Ascribed(e, t, None, false)) }
         | e=tmIff SUBTYPE t=tmIff BY tactic=thunk(typ)
             { mk_term (Ascribed(e, t, Some tactic, false)) }
         | REQUIRES t=typ
             { mk_term (Requires t) }
         | ENSURES t=typ
             { mk_term (Ensures t) }
         | DECREASES t=typ
             { mk_term (Decreases t) }
         | op=ifMaybeOp e1=noSeqTerm ret_opt=option(match_returning)
           THEN e2=noSeqTerm ELSE e3=noSeqTerm
             { mk_term (If(e1, op, ret_opt, e2, e3)) }

       ---
       4. CONFLICT RESOLUTION

       4.1 Known Conflicts

       From /home/grigory/Downloads/FStar/src/parser/parse.conflicts, the grammar has documented shift/reduce conflicts:

       State 792 - Type Constructor Attributes (lines 1-42):
       Token involved: LBRACK_AT_AT
       Reached after: TYPE ident typars option(ascribeKind) EQUALS

       Conflict: When seeing LBRACK_AT_AT after "type T =", should we:
       - Shift: Parse as binder attributes in an arrow type
       - Reduce: Complete empty constructor list and start new decorated decl

       Resolution: Shift (attribute belongs to next element, not new declaration)

       State 743 - Nested Pattern Branches (lines 84-116):
       Token involved: BAR
       Reached after: FUNCTION pattern maybeFocusArrow TRY term WITH branches

       Conflict: Does BAR continue inner TRY-WITH or outer FUNCTION?

       Resolution: Shift (BAR belongs to innermost match/try construct)

       State 657 - Nested FUNCTION (lines 189-221):
       Token involved: BAR
       Reached after: FUNCTION pattern maybeFocusArrow FUNCTION branches

       Conflict: Does BAR extend inner or outer FUNCTION?

       Resolution: Shift (extend innermost FUNCTION)

       State 486 - Sequencing (lines 222-253):
       Tokens involved: SEMICOLON_SEMICOLON, SEMICOLON
       Reached after: FUNCTION pattern maybeFocusArrow noSeqTerm

       Conflict: Does SEMICOLON continue branch body or outer term?

       Resolution: Shift (sequence extends branch body)

       4.2 Conflict Resolution Strategy

       The grammar relies on Menhir's default conflict resolution:
       1. Prefer shift over reduce (greedy parsing)
       2. For reduce-reduce conflicts, prefer earlier production

       This matches ML-style language conventions where:
       - Else binds to nearest if
       - Bars bind to innermost match/try/function
       - Sequences extend current expression

       ---
       5. SOURCE LOCATION TRACKING

       5.1 Range Type

       Source locations use the FStarC.Range module with a position type:

       type pos = {
         filename: string;
         line: int;
         col: int;
       }

       type range = pos * pos  (* start, end positions *)

       5.2 Range Utilities in Parser

       The parser uses helper functions for range construction (FStarC_Parser_Parse.mly:34-35):

       let rr = FStarC_Parser_Util.translate_range
       let rr2 = FStarC_Parser_Util.translate_range2

       These convert Menhir's $loc syntax to F* ranges.

       5.3 hasRange Type Class

       AST nodes implement the hasRange class for uniform position access:

       instance hasRange_term    : hasRange term
       instance hasRange_pattern : hasRange pattern
       instance hasRange_binder  : hasRange binder
       instance hasRange_decl    : hasRange decl

       ---
       6. DEPENDENCY ANALYSIS

       6.1 Dependency Module Overview

       The dependency analysis is in /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.Dep.fst. From the module header (lines 17-25):

       (** This module provides an ocamldep-like tool for F*, invoked with [fstar --dep].
           It also supports scanning individual AST declarations for dependences.
           It is used in many parts of the compiler, including
            * to output a .depend for use with Makefiles, using fstar --dep
            * to check for the dependences of a checked file, used to write out their hashes
            * to scan dependences of a declarations on the fly, for use with fly_deps
           etc.
       *)

       6.2 Parsing Data Elements

       The dependency scanner collects these data elements (FStarC.Parser.Dep.fsti:39-46):

       type parsing_data_elt =
         | P_begin_module of lident
         | P_open of bool & lident          (* bool = let open *)
         | P_implicit_open_module_or_namespace of (open_kind & lid)
         | P_dep of bool & lident           (* bool = friend dependency *)
         | P_alias of ident & lident        (* module alias *)
         | P_lid of lident                  (* referenced identifier *)
         | P_inline_for_extraction

       6.3 Dependency Types

       Four dependency relationship types (FStarC.Parser.Dep.fst:220-228):

       type dependence =
         | UseInterface of module_name      (* Must use .fsti *)
         | PreferInterface of module_name   (* Prefer .fsti if available *)
         | UseImplementation of module_name (* Must use .fst *)
         | FriendImplementation of module_name  (* Friend access to .fst *)

       6.4 AST Scanning

       The collect_term function traverses the AST to find dependencies (lines 861-993). Key patterns:

       and collect_term' = function
         | Var lid | Name lid | AST.Projector (lid, _) | AST.Discrim lid ->
             add_to_parsing_data (P_lid lid)
         | Construct (lid, termimps) ->
             add_to_parsing_data (P_lid lid);
             List.iter (fun (t, _) -> collect_term t) termimps
         | LetOpen (lid, t) ->
             add_to_parsing_data (P_open (true, lid));
             collect_term t
         (* ... patterns for all term forms *)

       6.5 Automatic Dependencies

       Certain constructs trigger automatic dependencies (lines 972-1072):

       | CalcProof (rel, init, steps) ->
           add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Calc")));

       | IntroForall (bs, p, e) ->
           add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));

       | SeqLiteral ts ->
           add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Seq.Base")));

       ---
       7. PRETTY PRINTING

       7.1 ToDocument Module

       The pretty printer is in /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.ToDocument.fst. It converts AST back to formatted source code.

       7.2 Comment Preservation

       Comments are tracked via a mutable stack (line 492):

       let comment_stack : ref (list (string & range)) = mk_ref []

       From lines 469-491, the comment placement rules are:
       1. At most one comment per line
       2. Line feeds between declarations are preserved
       3. Comments attach to AST nodes based on range comparison
       4. Leftover comments are printed at the end

       7.3 Operator Precedence for Printing

       The printer maintains its own precedence table for correct parenthesization (lines 315-348):

       let opinfix4  : associativity_level = Right, [Exact "|->"; UnicodeOperator]
       let opinfix3l : associativity_level = Left,  [StartsWith '*'; StartsWith '/'; StartsWith '%']
       let opinfix3r : associativity_level = Right, [Exact "**"]
       let opinfix2  : associativity_level = Left,  [StartsWith '+'; StartsWith '-']
       let opinfix1  : associativity_level = Right, [StartsWith '@'; StartsWith '^']
       let pipe_right : associativity_level = Left, [Exact "|>"]
       let opinfix0d : associativity_level = Left,  [StartsWith '$']
       let opinfix0c : associativity_level = Left,  [StartsWith '='; StartsWith '<'; StartsWith '>']
       let opinfix0b : associativity_level = Left,  [StartsWith '&']
       let opinfix0a : associativity_level = Left,  [StartsWith '|']

       7.4 Annotation Styles

       Type signatures can be formatted in multiple ways (lines 433-436):

       type annotation_style =
         | Binders of int & int & bool  (* val f (x1:t1) ... (xn:tn) : C *)
         | Arrows of int & int          (* val f : x1:t1 -> ... -> xn:tn -> C *)

       ---
       8. EXTENSION POINTS

       8.1 Syntax Extensions (Blobs)

       F* supports embedded domain-specific languages via "blobs" (FStarC_Parser_Parse.mly:51-56):

       let parse_extension_blob (extension_name:string)
                                (s:string)
                                (blob_range:range)
                                (extension_syntax_start:range) : FStarC_Parser_AST.decl' =
           DeclSyntaxExtension (extension_name, s, blob_range, extension_syntax_start)

       Usage in the grammar (lines 436-445):

       | blob=BLOB
           {
             let ext_name, contents, pos, snap = blob in
             let blob_range = rr (snd snap, snd $loc) in
             let extension_syntax_start_range = (rr (pos, pos)) in
             parse_extension_blob ext_name contents blob_range extension_syntax_start_range
           }

       8.2 Language Declarations

       The #lang- directive enables alternative syntaxes (lines 449-456 in lexer):

       | "#lang-", ident -> (
          let s = L.lexeme lexbuf in
          let lang_name = BatString.lchop ~n:6 s in
          let snap = Sedlexing.snapshot lexbuf in
          Buffer.clear use_lang_buffer;
          let pos = L.current_pos lexbuf in
          use_lang_blob snap lang_name pos use_lang_buffer lexbuf
        )

       8.3 To-Be-Desugared Declarations

       For custom syntaxes that need deferred processing (FStarC.Parser.AST.fsti:244-251):

       type to_be_desugared = {
         lang_name: string;
         blob: FStarC.Dyn.dyn;
         idents: list ident;
         to_string: FStarC.Dyn.dyn -> string;
         eq: FStarC.Dyn.dyn -> FStarC.Dyn.dyn -> bool;
         dep_scan: dep_scan_callbacks -> FStarC.Dyn.dyn -> unit
       }

       The dep_scan_callbacks interface allows extensions to participate in dependency analysis:

       type dep_scan_callbacks = {
          scan_term: term -> unit;
          scan_binder: binder -> unit;
          scan_pattern: pattern -> unit;
          add_lident: lident -> unit;
          add_open: lident -> unit;
       }

       ---
       9. ERROR RECOVERY

       9.1 Unparseable Declarations

       The AST includes an Unparseable variant for error recovery:

       type decl' =
         | ...
         | Unparseable

       This allows the parser to continue after encountering malformed declarations.

       9.2 Error Messages in Grammar

       The grammar provides contextual error messages (lines 392-393, 406-409):

       | MODULE q=qlident
           { raise_error_text (rr $loc(q)) Fatal_SyntaxError
               "Syntax error: expected a module name" }

       | VAL c=constant
           { raise_error_text (rr $loc) Fatal_SyntaxError
               "Syntax error: constants are not allowed in val declarations" }

       9.3 Range-Tagged Errors

       All parser errors include source location via the raise_error_text helper:

       raise_error_text : range -> error_code -> string -> 'a

       ---
       10. SMART CONSTRUCTORS

       10.1 AST Construction Helpers

       The AST module provides smart constructors for common patterns (FStarC.Parser.AST.fsti:313-348):

       val mk_decl : decl' -> range -> list decoration -> decl
       val mk_binder_with_attrs : binder' -> range -> level -> aqual -> list term -> binder
       val mk_binder : binder' -> range -> level -> aqual -> binder
       val mk_term : term' -> range -> level -> term
       val mk_pattern : pattern' -> range -> pattern

       val mk_uminus : term -> range -> range -> level -> term
       val un_curry_abs : list pattern -> term -> term'
       val mk_function : list branch -> range -> range -> term

       val consPat : range -> pattern -> pattern -> pattern'
       val consTerm : range -> term -> term -> term

       val unit_const : range -> term
       val ml_comp : term -> term
       val tot_comp : term -> term

       val mkApp : term -> list (term & imp) -> range -> term
       val mkTuple : list term -> range -> term
       val mkDTuple : list term -> range -> term
       val mkRefinedBinder : ident -> term -> bool -> option term -> range -> aqual -> list term -> binder

       10.2 Operator Compilation

       Operators are compiled to canonical names (FStarC.Parser.AST.fst:373-477):

       let compile_op arity s r =
           let name_of_char = function
             |'&' -> "Amp"    |'@' -> "At"      |'+' -> "Plus"
             |'-' when arity=1 -> "Minus"       |'-' -> "Subtraction"
             |'~' -> "Tilde"  |'/' -> "Slash"   |'\\' -> "Backslash"
             |'<' -> "Less"   |'=' -> "Equals"  |'>' -> "Greater"
             |'_' -> "Underscore"  |'|' -> "Bar"  |'!' -> "Bang"
             |'^' -> "Hat"    |'%' -> "Percent" |'*' -> "Star"
             |'?' -> "Question" |':' -> "Colon" |'$' -> "Dollar"
             |'.' -> "Dot"
             | c -> "u" ^ show (Util.int_of_char c)
           in
           match s with
           | ".[]<-" -> "op_String_Assignment"
           | ".()<-" -> "op_Array_Assignment"
           | ".[]" -> "op_String_Access"
           | ".()" -> "op_Array_Access"
           | _ -> "op_" ^ String.concat "_" (List.map name_of_char (String.list_of_string s))

       ---
       11. PRAGMAS

       11.1 Pragma Types

       Pragmas control compiler behavior (FStarC.Parser.AST.fsti:226-234):

       type pragma =
         | ShowOptions
         | SetOptions of string
         | ResetOptions of option string
         | PushOptions of option string
         | PopOptions
         | RestartSolver
         | PrintEffectsGraph
         | Check of term

       11.2 Pragma Grammar

       Pragma syntax (FStarC_Parser_Parse.mly:241-257):

       pragma:
         | PRAGMA_SHOW_OPTIONS         { ShowOptions }
         | PRAGMA_SET_OPTIONS s=string { SetOptions s }
         | PRAGMA_RESET_OPTIONS s_opt=string? { ResetOptions s_opt }
         | PRAGMA_PUSH_OPTIONS s_opt=string?  { PushOptions s_opt }
         | PRAGMA_POP_OPTIONS          { PopOptions }
         | PRAGMA_RESTART_SOLVER       { RestartSolver }
         | PRAGMA_PRINT_EFFECTS_GRAPH  { PrintEffectsGraph }
         | PRAGMA_CHECK t=term         { Check t }

       ---
       12. SUMMARY

       The F* parser infrastructure provides a comprehensive system for:

       1. Lexical Analysis - Unicode-aware tokenization with operator precedence
       2. AST Design - Unified term representation with level annotations
       3. Grammar - Menhir-based parser with controlled conflicts
       4. Dependencies - Full AST traversal for module dependency tracking
       5. Pretty Printing - Reversible formatting with comment preservation
       6. Extensions - Embedded DSL support via blobs and language declarations

       Key files for reference:
       - /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.AST.fst - AST definitions
       - /home/grigory/Downloads/FStar/src/ml/FStarC_Parser_Parse.mly - Grammar
       - /home/grigory/Downloads/FStar/src/ml/FStarC_Parser_LexFStar.ml - Lexer
       - /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.Dep.fst - Dependencies
       - /home/grigory/Downloads/FStar/src/parser/FStarC.Parser.ToDocument.fst - Pretty printing
       - /home/grigory/Downloads/FStar/src/parser/parse.conflicts - Conflict documentation

  ⎿  Done (14 tool uses · 157.7k tokens · 4m 14s)

● elite-bug-hunter(F* Ch3: Desugaring ToSyntax)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering DESUGARING (AST → Internal Syntax).

       Explore /home/grigory/Downloads/FStar/src/tosyntax/ extensively.

       Focus on:
       1. Read FStarC.ToSyntax.ToSyntax.fst completely (175KB!) - document all desugaring transformations
       2. Read FStarC.ToSyntax.Interleave.fst - understand interface/implementation interleaving
       3. Read FStarC.ToSyntax.TickedVars.fst - understand variable handling
       4. Compare Parser.AST nodes to Syntax.Syntax nodes - document the translation

       Your chapter should include:
       - Name resolution algorithm
       - Scope management (how let, match, function introduce scopes)
       - Module and namespace handling
       - Implicit argument insertion
       - Pattern compilation
       - Effect inference at desugar time
       - Error messages generated during desugaring
       - The environment (DsEnv) structure and threading

       Read at least 6 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have sufficient material to write a comprehensive documentation chapter on F*'s desugaring phase. Let me compile this analysis.

       ---
       F* DESUGARING: From Parser AST to Internal Syntax

       Chapter Overview

       This chapter documents F*'s desugaring phase, which transforms the surface-level Parser AST into the internal Syntax representation. The desugaring phase is implemented primarily in the FStarC.ToSyntax.ToSyntax module (4201 lines), with supporting infrastructure in
       FStarC.Syntax.DsEnv (desugaring environment), FStarC.ToSyntax.Interleave (interface/implementation ordering), and FStarC.ToSyntax.TickedVars (implicit variable handling).

       ---
       1. THE DESUGARING ENVIRONMENT (DsEnv)

       The desugaring environment is the central data structure that tracks all scoping information during the translation from Parser AST to internal Syntax.

       1.1 Environment Structure

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:141-170:

       type env = {
         curmodule:            option lident;                   (* name of the module being desugared *)
         curmonad:             option ident;                    (* current monad being desugared *)
         modules:              list (lident & modul);           (* previously desugared modules *)
         scope_mods:           list scope_mod;                  (* STACK of toplevel or local scope modifiers *)
         exported_ids:         SMap.t exported_id_set;          (* identifiers reachable in a module *)
         trans_exported_ids:   SMap.t exported_id_set;          (* transitive version along "include" *)
         includes:             SMap.t (ref (list (lident & restriction)));
         sigaccum:             sigelts;                         (* type declarations being accumulated *)
         sigmap:               SMap.t (sigelt & bool);          (* bool = declared in interface file *)
         iface:                bool;                            (* desugaring an interface? *)
         admitted_iface:       bool;                            (* is it an admitted interface? *)
         expect_typ:           bool;                            (* expect a type at this position *)
         remaining_iface_decls:list (lident & list Parser.AST.decl);
         iface_interleaving_init: bool;
         syntax_only:          bool;                            (* skip type-checking on next push *)
         ds_hooks:             dsenv_hooks;                     (* hooks for symbol tracking *)
         dep_graph:            FStarC.Parser.Dep.deps;
         no_prelude:           bool;
       }

       1.2 Scope Modifiers

       The scope_mods field is a STACK of scope modifiers that track the current visibility context. From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:89-98:

       type scope_mod =
       | Local_bindings           of PSMap.t local_binding  (* local name bindings in scope *)
       | Rec_binding              of rec_binding             (* recursive binding *)
       | Module_abbrev            of module_abbrev           (* module M = ... *)
       | Open_module_or_namespace of open_module_or_namespace & bool  (* bool = implicit open *)
       | Top_level_defs           of PSMap.t unit           (* top-level definitions in scope *)
       | Record_or_dc             of record_or_dc           (* record field visibility *)

       The Local_bindings variant uses a map to avoid linear scans. Each local binding is a triple (ident & bv & used_marker) where the used_marker is a reference to track whether the binding has been used (for unused variable warnings).

       1.3 Environment Threading

       The desugaring functions use a monadic pattern withenv to thread the environment through transformations:

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fsti:53:
       type withenv 'a = env -> 'a & env

       ---
       2. NAME RESOLUTION ALGORITHM

       Name resolution is the process of converting surface identifiers (potentially unqualified) to fully-qualified names. F*'s algorithm handles local bindings, open modules/namespaces, includes, and module abbreviations.

       2.1 Core Resolution Function

       The main resolution function is try_lookup_id'', which scans through scope modifiers in order. From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:441-509:

       let try_lookup_id''
         env
         (id: ident)
         (eikind: exported_id_kind)
         (k_local_binding: local_binding -> cont_t 'a)
         (k_rec_binding:   rec_binding   -> cont_t 'a)
         (k_record: record_or_dc -> cont_t 'a)
         (find_in_module: lident -> cont_t 'a)
         (lookup_default_id: cont_t 'a -> ident -> cont_t 'a) : option 'a
         =
           let proc = function
             | Local_bindings lbs when Some? (PSMap.try_find lbs (string_of_id id)) ->
               let Some l = PSMap.try_find lbs (string_of_id id) in
               let (_, _, used_marker) = l in
               used_marker := true;   (* Mark as used *)
               k_local_binding l

             | Rec_binding r when check_rec_binding_id r ->
               let (_, _, used_marker) = r in
               used_marker := true;
               k_rec_binding r

             | Open_module_or_namespace ((ns, Open_module, restriction),_) ->
               ( match is_ident_allowed_by_restriction id restriction with
               | None -> Cont_ignore
               | Some id -> find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)

             | Top_level_defs ids when Some? (PSMap.try_find ids (string_of_id id)) ->
               lookup_default_id Cont_ignore id  (* might be a val without let yet *)

             | Record_or_dc r when is_exported_id_field eikind ->
               find_in_module_with_includes Exported_id_field ...
             ...
           in
           let rec aux = function
             | a :: q -> option_of_cont (fun _ -> aux q) (proc a)
             | [] -> option_of_cont (fun _ -> None) (lookup_default_id Cont_fail id)
           in aux env.scope_mods

       The algorithm processes scope modifiers in stack order (most recent first), which naturally implements shadowing semantics.

       2.2 Qualified Name Resolution

       For qualified names (e.g., M.N.x), resolution first tries to resolve the namespace part:

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:627-646:

       let resolve_in_open_namespaces'' env lid ... =
         match ns_of_lid lid with
         | _ :: _ ->  (* Qualified name: resolve namespace first *)
           begin match resolve_module_name env (set_lid_range (lid_of_ids (ns_of_lid lid)) ...) true with
           | None -> None
           | Some modul ->
               option_of_cont (fun _ -> None)
                 (find_in_module_with_includes eikind f_module Cont_fail env modul (ident_of_lid lid))
           end
         | [] ->  (* Unqualified name: scan scope mods *)
           try_lookup_id'' env (ident_of_lid lid) eikind k_local_binding k_rec_binding k_record ...

       2.3 Module Name Resolution

       Module names are resolved considering module abbreviations and open namespaces:

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:558-583:

       let resolve_module_name env lid (honor_ns: bool) : option lident =
           let rec aux = function
               | [] ->
                 if module_is_defined env lid then Some lid else None

               | Open_module_or_namespace ((ns, Open_namespace, restriction),_) :: q when honor_ns ->
                 let new_lid = lid_of_path (path_of_lid ns @ path_of_lid lid) ... in
                 if module_is_defined env new_lid then Some new_lid else aux q

               | Module_abbrev (name, modul) :: _ when nslen = 0 && (string_of_id name) = ... ->
                 Some modul  (* Module abbreviation match *)

               | _ :: q -> aux q
           in aux env.scope_mods

       ---
       3. SCOPE MANAGEMENT

       3.1 Pushing Bound Variables

       When a new variable binding is encountered (let, match, function parameter), it must be pushed into the environment:

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fsti:116-117:

       val push_bv': env -> ident -> env & bv & used_marker
       val push_bv: env -> ident -> env & bv

       The push_bv' variant returns the used_marker for tracking unused bindings. The implementation adds a Local_bindings scope modifier.

       3.2 Let Bindings

       Let bindings introduce scopes differently depending on whether they are top-level or local, and whether they are recursive.

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:1425-1567:

       | Let(qual, lbs, body) ->
         let is_rec = qual = LocalRec in
         (* For recursive lets, we need to populate env' with all bindings first *)
         let env', fnames, rec_bindings, used_markers =
           List.fold_left (fun (env, fnames, rec_bindings, used_markers) (_attr_opt, (f, _, _), _) ->
             let env, lbname, rec_bindings, used_markers = match f with
               | Inl x ->
                 let env, xx, used_marker = push_bv' env x in
                 env, Inl xx, S.mk_binder xx::rec_bindings, used_marker::used_markers
               | Inr l ->
                 let env, used_marker = push_top_level_rec_binding env (ident_of_lid l) in
                 env, Inr l, rec_bindings, used_marker::used_markers in
             env, (lbname::fnames), rec_bindings, used_markers) (env, [], [], []) funs
         in

       For recursive bindings, all names are pushed before desugaring any definitions, ensuring mutual visibility.

       3.3 Match Patterns

       Match patterns introduce scopes for pattern variables. The algorithm uses a shared resolution function across or-pattern branches to ensure consistent variable binding:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:662-672:

       let resolvex (l:lenv_t) e x =
         (* This resolution function is shared across PatOr branches *)
         match Option.find (fun y -> (string_of_id y.ppname = string_of_id x)) l with
         | Some y -> l, e, y  (* Reuse existing bv *)
         | _ ->
           let e, xbv = push_bv e x in
           (xbv::l), e, xbv

       3.4 Function Abstractions

       Function abstractions (fun x -> e) introduce scopes for their parameters:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:1227-1325:

       | Abs(binders, body) ->
         (* Check for duplicate parameter names *)
         let bvss = List.map gather_pattern_bound_vars binders in
         begin match check_disjoint bvss with
         | None -> ()
         | Some id -> raise_error id Fatal_NonLinearPatternNotPermitted [...]
         end;
         (* Close over free ticked variables *)
         let _, ftv = List.fold_left (fun (env, ftvs) pat -> ...) (env, []) binders in
         let binders = (ftv |> List.map (fun a ->
             mk_pattern (PatVar(a, Some AST.Implicit, [])) top.range))
           @binders in
         (* Desugar pattern by pattern *)
         let rec aux aqs env bs sc_pat_opt pats : S.term & antiquotations_temp = ...

       ---
       4. MODULE AND NAMESPACE HANDLING

       4.1 Open Declarations

       Open declarations add visibility to a module's exports:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:3477-3479:

       | Open (lid, restriction) ->
         let env = Env.push_namespace env lid restriction in
         env, []

       The restriction parameter controls what identifiers are visible (e.g., open FStar.List { map; filter }).

       4.2 Include Declarations

       Include declarations re-export another module's identifiers:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:3507-3509:

       | Include (lid, restriction) ->
         let env = Env.push_include env lid restriction in
         env, []

       4.3 Module Abbreviations

       Module abbreviations create local aliases:

       | ModuleAbbrev(x, l) ->
         Env.push_module_abbrev env x l, []

       ---
       5. INTERFACE/IMPLEMENTATION INTERLEAVING

       The Interleave module ensures that declarations in an implementation file are processed in an order consistent with their interface signatures.

       5.1 The Ordering Rule

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.Interleave.fst:82-111:

       Ordering rule:
           If a val-declaration for 'a' precedes a val-declaration for 'b',
           then the let-definition for 'a' must precede the let-definition for 'b'.

       Example:
           val a
           let x0
           val b
           let x1

           let a
           let b

       Is effectively ordered as:
           val a
           let x0
           let x1
           let a

           val b
           let b

       5.2 Prefix Algorithm

       The main interleaving function prefixes implementations with their interface declarations:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.Interleave.fst:149-223:

       let rec prefix_with_iface_decls (iface:list decl) (impl:decl) : list decl & list decl =
          match iface with
          | [] -> [], [qualify_karamel_private impl]
          | iface_hd::iface_tl -> begin
            match iface_hd.d with
            | Val(x, _) ->
              let def_ids = definition_lids impl in
              let defines_x = Util.for_some (id_eq_lid x) def_ids in
              if not defines_x then (
                if def_ids |> Util.for_some (fun y ->
                      iface_tl |> Util.for_some (is_val (ident_of_lid y)))
                then raise_error impl Fatal_WrongDefinitionOrder [...]
                iface, [qualify_karamel_private impl]
              ) else (
                (* Handle mutual definitions *)
                let mutually_defined_with_x = def_ids |> List.filter ... in
                let take_iface, rest_iface = aux mutually_defined_with_x iface_tl in
                rest_iface, iface_hd::take_iface@[impl]
              )
            ...

       5.3 Interface Validation

       Interface files are validated to ensure consistency:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.Interleave.fst:225-248:

       let check_initial_interface (iface:list decl) =
           let rec aux iface =
               match iface with
               | hd::tl -> begin
                   match hd.d with
                   | Val(x, t) ->
                     if Util.for_some (is_definition_of x) tl
                     then raise_error hd Fatal_BothValAndLetInInterface
                          "'val x' and 'let x' cannot both be provided in an interface"
                     else if hd.quals |> List.contains Assumption
                     then raise_error hd Fatal_AssumeValInInterface
                          "Interfaces cannot use `assume val x : t`"
                     else ()
                   ...

       ---
       6. IMPLICIT ARGUMENT INSERTION (Ticked Variables)

       F* supports implicit type/universe arguments through "ticked" variables (names starting with ').

       6.1 Detection and Collection

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.TickedVars.fst:33-41:

       let ident_is_ticked (id: ident) : bool =
         let nm = string_of_id id in
         String.length nm > 0 && String.get nm 0 = '\''

       let lident_is_ticked (id: lident) : bool =
         let ns = ns_of_lid id in
         let id = ident_of_lid id in
         Nil? ns && ident_is_ticked id

       6.2 Free Variable Collection

       The free_ticked_vars function traverses a term collecting unbound ticked variables:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.TickedVars.fst:59-68:

       let rec go_term (env : DsEnv.env) (t: term) : m unit =
         match t.tm with
         | Var a ->
           if lident_is_ticked a && None? (Env.try_lookup_id env (Ident.ident_of_lid a)) then
             emit1 (Ident.ident_of_lid a)
           else
             return ()
         ...

       6.3 Closure Over Implicit Variables

       The close function wraps a term with implicit binders for all free ticked variables:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.TickedVars.fst:234-239:

       let close env t =
         let ftv = free_ticked_vars env t in
         if Nil? ftv then t else
           let binders = ftv |> List.map (fun x ->
             mk_binder (Annotated(x, tm_type (pos x))) (pos x) Type_level (Some Implicit)) in
           let result = mk_term (Product(binders, t)) t.range t.level in
           result

       ---
       7. PATTERN COMPILATION

       7.1 Pattern Desugaring

       The main pattern desugaring function handles all pattern forms:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:657-861:

       let rec desugar_data_pat
           (top_level_ascr_allowed : bool)
           (env:env_t)
           (p:pattern)
           : (env_t & bnd & list annotated_pat) & antiquotations_temp =
         ...
         let rec aux' (top:bool) (loc:lenv_t) (aqs:antiquotations_temp) (env:env_t) (p:pattern)
           : lenv_t & antiquotations_temp & env_t & bnd & pat & list (bv & Syntax.typ & list S.term)
           =
           match p.pat with
             | PatWild (aq, attrs) ->
               let x = S.new_bv (Some p.prange) (tun_r p.prange) in
               loc, aqs, env, LocalBinder(x, aq, attrs), pos <| Pat_var x, []

             | PatConst c ->
               let x = S.new_bv (Some p.prange) (tun_r p.prange) in
               loc, aqs, env, LocalBinder(x, None, []), pos <| Pat_constant c, []

             | PatVar (x, aq, attrs) ->
               let loc, env, xbv = resolvex loc env x in
               loc, aqs, env, LocalBinder(xbv, aq, attrs), pos <| Pat_var xbv, []

             | PatApp({pat=PatName l}, args) ->
               let loc, aqs, env, annots, args = List.fold_right (fun arg (loc, aqs, env, annots, args) ->
                 let loc, aqs, env, b, arg, ans = aux loc aqs env arg in
                 let imp = is_implicit b in
                 (loc, aqs, env, ans@annots, (arg, imp)::args)) args (loc, aqs, env, [], []) in
               let l, _ = fail_or env (try_lookup_datacon env) l in
               let x = S.new_bv (Some p.prange) (tun_r p.prange) in
               loc, aqs, env, LocalBinder(x, None, []), pos <| Pat_cons(l, None, args), annots

             | PatList pats -> (* Desugar to Cons/Nil *)
               ...
             | PatTuple(args, dep) -> (* Desugar to tuple constructor *)
               ...
             | PatRecord fields -> (* Build unresolved constructor *)
               ...

       7.2 Linear Pattern Checking

       F* enforces that pattern variables appear exactly once (no non-linear patterns):

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:554-598:

       let check_linear_pattern_variables pats (r:Range.t) =
         let rec pat_vars p : RBSet.t bv =
           match p.v with
           | Pat_var x ->
             if string_of_id x.ppname = Ident.reserved_prefix
             then empty ()
             else singleton x
           | Pat_cons(_, _, pats) ->
             let aux out (p, _) =
                 let p_vars = pat_vars p in
                 let intersection = inter p_vars out in
                 if is_empty intersection
                 then union out p_vars
                 else
                   let duplicate_bv = List.hd (elems intersection) in
                   raise_error duplicate_bv Fatal_NonLinearPatternNotPermitted [...]
             in
             List.fold_left aux (empty ()) pats
         in
         (* Also check coherence across or-patterns *)
         ...

       7.3 Disjunctive Pattern Expansion

       Or-patterns are expanded into multiple branches:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:135-142:

       let desugar_disjunctive_pattern annotated_pats when_opt branch =
           annotated_pats |> List.map (fun (pat, annots) ->
               let branch = List.fold_left (fun br (bv, ty, _) ->
                               let lb = U.mk_letbinding (Inl bv) [] ty C.effect_Tot_lid (S.bv_to_name bv) [] br.pos in
                               let branch = SS.close [S.mk_binder bv] branch in
                               mk (Tm_let {lbs=(false, [lb]); body=branch}) br.pos) branch annots in
               U.branch(pat, when_opt, branch)
           )

       ---
       8. EFFECT INFERENCE AT DESUGAR TIME

       8.1 Computation Type Detection

       The desugarer determines if a type annotation is a computation type (has effect):

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:193-207:

       let rec is_comp_type env t =
           match (unparen t).tm with
           | Name l when lid_equals (Env.current_module env) C.prims_lid &&
                         (let s = string_of_id (ident_of_lid l) in
                          s = "Tot" || s = "GTot") ->
             true
           | Name l
           | Construct(l, _) -> Env.try_lookup_effect_name env l |> Some?
           | App(head, _, _) -> is_comp_type env head
           | Ascribed(t, _, _, _)
           | LetOpen(_, t) -> is_comp_type env t
           | _ -> false

       8.2 Lemma Preprocessing

       The Lemma effect has special syntax sugar that requires preprocessing:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:2242-2335:

       let pre_process_comp_typ (t:AST.term) =
         let head, args = head_and_args t in
         match head.tm with
         | Name lemma when ((string_of_id (ident_of_lid lemma)) = "Lemma") ->
           let unit_tm = mk_term (Name C.unit_lid) t.range Type_level, Nothing in
           let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
           let req_true = ...
           let thunk_ens (e, i) = (thunk e, i) in  (* Postconditions are thunked *)
           let args = match args with
             | [ens] -> [unit_tm;req_true;thunk_ens ens;nil_pat]
             | [req;ens] when is_requires req && is_ensures ens ->
               [unit_tm;req;thunk_ens ens;nil_pat]
             | [ens;smtpat] when is_smt_pat smtpat ->
               [unit_tm;req_true;thunk_ens ens;smtpat]
             ...

       ---
       9. ERROR MESSAGES DURING DESUGARING

       9.1 Common Error Patterns

       The desugarer generates various error messages for syntactic issues:

       Non-linear patterns:
       raise_error duplicate_bv Fatal_NonLinearPatternNotPermitted
         "Non-linear patterns are not permitted: `x` appears more than once in this pattern."

       Variable not found:
       raise_error s Fatal_UnepxectedOrUnboundOperator
         ("Unexpected or unbound operator: " ^ Ident.string_of_id s)

       Wrong definition order (interleaving):
       raise_error impl Fatal_WrongDefinitionOrder [
           text "Expected the definition of" ^/^ pp x ^/^ text "to precede" ^/^ (pp def_ids)
       ]

       9.2 Typo Suggestions

       The DsEnv module includes typo detection for helpful error messages:

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.DsEnv.fst:47-52:

       let typo_candidates (x : string) (xs : list string) : list string =
         let cands = xs |> List.map (fun y -> (EditDist.edit_distance x y, y)) in
         let cands = Class.Ord.sort cands |> Class.Ord.dedup in
         let cands = takeWhileMax 5 (fun (d, _) -> d < 3) cands in
         List.map snd cands

       ---
       10. DECLARATION DESUGARING

       10.1 The Main Entry Point

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:3447-3458:

       and desugar_decl env (d:decl) : (env_t & sigelts) =
         FStarC.GenSym.reset_gensym ();
         let attrs = List.map (desugar_term env) d.attrs in
         let attrs = U.deduplicate_terms attrs in
         let env, ses = desugar_decl_maybe_fail_attr env d attrs in
         let ses =
           if U.has_attribute attrs Const.admitted_lid
           then ses |> List.map (fun se -> { se with sigmeta = { se.sigmeta with sigmeta_admit = true } })
           else ses
         in
         env, ses |> List.map generalize_annotated_univs

       10.2 Type Definitions

       Type definitions (type T = ...) are handled by desugar_tycon:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:2650-2960:

       let rec desugar_tycon env (d: AST.decl) (d_attrs:list S.term) quals tcs : (env_t & sigelts) =
         match tcs with
           | [(TyconAbstract(id, bs, kopt), _)] ->
               (* Abstract type declaration *)
               ...

           | [(TyconAbbrev(id, binders, kopt, t), _)] ->
               (* Type abbreviation *)
               let env', typars = typars_of_binders env binders in
               let t = desugar_typ env' t in
               mk_typ_abbrev env d qlid [] typars kopt t [qlid] quals ...

           | [(TyconRecord payload, d_attrs)] ->
               (* Record type - convert to variant with single constructor *)
               let t, fs = tycon_record_as_variant trec in
               desugar_tycon env d d_attrs (RecordType (...)::quals) [t]

           |  _::_ ->
               (* Mutual type definitions *)
               let mutuals = List.map (fun (x, _) -> qualify env <| tycon_id x) tcs in
               ...

       10.3 Top-Level Let Bindings

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:3646-3717:

       | TopLevelLet(isrec, lets) ->
         let expand_toplevel_pattern = ... in
         if not expand_toplevel_pattern then begin
           let lets = List.map (fun x -> None, x) lets in
           let as_inner_let = mk_term (Let(qual, lets, mk_term (Const Const_unit) ...)) ... in
           let ds_lets, aq = desugar_term_maybe_top true env as_inner_let in
           match (Subst.compress ds_lets).n with
             | Tm_let {lbs} ->
               let fvs = snd lbs |> List.map (fun lb -> Inr?.v lb.lbname) in
               let val_quals, val_attrs = ... in (* Fetch from interface *)
               let s = { sigel = Sig_let {lbs; lids=names}; ... } in
               let env = push_sigelt env s in
               env, [s]

       ---
       11. TERM DESUGARING TRANSFORMATIONS

       11.1 Operator Desugaring

       Operators are resolved to their fully qualified names:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:231-267:

       let op_as_term env arity op : option S.term =
         let r l = Some (S.lid_and_dd_as_fv (set_lid_range l (range_of_id op)) None |> S.fv_to_tm) in
         let fallback () =
           match Ident.string_of_id op with
           | "=" -> r C.op_Eq
           | "<" -> r C.op_LT
           | "&&" -> r C.op_And
           | "||" -> r C.op_Or
           | "+" -> r C.op_Addition
           | "-" when (arity=1) -> r C.op_Minus  (* Unary minus *)
           | "-" -> r C.op_Subtraction
           ...

       11.2 Record Literals

       Record literals are desugared with unresolved constructor annotations that the typechecker resolves:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:1682-1748:

       | Record(eopt, fields) ->
         let uc =
           match record_opt with
           | None ->
             { uc_base_term = Some? eopt;
               uc_typename = None;
               uc_fields = field_names }
           | Some record ->
             { uc_base_term = Some? eopt;
               uc_typename = Some record.typename;
               uc_fields = qualify_field_names record.typename field_names }
         in
         let head = S.fvar_with_dd lid (Some (Unresolved_constructor uc)) in
         S.mk_Tm_app head args top.range

       11.3 Sequence Expressions

       Sequences are desugared to let-unit bindings:

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:1354-1366:

       | Seq(t1, t2) ->
         (* let _ : unit = e1 in e2 *)
         let p = mk_pattern (PatWild (None, [])) t1.range in
         let p = mk_pattern (PatAscribed (p, (unit_ty p.prange, None))) p.prange in
         let t = mk_term (Let(LocalNoLetQualifier, [None, (p, t1)], t2)) top.range Expr in
         let tm, s = desugar_term_aq env t in
         mk (Tm_meta {tm; meta=Meta_desugared Sequence}), s

       ---
       12. BINDER DESUGARING

       12.1 Basic Binder Processing

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:2548-2573:

       and desugar_binder_aq env b : (option ident & S.term & list S.attribute) & antiquotations_temp =
         let attrs = b.battributes |> List.map (desugar_term env) in
         match b.b with
         | Annotated(x, t) ->
           let ty, aqs = desugar_typ_aq env t in
           (Some x, ty, attrs), aqs

         | NoName t ->
           let ty, aqs = desugar_typ_aq env t in
           (None, ty, attrs), aqs

         | Variable x ->
           if ident_is_ticked x
           then (Some x, setPos (range_of_id x) U.ktype, attrs), []  (* Ticked vars get Type *)
           else (Some x, tun_r (range_of_id x), attrs), []           (* Others get unknown type *)

       12.2 Binder Qualification Translation

       From /home/grigory/Downloads/FStar/src/tosyntax/FStarC.ToSyntax.ToSyntax.fst:2589-2597:

       and trans_bqual env = function
         | Some AST.Implicit -> Some S.imp_tag
         | Some AST.Equality -> Some S.Equality
         | Some (AST.Meta t) ->
           Some (S.Meta (desugar_term env t))
         | Some (AST.TypeClassArg) ->
           let tcresolve = desugar_term env (mk_term (Var C.tcresolve_lid) ...) in
           Some (S.Meta tcresolve)
         | None -> None

       ---
       13. KEY DATA TYPE MAPPINGS

       The following table summarizes the main transformations from Parser.AST nodes to Syntax.Syntax nodes:

       | Parser.AST                    | Syntax.Syntax             | Notes                        |
       |-------------------------------|---------------------------|------------------------------|
       | term.Var l                    | Tm_fvar fv                | After name resolution        |
       | term.Name l                   | Tm_fvar fv or Tm_type     | Depends on resolved name     |
       | term.App(h, a, imp)           | Tm_app {hd; args}         | Implicit flags preserved     |
       | term.Abs(bs, e)               | Tm_abs {bs; body; rc_opt} | With pattern compilation     |
       | term.Let(q, lbs, e)           | Tm_let {lbs; body}        | Recursive bindings closed    |
       | term.Match(e, None, opt, brs) | Tm_match {...}            | Branches desugared           |
       | term.Product(bs, t)           | Tm_arrow {bs; comp}       | Creates arrow type           |
       | term.Refine(b, t)             | Tm_refine {b; phi}        | Refinement type              |
       | pattern.PatVar(x,_,_)         | Pat_var bv                | Creates fresh bv             |
       | pattern.PatApp(h, args)       | Pat_cons(fv, _, args)     | Datacon lookup               |
       | decl.TopLevelLet              | Sig_let                   | With universe generalization |
       | decl.Tycon                    | Sig_bundle or Sig_let     | Inductives or abbreviations  |

       ---
       14. SUMMARY

       The F* desugaring phase performs these critical transformations:

       1. Name Resolution: Converts unqualified identifiers to fully-qualified names by searching through scope modifiers (local bindings, opens, includes, abbreviations).
       2. Scope Management: Maintains a stack-based environment that correctly handles shadowing, mutual recursion, and nested scopes from let/match/function.
       3. Implicit Variable Insertion: Detects ticked variables ('a) and closes terms over them as implicit type parameters.
       4. Pattern Compilation: Transforms surface patterns into internal pattern representations, enforcing linearity and expanding or-patterns.
       5. Interface Interleaving: Ensures implementation definitions appear after their interface signatures while preserving semantic ordering.
       6. Effect Detection: Identifies computation types and preprocesses effect abbreviations like Lemma.
       7. Syntactic Sugar: Desugars records, sequences, operators, list/tuple literals, and proof calculus terms into core syntax.

       The result is a well-formed internal AST ready for type inference and elaboration by the typechecker.
  ⎿  Done (18 tool uses · 161.2k tokens · 4m 1s)

● elite-bug-hunter(F* Ch4: Internal Syntax)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering INTERNAL SYNTAX REPRESENTATION.

       Explore /home/grigory/Downloads/FStar/src/syntax/ extensively.

       Focus on:
       1. Read FStarC.Syntax.Syntax.fst completely - document every type (term, binder, universe, etc.)
       2. Read FStarC.Syntax.Util.fst - document key utility functions
       3. Read FStarC.Syntax.Subst.fst - understand substitution
       4. Read FStarC.Syntax.Free.fst - understand free variable computation
       5. Read FStarC.Syntax.Hash.fst - understand term hashing for caching
       6. Read FStarC.Syntax.VisitM.fst - understand monadic traversal

       Your chapter should include:
       - Complete term representation (Tm_app, Tm_abs, Tm_match, etc.)
       - Binder types and binding structure
       - Universe handling
       - Effect annotations in syntax
       - Pattern representation
       - Qualifiers and attributes
       - Metadata and source locations
       - Compression/optimization techniques

       Read at least 10 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive knowledge of the F* syntax internals. Let me write the detailed documentation chapter.

       ---
       F* Internal Syntax Representation: A Comprehensive Technical Reference

       Chapter Overview

       This chapter provides an exhaustive technical documentation of F*'s internal syntax representation, as implemented in the FStarC.Syntax module family. The syntax module forms the core data structures upon which the entire F* compiler operates, from parsing through
       elaboration, type checking, and extraction. Understanding these structures is essential for anyone working on the F* compiler, developing tactics, or building tools that manipulate F* terms programmatically.

       ---
       1. Core Term Representation

       The central type in F*'s syntax is term, which represents all expressions and types in the language. Terms are wrapped in a syntax record that carries metadata:

       1.1 The Syntax Wrapper

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 357-362

       and syntax 'a = {
           n:'a;
           pos:range;
           vars:memo free_vars;
           hash_code:memo FStarC.Hash.hash_code
       }

       Every term node is wrapped in this record containing:
       - n: The actual term constructor
       - pos: Source location (range) for error reporting
       - vars: Memoized free variables (computed lazily)
       - hash_code: Memoized hash code for efficient equality checking

       The memo type is a mutable reference to an optional value, allowing lazy computation and caching:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 49-50

       type memo 'a = ref (option 'a)

       1.2 Term Constructors (term')

       The term' type enumerates all possible term forms:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 123-174

       type term' =
         | Tm_bvar       of bv                // Bound variable (de Bruijn index)
         | Tm_name       of bv                // Local constant (unique name)
         | Tm_fvar       of fv                // Fully qualified top-level reference
         | Tm_uinst      of term & universes  // Universe instantiation
         | Tm_constant   of sconst            // Primitive constants
         | Tm_type       of universe          // Type at a universe level
         | Tm_abs        { bs:binders; body:term; rc_opt:option residual_comp }
         | Tm_arrow      { bs:binders; comp:comp }
         | Tm_refine     { b:bv; phi:term }
         | Tm_app        { hd:term; args:args }
         | Tm_match      { scrutinee:term; ret_opt:option match_returns_ascription;
                           brs:list branch; rc_opt:option residual_comp }
         | Tm_ascribed   { tm:term; asc:ascription; eff_opt:option lident }
         | Tm_let        { lbs:letbindings; body:term }
         | Tm_uvar       of ctx_uvar_and_subst
         | Tm_delayed    { tm:term; substs:subst_ts }
         | Tm_meta       { tm:term; meta:metadata }
         | Tm_lazy       of lazyinfo
         | Tm_quoted     of term & quoteinfo
         | Tm_unknown

       Variable Representation

       F* uses a hybrid naming scheme combining de Bruijn indices with named variables:

       Tm_bvar (Bound Variables): Variables bound by lambda, let, or pattern matching, referenced by de Bruijn index. The index counts from the innermost binder (0) outward.

       Tm_name (Named Variables): Local constants with unique identifiers. These are "opened" bound variables used during type checking for more readable error messages.

       Tm_fvar (Free Variables): Fully qualified references to top-level definitions from modules.

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 363-371

       and bv = {
           ppname:ident;  // Programmer-provided name for pretty-printing
           index:int;     // de Bruijn index (0-based, counting up from binder)
           sort:term      // The type of this variable
       }

       and fv = {
           fv_name :var;           // Fully qualified name (lident)
           fv_qual :option fv_qual // Constructor/projector qualification
       }

       The fv_qual distinguishes data constructors from projectors:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 333-343

       and fv_qual =
         | Data_ctor
         | Record_projector of (lident & ident)
         | Record_ctor of lident & list ident
         | Unresolved_projector of option fv
         | Unresolved_constructor of unresolved_constructor

       Application and Abstraction

       Tm_app: Function application with the head term and a list of arguments:

       | Tm_app { hd:term; args:args }

       Arguments include implicit/explicit qualification:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 295-296

       and arg = term & aqual  // Term with optional argument qualifier
       and args = list arg

       Tm_abs: Lambda abstraction with binders, body, and optional residual computation type:

       | Tm_abs { bs:binders; body:term; rc_opt:option residual_comp }

       The residual computation type caches effect information after type checking:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 380-384

       and residual_comp = {
           residual_effect:lident;          // Effect name
           residual_typ   :option typ;      // Result type
           residual_flags :list cflag       // Computation flags
       }

       Refinement Types

       Tm_refine: Dependent refinement types {x:t | phi}:

       | Tm_refine { b:bv; phi:term }

       The bound variable b is in scope within the refinement formula phi.

       Pattern Matching

       Tm_match: Pattern matching with optional return annotation:

       | Tm_match { scrutinee:term;
                    ret_opt:option match_returns_ascription;
                    brs:list branch;
                    rc_opt:option residual_comp }

       Branches are triples of pattern, optional guard, and body:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti line 198

       and branch = pat & option term & term  // (pattern, when-guard, body)

       ---
       2. Binder Types and Binding Structure

       2.1 Binder Definition

       Binders carry rich information about parameter binding:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 297-303

       and binder = {
         binder_bv    : bv;                            // The bound variable
         binder_qual  : bqual;                         // Implicit/explicit/meta
         binder_positivity : option positivity_qualifier;  // Strictly positive?
         binder_attrs : list attribute                 // Attached attributes
       }
       and binders = list binder

       2.2 Binder Qualifiers

       Binder qualifiers control implicit argument handling:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 431-435

       and binder_qualifier =
         | Implicit of bool   // bool marks inaccessible implicit (data constructor arg)
         | Meta of term       // Meta-argument specifying a tactic
         | Equality           // Equality constraint binder
       and bqual = option binder_qualifier

       Argument qualifiers track attributes on applied arguments:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 436-440

       and arg_qualifier = {
         aqual_implicit : bool;
         aqual_attributes : list attribute
       }
       and aqual = option arg_qualifier

       2.3 Positivity Qualifiers

       For inductive type checking:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 119-121

       type positivity_qualifier =
         | BinderStrictlyPositive
         | BinderUnused

       ---
       3. Universe Handling

       F*'s universe polymorphism is central to its type theory. Universe levels form a hierarchy where Type u : Type (u+1).

       3.1 Universe Terms

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 68-77

       type universe =
         | U_zero                          // Base universe (0)
         | U_succ  of universe             // Successor (u + 1)
         | U_max   of list universe        // Maximum of universes
         | U_bvar  of int                  // Bound universe variable (de Bruijn)
         | U_name  of univ_name            // Named universe variable
         | U_unif  of universe_uvar        // Unification variable
         | U_unknown                       // Placeholder during elaboration

       and univ_name = ident
       and universe_uvar = Unionfind.p_uvar (option universe) & version & range

       3.2 Universe Variable Management

       Universe unification variables use the same unionfind infrastructure as term uvars but with a separate graph:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Unionfind.fst lines 205-213

       let univ_uvar_id u  = PU.puf_id (get_univ_graph()) (chk_v_u u)
       let univ_fresh (rng:Range.t) =
           fail_if_ro ();
           PU.puf_fresh (get_univ_graph()) None, get_version(), rng

       let univ_find u     = PU.puf_find (get_univ_graph()) (chk_v_u u)
       let univ_change u t = set_univ_graph (PU.puf_change (get_univ_graph()) (chk_v_u u) (Some t))
       let univ_equiv  u v = PU.puf_equivalent (get_univ_graph()) (chk_v_u u) (chk_v_u v)

       3.3 Universe Compression

       Universe compression resolves unification variables:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 108-114

       let rec compress_univ u = match u with
           | U_unif u' ->
             begin match Unionfind.univ_find u' with
               | Some u -> compress_univ u
               | _ -> u
             end
           | _ -> u

       ---
       4. Effect Annotations in Syntax

       4.1 Computation Types

       Computation types describe effectful computations:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 280-294

       and comp_typ = {
         comp_univs:universes;    // Universe arguments
         effect_name:lident;      // Effect name (e.g., Tot, Div, ST)
         result_typ:typ;          // Return type
         effect_args:args;        // Effect indices/WPs
         flags:list cflag         // Optimization flags
       }

       and comp' =
         | Total  of typ          // Pure total computation
         | GTotal of typ          // Ghost total computation
         | Comp   of comp_typ     // General effect

       and comp = syntax comp'

       4.2 Computation Flags

       Flags optimize compilation and SMT encoding:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 307-317

       and cflag =
         | TOTAL                      // No real effect, safe to reduce
         | MLEFFECT                   // ML effect
         | LEMMA                      // Lemma effect
         | RETURN                     // WP is return_wp
         | PARTIAL_RETURN             // Return with precondition
         | SOMETRIVIAL                // Null WP
         | TRIVIAL_POSTCONDITION      // No meaningful postcondition
         | SHOULD_NOT_INLINE          // Prevent inlining
         | CPS                        // CPS-transformed (DM4F)
         | DECREASES of decreases_order  // Termination measure

       4.3 Decreases Clauses

       Termination measures can be lexicographic or well-founded:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 304-306

       and decreases_order =
         | Decreases_lex of list term    // Lexicographic ordering
         | Decreases_wf of term & term   // Well-founded relation and term

       ---
       5. Pattern Representation

       5.1 Pattern Constructors

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 201-206

       and pat' =
         | Pat_constant of sconst                           // Literal pattern
         | Pat_cons     of fv & option universes &          // Constructor pattern
                           list (pat & bool)                 // (sub-patterns, explicit?)
         | Pat_var      of bv                               // Variable binding
         | Pat_dot_term of option term                      // Inaccessible pattern

       and pat = withinfo_t pat'  // Pattern with source range

       The withinfo_t wrapper provides source location:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 35-39

       type withinfo_t 'a = {
         v: 'a;   // The value
         p: range; // Source position
       }

       5.2 Pattern Variable Extraction

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fst lines 415-422

       let pat_bvs (p:pat) : list bv =
           let rec aux b p = match p.v with
               | Pat_dot_term _
               | Pat_constant _ -> b
               | Pat_var x -> x::b
               | Pat_cons(_, _, pats) -> List.fold_left (fun b (p, _) -> aux b p) b pats
           in
           List.rev <| aux [] p

       ---
       6. Qualifiers and Attributes

       6.1 Declaration Qualifiers

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 458-485

       type qualifier =
         | Assumption                    // No definition, just declaration
         | New                           // Fresh type constant
         | Private                       // Module-private
         | Unfold_for_unification_and_vcgen  // Always unfold
         | Irreducible                   // Never unfold
         | Inline_for_extraction         // Must unfold for extraction
         | NoExtract                     // Don't extract
         | Noeq                          // Don't generate HasEq
         | Unopteq                       // Unoptimized HasEq
         | TotalEffect                   // Effect forbids non-termination
         | Logic                         // For refinement logic only
         | Reifiable                     // Effect can be reified
         | Reflectable of lident         // Effect can be reflected
         | Visible_default               // May unfold if necessary
         | Discriminator of lident       // Discriminator function
         | Projector of lident & ident   // Field projector
         | RecordType of (list ident & list ident)
         | RecordConstructor of (list ident & list ident)
         | Action of lident              // Effect action
         | ExceptionConstructor          // Prims.exn constructor
         | HasMaskedEffect               // Top-level effectful let
         | Effect                        // Effect constructor name
         | OnlyName                      // Placeholder for elaboration
         | InternalAssumption            // F*-generated assumption

       6.2 Attributes

       Attributes are simply terms attached to declarations:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti line 386

       and attribute = term

       ---
       7. Metadata and Source Locations

       7.1 Term Metadata

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 318-326

       and metadata =
         | Meta_pattern       of list term & list args  // SMT triggers
         | Meta_named         of lident                 // Type abbreviation name
         | Meta_labeled       of list Pprint.document & range & bool  // VC labels
         | Meta_desugared     of meta_source_info       // Desugaring info
         | Meta_monadic       of monad_name & typ       // Monadic annotation
         | Meta_monadic_lift  of monad_name & monad_name & typ  // Effect lift

       7.2 Desugaring Information

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 327-332

       and meta_source_info =
         | Sequence                           // Sequencing (;)
         | Primop                             // Primitive operation
         | Masked_effect                      // Effect masking
         | Meta_smt_pat                       // SMT pattern
         | Machine_integer of signedness & width  // Fixed-width integer

       ---
       8. Substitution System

       F* uses delayed substitutions for efficient term manipulation. Substitutions are composed rather than immediately applied.

       8.1 Substitution Elements

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 349-356

       and subst_elt =
          | DB of int & bv     // Replace bound var index i with name bv
          | DT of int & term   // Replace bound var index i with term
          | NM of bv  & int    // Replace name with bound var index
          | NT of bv  & term   // Replace name with term
          | UN of int & universe   // Replace universe var
          | UD of univ_name & int  // Replace universe name

       8.2 Substitution Composition

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 60-65

       let compose_subst (s1 s2 : subst_ts) : subst_ts =
           let s = fst s1 @ fst s2 in
           let ropt = match snd s2 with
                      | SomeUseRange _ -> snd s2
                      | _ -> snd s1 in
           (s, ropt)

       8.3 The Delay Function

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 69-78

       let delay (t:term) (s : subst_ts) : term =
        match t.n with
        | Tm_delayed {tm=t'; substs=s'} ->
           mk_Tm_delayed (t', compose_subst s' s) t.pos
        | _ ->
           mk_Tm_delayed (t, s) t.pos

       8.4 The Compress Function

       The critical compress function forces delayed substitutions and resolves uvars:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 533-550

       let rec compress_slow (t:term) =
           let t = force_uvar t in
           match t.n with
           | Tm_delayed {tm=t'; substs=s} ->
               compress (push_subst s t')
           | _ ->
               t

       and compress (t:term) =
         match t.n with
           | Tm_delayed _ | Tm_uvar _ ->
               let r = compress_slow t in
               r
           | _ ->
               t

       8.5 Opening and Closing Binders

       Opening converts bound variables to names:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 565-576

       let open_binders' bs =
          let rec aux bs o = match bs with
               | [] -> [], o
               | b::bs' ->
                 let x' = {freshen_bv b.binder_bv with sort=subst o b.binder_bv.sort} in
                 let imp = subst_bqual o b.binder_qual in
                 let attrs = b.binder_attrs |> List.map (subst o) in
                 let o = DB(0, x')::shift_subst 1 o in
                 let bs', o = aux bs' o in
                 (S.mk_binder_with_attrs x' imp b.binder_positivity attrs)::bs', o in
          aux bs []

       Closing converts names back to bound variables:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Subst.fst lines 563-564

       let closing_subst (bs:binders) =
           List.fold_right (fun b (subst, n) -> (NM(b.binder_bv, n)::subst, n+1)) bs ([], 0) |> fst

       ---
       9. Free Variable Computation

       9.1 Free Variables Record

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 372-377

       and free_vars = {
           free_names      : FlatSet.t bv;          // Free term variables
           free_uvars      : uvars;                 // Free unification variables
           free_univs      : FlatSet.t universe_uvar;  // Free universe uvars
           free_univ_names : FlatSet.t univ_name;   // Free universe names
       }

       9.2 Caching Strategy

       The free variable computation uses memoization at each node:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Free.fst lines 242-250

       and free_names_and_uvars t use_cache =
         let t = Subst.compress t in
         match !t.vars with
         | Some n when not (should_invalidate_cache n use_cache) -> n, empty ()
         | _ ->
             t.vars := None;
             let n = free_names_and_uvs' t use_cache in
             if use_cache <> Full then t.vars := Some (fst n);
             n

       9.3 Cache Invalidation

       The cache must be invalidated when uvars are resolved:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Free.fst lines 293-302

       and should_invalidate_cache n use_cache =
           (use_cache <> Def) ||
           (n.free_uvars |> for_any (fun u ->
                match UF.find u.ctx_uvar_head with
                | Some _ -> true
                | _ -> false)) ||
           (n.free_univs |> for_any (fun u ->
                  match UF.univ_find u with
                  | Some _ -> true
                  | None -> false))

       ---
       10. Term Hashing for Caching

       10.1 Hashing Infrastructure

       Term hashing enables efficient equality checking and hash-consing:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Hash.fst lines 42-54

       let maybe_memoize (h:syntax 'a) (f:syntax 'a -> mm H.hash_code) : mm H.hash_code =
         fun should_memo ->
           if should_memo
           then (
             match !h.hash_code with
             | Some c -> c, should_memo
             | None ->
               let c, should_memo = f h should_memo in
               if should_memo
               then h.hash_code := Some c;
               c, should_memo
           )
           else f h should_memo

       10.2 Term Hashing

       Each constructor gets a unique prime-based hash:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Hash.fst lines 99-134

       and hash_term' (t:term) : mm H.hash_code =
           match (SS.compress t).n with
           | Tm_bvar bv -> mix (of_int 3) (of_int bv.index)
           | Tm_name bv -> mix (of_int 5) (of_int bv.index)
           | Tm_fvar fv -> mix (of_int 7) (hash_fv fv)
           | Tm_uinst(t, us) -> mix (of_int 11)
                                      (mix (hash_term t) (hash_list hash_universe us))
           | Tm_constant sc -> mix (of_int 13) (hash_constant sc)
           | Tm_type u -> mix (of_int 17) (hash_universe u)
           | Tm_abs {bs; body=t; rc_opt=rcopt} ->
               mix (of_int 19) (mix (hash_list hash_binder bs)
                                    (mix (hash_term t) (hash_option hash_rc rcopt)))
           // ... other cases with distinct primes

       10.3 Hash-Based Equality

       Hashing enables fast inequality detection:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Hash.fst lines 360-365

       let rec equal_term (t1 t2:term) : bool =
         if physical_equality t1 t2 then true else
         if physical_equality t1.n t2.n then true else
         if ext_hash_term t1 <> ext_hash_term t2 then false else
         // ... structural comparison

       ---
       11. Monadic Traversal (VisitM)

       11.1 Visitor Monad Class

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.VisitM.fst lines 16-28

       class lvm (m:Type->Type) : Type = {
         lvm_monad       : monad m;

         f_term          : endo m term;
         f_binder        : endo m binder;
         f_binding_bv    : endo m bv;
         f_br            : endo m branch;
         f_comp          : endo m comp;
         f_residual_comp : endo m residual_comp;
         f_univ          : endo m universe;

         proc_quotes     : bool;
       }

       11.2 Tying the Knot

       Bottom-up traversal with callbacks:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.VisitM.fst lines 490-507

       let tie_bu (#m : Type -> Type) {| md : monad m |} (d : lvm m) : lvm m =
         let r : ref (lvm m) = mk_ref (novfs #m #md) in
         r :=
           {
             lvm_monad       = (!r).lvm_monad;
             f_term          = (fun x -> f_term #_ #d <<| on_sub_term #_ #!r x);
             f_binding_bv    = (fun x -> f_binding_bv #_ #d <<| on_sub_binding_bv #_ #!r x);
             f_binder        = (fun x -> f_binder #_ #d <<| on_sub_binder #_ #!r x);
             f_br            = (fun x -> f_br #_ #d <<| on_sub_br #_ #!r x);
             f_comp          = (fun x -> f_comp #_ #d <<| on_sub_comp #_ #!r x);
             f_residual_comp = (fun x -> f_residual_comp #_ #d <<| on_sub_residual_comp #_ #!r x);
             f_univ          = (fun x -> f_univ #_ #d <<| on_sub_univ #_ #!r x);
             proc_quotes     = d.proc_quotes;
           };
         !r

       11.3 Using Visitors

       Example: collecting all free variables appearing in a sigelt:

       let open FStarC.Writer in
       type mymon = writer (list lident)

       let m = VisitM.visitM_sigelt
                (fun t -> (match t.n with
                          | Tm_fvar fv -> Writer.emit [lid_of_fv fv]
                          | _ -> return ());
                          return t)
                (fun u -> return u) se
       in
       let lids, _ = Writer.run_writer m in

       ---
       12. Deep Compression

       12.1 Purpose

       Deep compression eliminates all delayed substitutions and resolves all uvars, preparing terms for serialization:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Compress.fst lines 51-72

       (* deep_compress_*: eliminating all unification variables and delayed
       substitutions in a sigelt. We traverse the entire syntactic structure
       to evaluate the explicit lazy substitutions (Tm_delayed) and to replace
       uvar nodes (Tm_uvar/U_unif) with their solutions.

       The return value of this function should *never* contain a lambda. This
       applies to every component of the term/sigelt: attributes, metadata, BV
       sorts, universes, memoized free variables, substitutions, etc.

       This is done to later dump the term/sigelt into a file (via OCaml's
       output_value, for instance). This marshalling does not handle
       closures[1] and we do not store the UF graph, so we cannot have any
       lambdas and every uvar node that must be replaced by its solution (and
       hence must have been resolved). *)

       12.2 Implementation

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Compress.fst lines 73-80

       let deep_compress (allow_uvars:bool) (allow_names: bool) (tm : term) : term =
         Stats.record "deep_compress" fun () ->
         Err.with_ctx ("While deep-compressing a term") (fun () ->
           Visit.visit_term_univs true
             (compress1_t allow_uvars allow_names)
             (compress1_u allow_uvars allow_names)
             tm
         )

       ---
       13. Unification Variables (Uvars)

       13.1 Context Uvars

       Uvars carry their typing context:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 175-186

       and ctx_uvar = {
         ctx_uvar_head:uvar;        // The actual uvar reference
         ctx_uvar_gamma:gamma;      // Context (cons list of bindings)
         ctx_uvar_binders:binders;  // Tm_name bindings (snoc list)
         ctx_uvar_reason:string;    // Why was this created
         ctx_uvar_range:range;      // Source location
         ctx_uvar_meta: option ctx_uvar_meta_t;  // Tactic/attribute metadata
       }

       and ctx_uvar_meta_t =
         | Ctx_uvar_meta_tac of term   // Solve by tactic
         | Ctx_uvar_meta_attr of term  // Defer_to attribute

       13.2 Unionfind Graph

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Unionfind.fst lines 57-62

       type uf = {
         term_graph: tgraph;   // Term unification graph
         univ_graph: ugraph;   // Universe unification graph
         version:version;      // For transaction management
         ro:bool;              // Read-only mode
       }

       13.3 Transaction Support

       For backtracking during type inference:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Unionfind.fst lines 128-134

       let new_transaction () =
           let tx = TX (get ()) in
           set ({get() with version=vops.next_minor()});
           tx
       let commit (tx:tx) = ()
       let rollback (TX uf) = set uf

       ---
       14. Lazy Terms

       14.1 Lazy Info Structure

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 388-393

       and lazyinfo = {
           blob  : dyn;          // Dynamic blob (any type)
           lkind : lazy_kind;    // What kind of lazy term
           ltyp  : typ;          // The type
           rng   : range;        // Source range
       }

       14.2 Lazy Kinds

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 398-420

       and lazy_kind =
         | BadLazy
         | Lazy_bv | Lazy_namedv | Lazy_binder | Lazy_optionstate
         | Lazy_fvar | Lazy_comp | Lazy_env | Lazy_proofstate
         | Lazy_ref_proofstate | Lazy_goal | Lazy_sigelt | Lazy_uvar
         | Lazy_letbinding | Lazy_embedding of emb_typ & Thunk.t term
         | Lazy_universe | Lazy_universe_uvar | Lazy_issue
         | Lazy_ident | Lazy_doc | Lazy_extension of string | Lazy_tref

       14.3 Unfolding Lazy Terms

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Util.fst lines 458-463

       let unfold_lazy i = Option.must !lazy_chooser i.lkind i

       let rec unlazy t =
           match (compress t).n with
           | Tm_lazy i -> unlazy <| unfold_lazy i
           | _ -> t

       ---
       15. Quoted Terms and Antiquotations

       15.1 Quote Info

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 217-279

       and antiquotations = int & list term  // Shift and antiquoted terms

       and quoteinfo = {
           qkind          : quote_kind;
           antiquotations : antiquotations;
       }

       15.2 Quote Kinds

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 89-91

       type quote_kind =
         | Quote_static   // Compile-time quote (`)
         | Quote_dynamic  // Runtime quote (quote)

       15.3 Antiquotation Handling

       Antiquotations use de Bruijn indices pointing into the antiquotation list:

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fst lines 244-249

       let lookup_aq (bv : bv) (aq : antiquotations) : term =
           try List.nth (snd aq) (List.length (snd aq) - 1 - bv.index + fst aq)
           with
           | _ ->
             failwith "antiquotation out of bounds"

       ---
       16. Signature Elements

       16.1 Sigelt Structure

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 760-768

       and sigelt = {
           sigel:    sigelt';                // The actual declaration
           sigrng:   range;                  // Source location
           sigquals: list qualifier;         // Qualifiers
           sigmeta:  sig_metadata;           // Metadata
           sigattrs: list attribute;         // Attributes
           sigopens_and_abbrevs: list (either open_module_or_namespace module_abbrev);
           sigopts:  option vconfig;         // Option context
       }

       16.2 Sigelt Constructors

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fsti lines 677-758

       type sigelt' =
         | Sig_inductive_typ { lid; us; params; num_uniform_params; t; mutuals; ds; injective_type_params }
         | Sig_bundle { ses:list sigelt; lids:list lident }
         | Sig_datacon { lid; us; t; ty_lid; num_ty_params; mutuals; injective_type_params; proj_disc_lids }
         | Sig_declare_typ { lid; us; t }
         | Sig_let { lbs:letbindings; lids:list lident }
         | Sig_assume { lid; us; phi:formula }
         | Sig_new_effect of eff_decl
         | Sig_sub_effect of sub_eff
         | Sig_effect_abbrev { lid; us; bs; comp; cflags }
         | Sig_pragma of pragma
         | Sig_splice { is_typed:bool; lids:list lident; tac:term }
         | Sig_polymonadic_bind { m_lid; n_lid; p_lid; tm; typ; kind }
         | Sig_polymonadic_subcomp { m_lid; n_lid; tm; typ; kind }
         | Sig_fail { errs; rng; fail_in_lax; ses }

       ---
       17. Key Utility Functions

       17.1 Head and Arguments Extraction

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Util.fst lines 346-362

       let head_and_args t =
           let t = compress t in
           match t.n with
           | Tm_app {hd=head; args} -> head, args
           | _ -> t, []

       let rec __head_and_args_full acc unmeta t =
           let t = compress t in
           match t.n with
           | Tm_app {hd=head; args} ->
             __head_and_args_full (args@acc) unmeta head
           | Tm_meta {tm} when unmeta ->
             __head_and_args_full acc unmeta tm
           | _ -> t, acc

       let head_and_args_full t = __head_and_args_full [] false t

       17.2 Arrow Decomposition

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Util.fst lines 742-761

       let rec arrow_formals_comp_ln (k:term) =
           let k = Subst.compress k in
           match k.n with
               | Tm_arrow {bs; comp=c} ->
                   if is_total_comp c && not (has_decreases c)
                   then let bs', k = arrow_formals_comp_ln (comp_result c) in
                        bs@bs', k
                   else bs, c
               | Tm_refine {b={ sort = s }} ->
                 let rec aux (s:term) (k:term) =
                   match (Subst.compress s).n with
                   | Tm_arrow _ -> arrow_formals_comp_ln s
                   | Tm_refine {b={ sort = s }} -> aux s k
                   | _ -> [], Syntax.mk_Total k
                 in
                 aux s k
               | _ -> [], Syntax.mk_Total k

       17.3 Constructor Helpers

       File: /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Util.fst lines 675-688

       let abs bs t lopt =
         let close_lopt lopt = match lopt with
             | None -> None
             | Some rc -> Some ({rc with residual_typ = Option.map (close bs) rc.residual_typ})
         in
         match bs with
         | [] -> t
         | _ ->
           let body = compress (Subst.close bs t) in
           match body.n with
               | Tm_abs {bs=bs'; body=t; rc_opt=lopt'} ->
                 mk (Tm_abs {bs=close_binders bs@bs'; body=t; rc_opt=close_lopt lopt'}) t.pos
               | _ ->
                 mk (Tm_abs {bs=close_binders bs; body; rc_opt=close_lopt lopt}) t.pos

       ---
       18. Summary

       The F* syntax module provides a sophisticated representation of terms that balances expressiveness with efficiency:

       1. De Bruijn Indices with Named Variables: Combines the capture-avoiding properties of de Bruijn representation with readable named variables for error messages.
       2. Delayed Substitutions: Substitutions compose rather than immediately apply, enabling efficient manipulation of large terms.
       3. Memoization: Free variables and hash codes are cached at each node, with careful cache invalidation when uvars are resolved.
       4. Rich Metadata: Source locations, attributes, qualifiers, and effect information are preserved throughout compilation.
       5. Unionfind for Unification: Term and universe unification variables use a transactional unionfind data structure supporting backtracking.
       6. Lazy Evaluation: Tm_lazy nodes defer expensive computations until needed.
       7. Visitor Framework: The monadic visitor pattern (VisitM) enables flexible term transformations.

       This infrastructure forms the foundation upon which F*'s powerful type system, effect system, and proof automation are built.
  ⎿  Done (13 tool uses · 166.1k tokens · 3m 43s)

● elite-bug-hunter(F* Ch5: Type Checker Core)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering TYPE CHECKER CORE.

       Explore /home/grigory/Downloads/FStar/src/typechecker/ extensively.

       Focus on:
       1. Read FStarC.TypeChecker.Core.fst completely - document the core type checking logic
       2. Read FStarC.TypeChecker.Env.fst - understand the type checking environment
       3. Read FStarC.TypeChecker.Common.fst - understand shared utilities
       4. Read FStarC.TypeChecker.Err.fst - understand error handling
       5. Read FStarC.TypeChecker.Quals.fst - understand qualifier inference
       6. Read FStarC.TypeChecker.Generalize.fst - understand type generalization

       Your chapter should include:
       - Bidirectional type checking algorithm (check vs infer modes)
       - Environment structure and lookup
       - Implicit argument handling
       - Guard generation and solving
       - Type abbreviation handling
       - Recursive definition checking
       - Error reporting with source locations
       - Interaction with SMT solver

       Read at least 10 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have gathered comprehensive information about the F* type checker. Let me write the detailed documentation chapter:

       ---
       F* TYPE CHECKER CORE: COMPREHENSIVE DOCUMENTATION

       Chapter Overview

       This chapter provides an in-depth examination of the F* type checker core, located in /home/grigory/Downloads/FStar/src/typechecker/. The core type checker implements a bidirectional type checking algorithm for pure and ghost F* terms, with sophisticated caching
       mechanisms, guard generation, and SMT interaction.

       ---
       1. ARCHITECTURAL OVERVIEW

       1.1 Module Organization

       The type checker is organized into several key modules:

       | Module     | File                              | Purpose                                               |
       |------------|-----------------------------------|-------------------------------------------------------|
       | Core       | FStarC.TypeChecker.Core.fst       | Core bidirectional type checking for pure/ghost terms |
       | Env        | FStarC.TypeChecker.Env.fst        | Type checking environment and context management      |
       | Common     | FStarC.TypeChecker.Common.fst     | Shared types: guards, problems, identifier info       |
       | Err        | FStarC.TypeChecker.Err.fst        | Error message formatting and reporting                |
       | Generalize | FStarC.TypeChecker.Generalize.fst | ML-style type generalization                          |
       | Quals      | FStarC.TypeChecker.Quals.fst      | Qualifier checking and inference                      |

       1.2 Core Type Checking Judgment

       The fundamental judgment implemented by the core checker is:

       G |- e : t | p

       Where:
       - G is the typing environment
       - e is the term being checked
       - t is the computed/checked type
       - p is a guard (precondition) that must be proven for the typing to hold

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:25-31:

       (* The guard t is a precondition of typing computed by the core checker;
          Once the guard is proven, the caller should call commit_guard on the 
          guard_commit_token_cb to notify the core checker that the guard was
          proven, allowing it to cache the result *)
       type guard_and_tok_t = typ & guard_commit_token_cb

       ---
       2. BIDIRECTIONAL TYPE CHECKING

       2.1 Checking Modes

       F* implements a bidirectional type checking algorithm with two primary modes:

       Inference Mode (Synthesis): Computes the type of a term
       // From FStarC.TypeChecker.Core.fst:65-66
       val compute_term_type (g:Env.env) (e:term)
         : either (tot_or_ghost & typ & option guard_and_tok_t) error

       Checking Mode: Verifies a term has an expected type
       // From FStarC.TypeChecker.Core.fst:59-60
       val check_term (g:Env.env) (e:term) (t:typ) (must_tot:bool)
         : either (option guard_and_tok_t) error

       2.2 Effect Classification

       The checker distinguishes between total and ghost computations:

       // From FStarC.TypeChecker.Core.fst:32-34
       type tot_or_ghost =
         | E_Total
         | E_Ghost

       2.3 The Main Checking Function

       The heart of the type checker is do_check, which handles all term forms. Here is the structure from /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1565-1598:

       and do_check (g:env) (e:term)
         : result (tot_or_ghost & typ) =
         let e = Subst.compress e in
         match e.n with
         | Tm_lazy ({lkind=Lazy_embedding _}) ->
           do_check g (U.unlazy e)

         | Tm_lazy i ->
           return (E_Total, i.ltyp)

         | Tm_meta {tm=t} ->
           memo_check g t

         | Tm_uvar (uv, s) ->
           return (E_Total, Subst.subst' s (U.ctx_uvar_typ uv))

         | Tm_name x ->
           begin
           match Env.try_lookup_bv g.tcenv x with
           | None ->
             fail_str (Format.fmt1 "Variable not found: %s" (show x))
           | Some (t, _) ->
             return (E_Total, t)
           end

         | Tm_fvar f ->
           begin
           match Env.try_lookup_lid g.tcenv f.fv_name with
           | Some (([], t), _) ->
             return (E_Total, t)
           | _ -> //no implicit universe instantiation allowed
             fail_str "Missing universes instantiation"
           end

       2.4 Application Type Checking

       Function application is handled specially, with support for short-circuit operators. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1654-1686:

         | Tm_app _ -> (
           let rec check_app_arg (eff_hd, t_hd) (arg, arg_qual) =
             let! x, eff_arr, t' = is_arrow g t_hd in
             let! eff_arg, t_arg = check "app arg" g arg in
             with_context "app subtyping" (Some (CtxTerm arg))
               (fun _ -> check_subtype g (Some arg) t_arg x.binder_bv.sort) ;!
             with_context "app arg qual" None
               (fun _ -> check_arg_qual arg_qual x.binder_qual) ;!
             return (join_eff eff_hd (join_eff eff_arr eff_arg),
                     Subst.subst [NT(x.binder_bv, arg)] t')
           in
           let check_app hd args =
              let! eff_hd, t = check "app head" g hd in
              fold check_app_arg (eff_hd, t) args
           in
           ...

       2.5 Let Binding Checking

       Let bindings require checking both the definition and body, with proper scoping. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1707-1724:

         | Tm_let {lbs=(false, [lb]); body} ->
           let Inl x = lb.lbname in
           let g', x, body = open_term g (S.mk_binder x) body in
           if U.is_pure_or_ghost_effect lb.lbeff
           then (
             let! eff_def, tdef = check "let definition" g lb.lbdef in
             let! _, ttyp = check "let type" g lb.lbtyp in
             let! u = is_type g ttyp in
             with_context "let subtyping" None
               (fun _ -> check_subtype g (Some lb.lbdef) tdef lb.lbtyp) ;!
             with_definition g x u lb.lbdef (
               let! eff_body, t = check "let body" g' body in
               check_no_escape [x] t;!
               return (join_eff eff_def eff_body, t)
             )
           )

       ---
       3. TYPE CHECKING ENVIRONMENT

       3.1 Environment Structure

       The full environment is defined in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Env.fsti:165-229:

       and env = {
         solver         :solver_t;                     (* interface to the SMT solver *)
         range          :Range.t;                      (* source location *)
         curmodule      :lident;                       (* Name of this module *)
         gamma          :list binding;                 (* Local typing environment *)
         gamma_sig      :list sig_binding;             (* signature elements *)
         gamma_cache    :SMap.t cached_elt;            (* Memo table *)
         modules        :list modul;                   (* type checked modules *)
         expected_typ   :option (typ & bool);          (* expected type *)
         sigtab         :SMap.t sigelt;                (* long-names to sigelts *)
         attrtab        :SMap.t (list sigelt);         (* attributes to sigelts *)
         instantiate_imp:bool;                         (* instantiate implicits? *)
         effects        :effects;                      (* monad lattice *)
         generalize     :bool;                         (* generalize let bindings? *)
         letrecs        :list (lbname & int & typ & univ_names);  (* recursive names *)
         top_level      :bool;                         (* top-level term? *)
         check_uvars    :bool;                         (* re-typecheck uvars *)
         use_eq_strict  :bool;                         (* use equality not subtyping *)
         is_iface       :bool;                         (* checking an interface? *)
         admit          :bool;                         (* admit VCs *)
         phase1         :bool;                         (* running in phase 1 *)
         failhard       :bool;                         (* don't continue after error *)
         ...
         tc_term :env -> term -> term & lcomp & guard_t;
         typeof_tot_or_gtot_term :env -> term -> must_tot -> term & typ & guard_t;
         universe_of :env -> term -> universe;
         ...
         core_check: core_check_t;
         missing_decl : RBSet.t lident;
       }

       3.2 Core Checker's Internal Environment

       The core checker wraps the main environment with additional state. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:121-126:

       type env = {
          tcenv : Env.env;
          allow_universe_instantiation : bool;
          should_read_cache: bool;
          max_binder_index: int
       }

       3.3 Binder Management

       Fresh binders are created with unique indices to avoid capture. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:139-153:

       let fresh_binder (g:env) (old:binder)
         : env & binder
         = let ctr = g.max_binder_index + 1 in
           let bv = { old.binder_bv with index = ctr } in
           let b = S.mk_binder_with_attrs bv old.binder_qual
                   old.binder_positivity old.binder_attrs in
           push_binder g b, b

       let new_binder (g:env) (t:typ) (r:Range.t)
       : env & binder
       = let bv = wild_bv t r in
         let b = S.mk_binder bv in
         fresh_binder g b

       3.4 Environment Lookup Functions

       The environment provides various lookup functions. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Env.fsti:322-341:

       val lid_exists             : env -> lident -> bool
       val try_lookup_bv          : env -> bv -> option (typ & Range.t)
       val lookup_bv              : env -> bv -> typ & Range.t
       val lookup_qname           : env -> lident -> qninfo
       val lookup_sigelt          : env -> lident -> option sigelt
       val try_lookup_lid         : env -> lident -> option ((universes & typ) & Range.t)
       val try_lookup_and_inst_lid: env -> universes -> lident -> option (typ & Range.t)
       val lookup_lid             : env -> lident -> (universes & typ) & Range.t
       val lookup_univ            : env -> univ_name -> bool
       val try_lookup_val_decl    : env -> lident -> option (tscheme & list qualifier)
       val lookup_val_decl        : env -> lident -> (universes & typ)
       val lookup_datacon         : env -> lident -> universes & typ
       val lookup_and_inst_datacon: env -> universes -> lident -> typ

       ---
       4. GUARD GENERATION AND SOLVING

       4.1 Guard Types

       Guards are formulas that must be proven for type checking to succeed. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Common.fsti:67-69:

       type guard_formula =
         | Trivial
         | NonTrivial of formula

       4.2 Full Guard Structure

       The complete guard includes deferred constraints and implicits. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Common.fsti:154-161:

       type guard_t = {
         guard_f:    guard_formula;
         deferred_to_tac: deferred;  (* problems for tactics *)
         deferred:   deferred;
         univ_ineqs: clist universe & clist univ_ineq;
         implicits:  implicits_t;
       }

       4.3 Guard Generation in Core

       Guards are generated during subtype checking. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:775-792:

       let insert_guard (g:env) (guard:typ)
         : result unit
         = let! cache = get_cache () in
           put_cache {cache with guard_map =
             FStarC.Syntax.Hash.term_map_add guard
               { ge_gamma = g.tcenv.gamma } cache.guard_map }

       let guard (g:env) (guard:typ)
         : result unit
         = match! raw_lookup_guard guard with
           | Some ge ->
             if ge.ge_gamma `context_included` g.tcenv.gamma
             then return () //cache hit
             else (
               insert_guard g guard ;!
               return_with_guard () (Some guard)
             )
           | _ ->
             insert_guard g guard ;!
             return_with_guard () (Some guard)

       4.4 Guard Simplification

       Before returning guards to the caller, they are simplified. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:2181-2188:

       let simplify_steps =
           [Env.Beta;
            Env.UnfoldUntil delta_constant;
            Env.UnfoldQual ["unfold"];
            Env.UnfoldOnly [PC.pure_wp_monotonic_lid; PC.pure_wp_monotonic0_lid];
            Env.Simplify;
            Env.Primops;
            Env.NoFullNorm]

       ---
       5. RELATION CHECKING (EQUALITY AND SUBTYPING)

       5.1 Relation Types

       The checker supports equality and subtyping relations. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:244-251:

       type relation =
         | EQUALITY
         | SUBTYPING : option term -> relation

       let relation_to_string = function
         | EQUALITY -> "=?="
         | SUBTYPING None -> "<:?"
         | SUBTYPING (Some tm) -> Format.fmt1 "( <:? %s)" (show tm)

       5.2 The Main Relation Checker

       check_relation' handles all type comparison cases. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1046-1160:

       let rec check_relation' (g:env) (rel:relation) (t0 t1:typ)
         : result unit
         = let err (lbl:string) =
               match rel with
               | EQUALITY ->
                 fail [
                   parens (text lbl) ^/^ text "not equal terms:"
                   ^/^ pp t0 ^/^ text "<>" ^/^ pp t1
                 ]
               | _ ->
                 fail [
                   parens (text lbl) ^/^ pp t0
                   ^/^ text "is not a subtype of" ^/^ pp t1
                 ]
           in

           let! guard_not_ok = guard_not_allowed in
           let guard_ok = not guard_not_ok in

           (* Head matching for structural comparison *)
           let head_matches t0 t1
             : bool
             = let head0 = U.leftmost_head t0 in
               let head1 = U.leftmost_head t1 in
               match (U.un_uinst head0).n, (U.un_uinst head1).n with
               | Tm_fvar fv0, Tm_fvar fv1 -> fv_eq fv0 fv1
               | Tm_name x0, Tm_name x1 -> bv_eq x0 x1
               | Tm_constant c0, Tm_constant c1 -> equal_term head0 head1
               | Tm_type _, Tm_type _
               | Tm_arrow _, Tm_arrow _
               | Tm_match _, Tm_match _ -> true
               | _ -> false
           in

           (* Beta-iota reduction before comparison *)
           let beta_iota_reduce t =
               let t = Subst.compress t in
               let t = N.normalize [Env.HNF; Env.Weak; Env.Beta;
                                    Env.Iota; Env.Primops] g.tcenv t in
               match t.n with
               | Tm_refine _ -> U.flatten_refinement t
               | _ -> t
           in
           let t0 = Subst.compress (beta_iota_reduce t0) |> U.unlazy_emb in
           let t1 = Subst.compress (beta_iota_reduce t1) |> U.unlazy_emb in

           if equal_term t0 t1 then return ()
           else ...

       5.3 Refinement Type Subtyping

       Refinement types require special handling. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1197-1234:

             | Tm_refine {b=x0; phi=f0}, Tm_refine {b=x1; phi=f1} ->
               if head_matches x0.sort x1.sort
               then (
                 check_relation g EQUALITY x0.sort x1.sort ;!
                 let! u = universe_of_well_typed_term g x0.sort in
                 let g0 = g in
                 let g, b, f0 = open_term g (S.mk_binder x0) f0 in
                 let f1 = Subst.subst [DB(0, b.binder_bv)] f1 in
                   (match! guard_not_allowed with
                    | true ->
                      with_binders g0 [b] [u]
                        (check_relation g EQUALITY f0 f1)

                    | _ ->
                      match rel with
                      | EQUALITY ->
                        with_binders g0 [b] [u]
                          (handle_with
                             (check_relation g EQUALITY f0 f1)
                             (fun _ -> guard g (U.mk_iff f0 f1)))

                      | SUBTYPING (Some tm) ->
                        guard g0 (Subst.subst [NT(b.binder_bv, tm)]
                                 (U.mk_imp f0 f1))

                      | SUBTYPING None ->
                        guard g0 (U.mk_forall u b.binder_bv
                                 (U.mk_imp f0 f1)))
               )

       5.4 Arrow Subtyping

       Arrow types use contravariant argument checking. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1359-1386:

             | Tm_arrow {bs=[x0]; comp=c0}, Tm_arrow {bs=[x1]; comp=c1} ->
               with_context "subtype arrow" None (fun _ ->
                 let! _ = check_bqual x0.binder_qual x1.binder_qual in
                 check_positivity_qual rel x0.binder_positivity x1.binder_positivity;!
                 let! u1 = universe_of_well_typed_term g x1.binder_bv.sort in
                 let g_x1, x1, c1 = open_comp g x1 c1 in
                 let c0 = Subst.subst_comp [DB(0, x1.binder_bv)] c0 in
                 with_binders g [x1] [u1] (
                   let rel_arg =
                     match rel with
                     | EQUALITY -> EQUALITY
                     | _ -> SUBTYPING (Some (S.bv_to_name x1.binder_bv))
                   in
                   (* Contravariant in argument position *)
                   check_relation g rel_arg x1.binder_bv.sort x0.binder_bv.sort ;!
                   with_context "check_subcomp" None (fun _ ->
                     check_relation_comp g_x1 rel_comp c0 c1
                   )
                 )
               )

       ---
       6. CACHING MECHANISM

       6.1 Two-Level Cache Architecture

       The core checker uses a sophisticated two-level caching system. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:34-81:

       1. Functional cache: cache_t.term_map and cache_t.guard_map

          These caches are initialized to empty at each call into the public API.
          The call to check_term populates the caches as it checks a term and 
          returns guard to the caller. 

          Main invariant: the provability of the returned guard implies the
          provability of all cached guards in the guard_map; and, consequently,
          the typing of all terms in the term_map.

       2. Second level cache (imperative):
          Accumulates entries across multiple calls to this Core checker. 
          Every entry contains guards that have already been proven.
          Cleared explicitly by calling clear_memo_table at each top-level 
          declaration.

       6.2 Cache Data Structures

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:324-348:

       type hash_entry = {
          he_term:term;
          he_gamma:list binding;
          he_eff: tot_or_ghost;
          he_typ: typ
       }

       type guard_entry = {
         ge_gamma: list binding
       }

       type cache_t = {
         term_map : FStarC.Syntax.Hash.term_map hash_entry;
         guard_map : FStarC.Syntax.Hash.term_map guard_entry;
       }

       module THT = FStarC.Syntax.TermHashTable
       type tc_table = {
         table:THT.hashtable hash_entry;
         guard_table:THT.hashtable guard_entry;
         counter:ref int //version counter
       }

       6.3 Cache Lookup and Insertion

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:852-879:

       let lookup (g:env) (e:term) : result (tot_or_ghost & typ) =
         match! raw_lookup e with
         | None ->
           record_cache_miss ();
           fail_str "not in cache"
         | Some he ->
            if he.he_gamma `context_included` g.tcenv.gamma
            && not !dbg_DisableCoreCache
            then (
              record_cache_hit();
              (* Replace use ranges in cached type with current term's range *)
              let ty = replace_all_use_ranges (pos e) he.he_typ in
              return (he.he_eff, ty)
            )
            else (
              fail_str "not in cache"
            )

       6.4 Guard Commit Protocol

       When guards are proven, the cache is promoted. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:396-416:

       let commit_guard_core (g:guard_commit_token) : unit =
         if g.guard_counter <> !table.counter
         then () //table has been cleared since token was issued
         else (
           let cache = !g.guard_cache in
           match cache with
           | None -> ()
           | Some cache ->
             g.guard_cache := None; //invalidate
             FStarC.Syntax.Hash.term_map_fold
               (fun term hash_entry _ -> THT.insert term hash_entry table.table)
               cache.term_map
               ();
             FStarC.Syntax.Hash.term_map_fold
               (fun term guard_entry _ -> THT.insert term guard_entry table.guard_table)
               cache.guard_map
               ()
         )

       ---
       7. TYPE GENERALIZATION

       7.1 Universe Generalization

       Universe variables are generalized at let bindings. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Generalize.fst:49-65:

       let gen_univs env (x:FlatSet.t universe_uvar) : list univ_name =
           if is_empty x then []
           else let s = diff x (Env.univ_vars env) |> elems in
                let r = Some (Env.get_range env) in
                let u_names = s |> List.map (fun u ->
                  let u_name = Syntax.new_univ_name r in
                  if !dbg_Gen then
                   Format.print3 "Setting ?%s (%s) to %s\n"
                       (show <| UF.univ_uvar_id u)
                       (show (U_unif u))
                       (show (U_name u_name));
                  UF.univ_change u (U_name u_name);
                  u_name)
                in
                u_names

       7.2 Type Variable Generalization

       Type unification variables of kind Type are generalized. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Generalize.fst:183-220:

            let gen_types (uvs:list ctx_uvar) : list (bv & bqual) =
                uvs |> List.concatMap (fun u ->
                (* Don't generalize if has meta *)
                if Some? u.ctx_uvar_meta then [] else

                match UF.find u.ctx_uvar_head with
                | Some _ -> failwith "Unexpected instantiation"
                | _ ->
                  let k = N.normalize [Env.Beta; Env.Exclude Env.Zeta] env
                          (U.ctx_uvar_typ u) in
                  let bs, kres = U.arrow_formals k in
                  (* Only generalize variables at type k = a:Type{phi}
                     where k is closed *)
                  match (U.unrefine (N.unfold_whnf env kres)).n with
                  | Tm_type _ ->
                     let free = FStarC.Syntax.Free.names kres in
                     if not (is_empty free) then []
                     else
                     let a = S.new_bv (Some <| Env.get_range env) kres in
                     let t =
                         match bs with
                         | [] -> S.bv_to_name a
                         | _ -> U.abs bs (S.bv_to_name a)
                                (Some (U.residual_tot kres))
                     in
                     U.set_uvar u.ctx_uvar_head t;
                     [a, S.as_bqual_implicit true]

                  | _ -> []
                )

       7.3 Mutual Recursion Constraints

       Mutually recursive definitions must have compatible universes. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Generalize.fst:143-168:

            let force_univs_eq lec2 u1 u2 =
               if equal u1 u2
               then ()
               else let lb1, _, _ = lec_hd in
                    let lb2, _, _ = lec2 in
                    let msg = Format.fmt4 "Generalizing mutually recursive definitions \
                       requires incompatible set of universes for %s %s and %s %s"
                       (show lb1) (show u1) (show lb2) (show u2) in
                    raise_error env Errors.Fatal_IncompatibleSetOfUniverse msg

       ---
       8. QUALIFIER CHECKING

       8.1 Qualifier Compatibility

       Qualifiers on declarations must be compatible. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Quals.fst:85-127:

           let qual_compat q1 q2 =
             match q1 with
             | Assumption ->
               q2=Logic || inferred q2 || visibility q2 || assumption q2
               || (env.is_iface && q2=Inline_for_extraction) || q2=NoExtract

             | New ->
               inferred q2 || visibility q2 || assumption q2 ||
               q2=Inline_for_extraction || q2=NoExtract

             | Inline_for_extraction ->
                q2=Logic || visibility q2 || reducibility q2 ||
                reification q2 || inferred q2 || has_eq q2 ||
                (env.is_iface && q2=Assumption) || q2=NoExtract || q2=New

             | Unfold_for_unification_and_vcgen
             | Visible_default | Irreducible | Noeq | Unopteq ->
               q2=Logic || q2=Inline_for_extraction || q2=NoExtract ||
               has_eq q2 || inferred q2 || visibility q2 || reification q2

             | TotalEffect ->
               inferred q2 || visibility q2 || reification q2

             | Logic ->
               q2=Assumption || inferred q2 || visibility q2 || reducibility q2

             | Reifiable | Reflectable _ ->
               reification q2 || inferred q2 || visibility q2 ||
               q2=TotalEffect || q2=Visible_default

             | Private -> true
             | _ -> true

       8.2 Erasable Attribute Checking

       The erasable attribute has specific requirements. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Quals.fst:226-262:

       let check_erasable env quals (r:Range.t) se =
         ...
         if se_has_erasable_attr
         then begin
           match se.sigel with
           | Sig_bundle _ ->
             if not (quals |> BU.for_some (function Noeq -> true | _ -> false))
             then raise_error r Errors.Fatal_QulifierListNotPermitted [
                     text "Incompatible attributes and qualifiers: \
                      erasable types do not support decidable equality"
                    ]
           | Sig_let {lbs=(false, [lb])} ->
             let _, body, _ = U.abs_formals lb.lbdef in
             if not (N.non_info_norm env body)
             then raise_error body Errors.Fatal_QulifierListNotPermitted [
                     text "Illegal attribute: erasable only on non-informative types.";
                     text "The term" ^/^ pp body ^/^ text "is informative.";
                    ]
           ...
         end

       ---
       9. ERROR HANDLING

       9.1 Error Context

       Errors carry context information for better messages. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:266-306:

       type context = {
         no_guard : bool;
         unfolding_ok : bool;
         error_context: list (string & option context_term)
       }

       let print_context (ctx:context)
         : string =
         let rec aux (depth:string) (ctx:_) =
           match ctx with
           | [] -> ""
           | (msg, ctx_term)::tl ->
             let hd =
               Format.fmt3 "%s %s (%s)\n" depth msg
                 (match ctx_term with
                  | None -> ""
                  | Some ctx_term -> context_term_to_string ctx_term)
             in
             let tl = aux (depth ^ ">") tl in
             hd ^ tl
         in
         aux "" (List.rev ctx.error_context)

       9.2 Error Type

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:308-318:

       let error = context & Errors.error_message

       let print_error (err:error) =
         let ctx, msg = err in
         Format.fmt2 "%s%s" (print_context ctx) (Errors.Msg.rendermsg msg)

       let print_error_short (err:error) =
         let _, msg = err in
         Errors.Msg.rendermsg msg

       9.3 Error Message Formatting

       The Err module provides rich error formatting. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Err.fst:176-183:

       let subtyping_failed : env -> typ -> typ -> unit -> error_message =
            fun env t1 t2 () ->
             let ppt = N.term_to_doc env in
              [text "Subtyping check failed";
               prefix 2 1 (text "Expected type") (ppt t2) ^/^
               prefix 2 1 (text "got type") (ppt t1);
              ]

       9.4 Type Discrepancy Printing

       The error module attempts to show minimal differences. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Err.fst:48-120:

       (* Will attempt to enable certain printing flags to make x and y
        * visibly different. It will try to enable the least possible
        * subset of implicits, universes, effect_args and full_names. *)
       let print_discrepancy (#a:Type) (#b:eqtype) (f : a -> b) (x : a) (y : a) : b & b =
           let print () : b & b & bool =
               let xs = f x in
               let ys = f y in
               xs, ys, xs <> ys
           in
           ...
           let get () : list bool =
               let pi  = get_bool_option "print_implicits" in
               let pu  = get_bool_option "print_universes" in
               let pea = get_bool_option "print_effect_args" in
               let pf  = get_bool_option "print_full_names" in
               [pi; pu; pea; pf]
           in
           ...

       ---
       10. SMT SOLVER INTERACTION

       10.1 Solver Interface

       The environment includes a solver interface. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Env.fsti:231-245:

       and solver_t = {
           init            :env -> unit;
           snapshot        :string -> (solver_depth_t & unit);
           rollback        :string -> option solver_depth_t -> unit;
           encode_sig      :env -> sigelt -> unit;
           preprocess      :env -> goal -> bool & list (env & goal & optionstate);
           spinoff_strictly_positive_goals: option (env -> goal -> list (env & goal));
           handle_smt_goal :env -> goal -> list (env & goal);
           solve           :option (unit -> string) -> env -> goal -> unit;
           solve_sync      :option (unit -> string) -> env -> goal -> bool;
           finish          :unit -> unit;
           refresh         :option proof_namespace -> unit;
       }

       10.2 Core Check Callback

       The core checker is invoked as a callback. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Env.fsti:249-250:

       and core_check_t =
         env -> term -> typ -> bool -> either (option (typ & (unit -> unit))) (bool -> string)

       10.3 Guard Discharge Flow

       1. Core checker generates guards during type checking
       2. Guards are simplified using normalization
       3. Simplified guards are sent to SMT solver
       4. On successful proof, commit_guard is called
       5. Cache entries are promoted to permanent cache

       ---
       11. PATTERN MATCHING

       11.1 Pattern Type Checking

       Patterns are checked against the scrutinee type. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:1943-2010:

       and check_pat (g:env) (p:pat) (t_sc:typ) : result (binders & universes) =
         let unrefine_tsc t_sc =
           t_sc |> N.normalize_refinement N.whnf_steps g.tcenv
                |> U.unrefine in

         match p.v with
         | Pat_constant c ->
           let e = ... in
           let! _, t_const = check "pat_const" g e in
           let! _ = with_context "check_pat constant" None
                    (fun () -> check_subtype g (Some e) t_const (unrefine_tsc t_sc)) in
           return ([], [])

         | Pat_var bv ->
           let b = S.mk_binder {bv with sort=t_sc} in
           let! [u] = with_context "check_pat_binder" None
                      (fun _ -> check_binders g [b]) in
           return ([b], [u])

         | Pat_cons (fv, usopt, pats) ->
           let us = if None? usopt then [] else usopt |> Option.must in
           let formals, t_pat =
             Env.lookup_and_inst_datacon g.tcenv us (S.lid_of_fv fv)
             |> U.arrow_formals in
           ...

       11.2 Branch Condition Generation

       The checker generates conditions for pattern coverage. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:2065-2132:

       and pattern_branch_condition (g:env) (scrutinee:term) (pat:pat)
         : result (option term)
         = match pat.v with
           | Pat_var _ -> return None
           | Pat_constant c ->
             let const_exp = ... in
             let! _, t_const = check "constant pattern" g const_exp in
             return (Some (U.mk_decidable_eq t_const scrutinee const_exp))

           | Pat_cons(fv, us_opt, sub_pats) ->
             let discrimination =
               let is_induc, datacons = Env.datacons_of_typ g.tcenv
                                        (Env.typ_of_datacon g.tcenv fv.fv_name) in
               if not is_induc || List.length datacons > 1
               then let discriminator = U.mk_discriminator fv.fv_name in
                    match Env.try_lookup_lid g.tcenv discriminator with
                    | None -> None
                    | _ -> Some (mk_head_discriminator())
               else None
             in
             ...

       ---
       12. PUBLIC API

       12.1 Main Entry Points

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:2276-2291:

       let check_term g e t must_tot =
         match check_term_top g e (Some t) must_tot with
         | Success ((_, g), cache) -> Inl <| return_my_guard_and_tok_t g cache
         | Error err -> Inr err

       let check_term_at_type g e t =
         let must_tot = false in
         match check_term_top g e (Some t) must_tot with
         | Success (((eff, _), g), cache) -> Inl (eff, return_my_guard_and_tok_t g cache)
         | Error err -> Inr err

       let compute_term_type g e =
         let must_tot = false in
         match check_term_top g e None must_tot with
         | Success (((eff, ty), g), cache) -> Inl (eff, ty, return_my_guard_and_tok_t g cache)
         | Error err -> Inr err

       12.2 Equality and Subtyping Checks

       From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Core.fst:2303-2324:

       let check_term_equality guard_ok unfolding_ok g t0 t1
         = let g = initial_env g in
           let ctx = { unfolding_ok = unfolding_ok; 
                       no_guard = not guard_ok; 
                       error_context = [("Eq", None)] } in
           let r = check_relation g EQUALITY t0 t1 ctx initial_cache in
           match r with
           | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
           | Error err -> Inr err

       let check_term_subtyping guard_ok unfolding_ok g t0 t1
         = let g = initial_env g in
           let ctx = { unfolding_ok = unfolding_ok; 
                       no_guard = not guard_ok; 
                       error_context = [("Subtyping", None)] } in
           match check_relation g (SUBTYPING None) t0 t1 ctx initial_cache with
           | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
           | Error err -> Inr err

       ---
       13. KEY DESIGN PATTERNS

       13.1 Monadic Result Type

       The checker uses a custom monadic result type for threading context and cache:

       type __result a =
         | Success of a & cache_t
         | Error of error

       type result a = context -> cache_t -> __result (success a)

       13.2 With-Context Pattern

       Errors are contextualized using with_context:

       let with_context (#a:Type) (msg:string) (t:option context_term) (x:unit -> result a)
         : result a
         = fun ctx cache ->
            let ctx = { ctx with error_context=((msg,t)::ctx.error_context) } in
            x () ctx cache

       13.3 Guard Scoping

       Guards are scoped using with_binders:

       let with_binders (#a:Type) (initial_env:env) (xs:binders) (us:universes) (f:result a)
         : result a
         = with_guard f
           (function
             | Inr err -> fail_propagate err
             | Inl (res, None) -> return res
             | Inl (res, Some form) ->
               let form = mk_forall_l us xs form in
               guard initial_env form ;!
               return res)

       ---
       SUMMARY

       The F* type checker core implements a sophisticated bidirectional type checking algorithm with:

       1. Bidirectional checking: Synthesis and checking modes for efficient type inference
       2. Two-level caching: Functional caches promoted to permanent storage after guard proof
       3. Guard generation: Preconditions generated during subtyping that must be proven
       4. SMT integration: Guards discharged via SMT solver interaction
       5. Rich error context: Errors carry full checking context for debugging
       6. ML-style generalization: Universe and type variable generalization at let bindings
       7. Qualifier checking: Compatibility validation between declaration qualifiers

       The architecture cleanly separates:
       - Core.fst: Pure/ghost term checking with caching
       - Env.fst: Environment management and lookups
       - Common.fst: Shared types (guards, problems, identifier info)
       - Err.fst: Error message formatting
       - Generalize.fst: Type generalization
       - Quals.fst: Qualifier inference and checking
  ⎿  Done (16 tool uses · 154.3k tokens · 4m 7s)

● elite-bug-hunter(F* Ch6: Subtyping & Rel)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering SUBTYPING AND TYPE RELATIONS (Rel.fst).

       Explore /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Rel.fst (237KB - largest file!) extensively.

       Focus on:
       1. Read the entire Rel.fst file - document the subtyping algorithm
       2. Understand type equivalence checking
       3. Understand subtype constraints
       4. Understand unification
       5. Understand deferred constraints and their resolution

       Your chapter should include:
       - The worklist algorithm for constraint solving
       - How refinement types are compared
       - Flex-rigid unification
       - Universe constraints
       - Effect subtyping
       - Guard conditions generation
       - Interaction with normalization
       - When/why constraints are deferred
       - Debugging subtyping failures

       This is the MOST COMPLEX file in F*. Read it thoroughly and document every major function. Write the chapter as detailed documentation (6000+ words) directly in your response.
  ⎿  Response:
       Now I have a comprehensive understanding of the Rel.fst file. Let me write the detailed documentation chapter.

       ---
       F* Subtyping and Type Relations: A Comprehensive Guide to Rel.fst

       Introduction and Overview

       The file /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Rel.fst is the largest and most complex file in the F* typechecker at approximately 237KB and 5,770 lines. It implements F*'s refinement subtyping algorithm with higher-order unification, featuring
       special treatment for higher-order patterns. This module is the heart of F*'s type inference and checking system, responsible for determining when one type can be used where another is expected.

       The fundamental purpose of Rel.fst is to solve two classes of problems:

       1. Type Equality Problems (EQ): Determining if two types are definitionally equal
       2. Subtyping Problems (SUB/SUBINV): Determining if one type is a subtype of another

       The module uses a sophisticated constraint-solving approach based on a worklist algorithm, where constraints are processed iteratively, generating new sub-constraints and instantiating unification variables until either all constraints are satisfied or the solver gives
       up.

       ---
       Core Data Structures

       The Worklist

       The central data structure is the worklist type, which maintains the state of the constraint solver:

       type worklist = {
           attempting:   probs;                    // Problems currently being solved
           wl_deferred:  clist (int & deferred_reason & lstring & prob);  // Deferred problems
           wl_deferred_to_tac: clist (int & deferred_reason & lstring & prob);  // Problems for tactics
           ctr:          int;                      // Counter incremented on each substitution extension
           defer_ok:     defer_ok_t;               // Whether deferring is allowed
           smt_ok:       bool;                     // Whether SMT fallback is permitted
           umax_heuristic_ok: bool;                // Whether umax structural matching is allowed
           tcenv:        Env.env;                  // Top-level environment
           wl_implicits: implicits_t;              // Introduced unification variables
           repr_subcomp_allowed: bool;             // Whether effect subtyping with repr is allowed
           typeclass_variables: RBSet.t ctx_uvar   // Variables for typeclass resolution
       }

       The defer_ok field controls when constraints can be deferred:

       type defer_ok_t =
         | NoDefer            // Never defer - must solve now
         | DeferAny           // Can defer any constraint
         | DeferFlexFlexOnly  // Only defer flex-flex constraints

       Problems

       A problem represents a single constraint to be solved:

       type problem 'a = {
           pid:           int;              // Unique identifier
           lhs:           'a;               // Left-hand side
           relation:      rel;              // EQ, SUB, or SUBINV
           rhs:           'a;               // Right-hand side
           element:       option bv;        // Witness variable for subtyping
           logical_guard: term;             // Guard condition
           logical_guard_uvar: ctx_uvar;    // Uvar for the guard
           reason:        list string;      // Why this problem was created
           loc:           Range.range;      // Source location
           rank:          option rank_t;    // Problem difficulty ranking
           logical:       bool;             // Whether this is a logical context
       }

       The rel type captures the three possible relations:
       - EQ: Type equality (t1 = t2)
       - SUB: Subtyping (t1 <: t2)
       - SUBINV: Inverse subtyping (t1 :> t2, equivalent to t2 <: t1)

       Flex Terms

       A "flex" term is one headed by a unification variable. The flex_t type captures this:

       type flex_t = Flex of (term & ctx_uvar & args)

       This represents a term of the form ?u e1 ... en where ?u is a unification variable applied to arguments e1 ... en.

       Unification Variable Instantiations

       type uvi =
           | TERM of ctx_uvar & term      // Term-level instantiation
           | UNIV of S.universe_uvar & universe  // Universe-level instantiation

       Solutions

       The solver returns either success with deferred constraints and implicits, or failure with a problematic constraint and error message:

       type solution =
         | Success of deferred & deferred & implicits_t
         | Failed  of prob & lstring

       ---
       The Worklist Algorithm

       Main Solving Loop

       The main entry point is the solve function, which processes problems from the worklist until completion:

       let rec solve (probs: worklist) : solution =
           match next_prob probs with
           | Some (hd, tl, rank) ->
             let probs = {probs with attempting=tl} in
             begin match hd with
             | CProb cp -> solve_c (maybe_invert cp) probs
             | TProb tp ->
               if BU.physical_equality tp.lhs tp.rhs
               then solve (solve_prob hd None [] probs)
               else (* ... complex case analysis ... *)
             end
           | None ->
             (* No more problems to attempt *)
             match view probs.wl_deferred with
             | VNil -> Success (empty, as_deferred probs.wl_deferred_to_tac, probs.wl_implicits)
             | VCons _ _ ->
               (* Try to make progress on deferred problems *)
               let attempt, rest = probs.wl_deferred |> CList.partition
                                     (fun (c, _, _, _) -> c < probs.ctr) in
               match view attempt with
               | VNil -> Success (as_deferred probs.wl_deferred, ...)
               | _ -> solve ({probs with attempting=...; wl_deferred=rest})

       The algorithm works as follows:

       1. Select the next problem using next_prob, which returns the problem with the lowest rank
       2. Solve the problem based on its type (term or computation)
       3. If no problems remain, check deferred problems
       4. Deferred problems are re-attempted when the counter has increased (indicating progress was made)
       5. Repeat until success or failure

       Problem Ranking

       Problems are ranked to prioritize easier constraints first:

       let rank_t_num = function
           | Rigid_rigid -> 0         // Both sides are concrete types
           | Flex_rigid_eq -> 1       // Uvar = concrete (equality)
           | Flex_flex_pattern_eq -> 2 // Two pattern uvars (equality)
           | Flex_rigid -> 3          // Uvar <: concrete
           | Rigid_flex -> 4          // Concrete <: uvar
           | Flex_flex -> 5           // Both sides are uvars

       Lower ranks are prioritized because:
       - Rigid-rigid problems can be solved immediately by structural decomposition
       - Flex-rigid equality problems have a unique solution
       - Flex-flex problems are deferred as long as possible since they may have multiple solutions

       ---
       Type Equality and Subtyping

       The solve_t' Function

       The main term-level solver solve_t' handles all type equality and subtyping problems through an extensive case analysis on the structure of the LHS and RHS:

       and solve_t' (problem:tprob) (wl:worklist) : solution =
           let t1 = problem.lhs in
           let t2 = problem.rhs in
           match t1.n, t2.n with
           | Tm_delayed _, _ | _, Tm_delayed _ ->
               failwith "Impossible: terms were not compressed"
           
           | Tm_ascribed _, _ -> solve_t' ({problem with lhs=U.unascribe t1}) wl
           | Tm_meta _, _ -> solve_t' ({problem with lhs=U.unmeta t1}) wl
           
           | Tm_type u1, Tm_type u2 ->
               solve_one_universe_eq orig u1 u2 wl

           | Tm_arrow {bs=bs1; comp=c1}, Tm_arrow {bs=bs2; comp=c2} ->
               solve_binders bs1 bs2 orig wl (fun wl scope subst -> ...)

           | Tm_refine {b=x1; phi=phi1}, Tm_refine {b=x2; phi=phi2} ->
               (* Complex refinement comparison *)

           | Tm_uvar _, Tm_uvar _ -> (* flex-flex *)
           | Tm_uvar _, _ when problem.relation=EQ -> (* flex-rigid eq *)
           | _, Tm_uvar _ when problem.relation=EQ -> (* rigid-flex eq *)

           (* ... many more cases ... *)

       Refinement Type Comparison

       Refinement types are compared by:

       1. Comparing base types with the same relation
       2. Comparing refinement formulas with equality (for EQ) or implication (for SUB)

       | Tm_refine {b=x1; phi=phi1}, Tm_refine {b=x2; phi=phi2} ->
           let base_prob, wl = mk_t_problem wl [] orig x1.sort problem.relation x2.sort ... in
           let x1 = freshen_bv x1 in
           let phi1 = Subst.subst [DB(0, x1)] phi1 in
           let phi2 = Subst.subst [DB(0, x1)] phi2 in

           if problem.relation = EQ
           then (* try phi1 <=> phi2 *)
           else (* try phi1 => phi2 for SUB, phi2 => phi1 for SUBINV *)

       The solver first attempts to solve refinement formulas syntactically. If that fails and SMT is enabled, it falls back to generating an SMT guard.

       Arrow Type Comparison

       Arrow types are compared contravariantly in their domain and covariantly in their codomain:

       | Tm_arrow {bs=bs1; comp=c1}, Tm_arrow {bs=bs2; comp=c2} ->
           let (bs1, c1), (bs2, c2) = match_num_binders (bs1, mk_c c1) (bs2, mk_c c2) in
           solve_binders bs1 bs2 orig wl
               (fun wl scope subst ->
                   let c1 = Subst.subst_comp subst c1 in
                   let c2 = Subst.subst_comp subst c2 in
                   mk_c_problem wl scope orig c1 rel c2 None "function co-domain")

       The solve_binders function compares binder lists with contravariant relation:

       and solve_binders (bs1:binders) (bs2:binders) (orig:prob) (wl:worklist)
                         (rhs:worklist -> binders -> list subst_elt -> (prob & worklist)) : solution =
          let rec aux wl scope subst xs ys =
               match xs, ys with
               | [], [] -> rhs wl scope subst
               | x::xs, y::ys when eq_bqual x.binder_qual y.binder_qual ->
                  let prob, wl = mk_t_problem wl scope orig
                                   hd1.sort (invert_rel <| p_rel orig) hd2.sort ...
                  (* Continue with remaining binders *)

       ---
       Flex-Rigid Unification

       Pattern Unification

       The ideal case for flex-rigid unification is when the flex term is a pattern - a unification variable applied to distinct bound variables:

       let pat_vars env ctx args : option binders =
           let rec aux seen args =
             match args with
             | [] -> Some (List.rev seen)
             | (arg, i)::args ->
               let hd = sn env arg in
               match hd.n with
               | Tm_name a ->
                 if name_exists_in_binders a seen || name_exists_in_binders a ctx
                 then None  // Not a pattern - variable appears twice
                 else aux ((S.mk_binder a ...)::seen) args
               | _ -> None  // Not a pattern - argument is not a variable
           in aux [] args

       When the LHS is a pattern ?u x1 ... xn and the free variables of the RHS are contained in the context of ?u plus {x1, ..., xn}, we can directly solve:

       | Some lhs_binders -> // It's a pattern
           let fvs1 = binders_as_bv_set (ctx_uv.ctx_uvar_binders @ lhs_binders) in
           let fvs2 = Free.names rhs in
           if subset fvs2 fvs1
           then let sol = mk_solution env lhs lhs_binders rhs in
                let wl = restrict_all_uvars env ctx_uv lhs_binders uvars wl in
                solve (solve_prob orig None sol wl)

       Quasi-Pattern Unification

       When the flex term is not a pattern but close to one, the solver attempts quasi-pattern unification:

       let quasi_pattern env (f:flex_t) : option (binders & typ) =
           let (Flex (_, ctx_uvar, args)) = f in
           let t_hd = U.ctx_uvar_typ ctx_uvar in
           let ctx = ctx_uvar.ctx_uvar_binders in
           let rec aux pat_binders formals t_res args =
               match formals, args with
               | [], [] -> Some (List.rev pat_binders, U.arrow formals (S.mk_Total t_res))
               | fml::formals, (a, a_imp)::args ->
                   match (SS.compress a).n with
                   | Tm_name x ->
                       if name_exists_in x ctx || name_exists_in x pat_binders
                       then aux (fml :: pat_binders) formals t_res args  // Skip duplicate
                       else (* Include x in pattern *)
                   | _ -> aux (fml :: pat_binders) formals t_res args  // Non-variable arg
               | [], args -> (* Need to unfold return type *)

       Quasi-patterns allow solving cases where some arguments are not variables, by treating those positions as extra parameters in the solution.

       First-Order Heuristic

       The try_first_order function attempts to solve flex-rigid problems by directly matching head symbols:

       let try_first_order orig env wl lhs rhs =
           let (Flex (_t1, ctx_uv, args_lhs)) = lhs in
           let head, args_rhs = U.head_and_args rhs in

           (* Check if head has the right type *)
           if n_args_lhs > n_args_rhs then Inl "not enough args"
           else
             let i = n_args_rhs - n_args_lhs in
             let prefix, args_rhs = List.splitAt i args_rhs in
             let head = S.mk_Tm_app head prefix head.pos in

             (* Verify head type matches uvar type *)
             if TEQ.eq_tm env t_head (U.ctx_uvar_typ ctx_uv) = TEQ.Equal
             then (* Set ?u := head and create subproblems for arguments *)

       Imitation

       When patterns fail, the solver uses imitation for applications and arrows:

       let imitate (orig:prob) (env:Env.env) (wl:worklist) (lhs:flex_t) (rhs:term) =
           match quasi_pattern env lhs with
           | None -> giveup_or_defer orig wl Deferred_first_order_heuristic_failed msg
           | Some (bs_lhs, t_res_lhs) ->
             if is_app rhs then imitate_app orig env wl lhs bs_lhs t_res_lhs rhs
             else if is_arrow rhs then imitate_arrow orig wl lhs bs_lhs t_res_lhs EQ rhs

       For arrow imitation:

       and imitate_arrow (orig:prob) (wl:worklist) (lhs:flex_t) (bs_lhs:binders) (t_res_lhs:term)
                         (rel:rel) (arrow:term) : solution =
           let (Flex (_, u_lhs, _)) = lhs in
           let formals, c = U.arrow_formals_comp arrow in
           let rec aux (bs:binders) (formals:binders) wl =
               match formals with
               | [] ->
                 let c', wl = imitate_comp bs c wl in
                 let lhs' = U.arrow bs c' in
                 let sol = TERM (u_lhs, U.abs bs_lhs lhs' ...) in
                 (* Create subproblem: lhs' ~ arrow *)

       ---
       Flex-Flex Unification

       Flex-flex constraints involve two unification variables and are the most delicate to handle. The solver tries to defer them as long as possible:

       and solve_t_flex_flex env orig wl (lhs:flex_t) (rhs:flex_t) : solution =
           match p_rel orig with
           | SUB | SUBINV ->
             if wl.defer_ok = DeferAny
             then giveup_or_defer_flex_flex orig wl Deferred_flex msg
             else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs

           | EQ ->
             if wl.defer_ok <> NoDefer && (not (is_flex_pat lhs) || not (is_flex_pat rhs))
             then giveup_or_defer_flex_flex orig wl Deferred_flex_flex_nonpattern msg
             else (* Must solve now *)

       When forced to solve, the algorithm creates a new "meet" variable:

       (* Given: ?u (y1..ym) ~ ?v (y1'..ym')
          Create: ctx_w |- ?w : z1..zk -> tres
          where zs = intersection of visible variables
          Solve: ?u := fun y1..ym -> ?w z1...zk
                 ?v := fun y1'..ym' -> ?w z1...zk *)
       let ctx_w, _ = maximal_prefix u_lhs.ctx_uvar_binders u_rhs.ctx_uvar_binders in
       let zs = intersect_binders gamma_w (ctx_l @ binders_lhs) (ctx_r @ binders_rhs) in
       let new_uvar_typ = U.arrow zs (S.mk_Total t_res_lhs) in
       let _, w, wl = new_uvar "flex-flex quasi" wl range gamma_w ctx_w new_uvar_typ ... in
       let w_app = S.mk_Tm_app w (List.map (fun z -> S.as_arg (S.bv_to_name z)) zs) w.pos in
       let s1 = TERM(u_lhs, U.abs binders_lhs w_app ...) in
       let s2 = TERM(u_rhs, U.abs binders_rhs w_app ...) in

       ---
       Universe Constraints

       Universe Equality

       Universe constraints are solved recursively:

       let rec solve_universe_eq pid_orig wl u1 u2 =
           let u1 = N.normalize_universe wl.tcenv u1 in
           let u2 = N.normalize_universe wl.tcenv u2 in
           match u1, u2 with
           | U_name x, U_name y ->
             if (string_of_id x) = (string_of_id y) then USolved wl
             else ufailed_simple "Incompatible universes"

           | U_zero, U_zero -> USolved wl

           | U_succ u1, U_succ u2 -> solve_universe_eq pid_orig wl u1 u2

           | U_unif v1, U_unif v2 ->
             if UF.univ_equiv v1 v2 then USolved wl
             else let wl = extend_universe_solution pid_orig [UNIV(v1, u2)] wl in USolved wl

           | U_unif v1, u | u, U_unif v1 ->
             if occurs_univ v1 u
             then try_umax_components u1 u2 "Failed occurs check"
             else USolved (extend_universe_solution pid_orig [UNIV(v1, u)] wl)

           | U_max _, _ | _, U_max _ ->
             if wl.defer_ok = DeferAny then UDeferred wl
             else (* Try structural matching *)

       Universe Inequalities

       Universe inequalities arise from inductive type definitions and are solved after all other constraints:

       let solve_universe_inequalities' tx env (variables, ineqs) : unit =
          (* For each universe variable ?u:
             1. Collect lower bounds from inequalities
             2. Set ?u to max(lower_bounds)
             3. Verify all inequalities are satisfied *)
          let sols = variables |> CList.collect (fun v ->
            match SS.compress_univ v with
            | U_unif _ ->
                let lower_bounds = ineqs |> CList.collect (fun (u, v') ->
                  if equiv v v' && not (variables |> CList.existsb (equiv u))
                  then cons u empty
                  else empty)
                in
                let lb = N.normalize_universe env (U_max (to_list lower_bounds)) in
                singleton (lb, v)
            | _ -> empty)

       ---
       Effect Subtyping

       Computation Type Problems

       The solve_c function handles computation type constraints:

       and solve_c (problem:problem comp) (wl:worklist) : solution =
           let c1 = problem.lhs in
           let c2 = problem.rhs in
           
           match c1.n, c2.n with
           | Total t1, Total t2 | GTotal t1, GTotal t2 ->
             solve_t (problem_using_guard orig t1 problem.relation t2 ...) wl

           | Total t1, GTotal t2 when problem.relation = SUB ->
             solve_t (problem_using_guard orig t1 problem.relation t2 ...) wl

           | Comp _, Comp _ ->
             if problem.relation = EQ
             then solve_eq c1_comp c2_comp Env.trivial_guard
             else if Env.is_layered_effect env c2.effect_name
             then solve_layered_sub c1 c2
             else match Env.monad_leq env c1.effect_name c2.effect_name with
                  | None -> giveup wl msg orig
                  | Some edge -> solve_sub c1 edge c2

       Layered Effect Subtyping

       For indexed effects, subtyping uses the effect's subcomp combinator:

       let solve_layered_sub c1 c2 =
           let lift_c1 (edge:edge) =
             c1 |> S.mk_Comp |> edge.mlift.mlift_wp env
                |> (fun (c, g) -> Env.comp_to_comp_typ env c, g) in

           (* Find subcomp combinator *)
           let c1, g_lift, stronger_t_opt, kind, ... =
             match Env.exists_polymonadic_subcomp env c1.effect_name c2.effect_name with
             | None -> (* Try lifting via monad_leq *)
             | Some (t, kind) -> (* Use polymonadic subcomp *)

           (* Apply the subcomp combinator *)
           let fml, sub_probs, wl =
             if kind = Ad_hoc_combinator
             then apply_ad_hoc_indexed_subcomp env bs subcomp_c c1 c2 ...
             else apply_substitutive_indexed_subcomp env kind bs subcomp_c c1 c2 ...

       ---
       Guard Conditions

       Guard Generation

       When SMT is needed, guards are generated using guard_of_prob:

       let guard_of_prob (wl:worklist) (problem:tprob) (t1 : term) (t2 : term) : term & worklist =
           let has_type_guard t1 t2 =
               match problem.element with
               | Some t -> U.mk_has_type t1 (S.bv_to_name t) t2
               | None ->
                   let x = S.new_bv None t1 in
                   let u_x = env.universe_of env t1 in
                   U.mk_forall u_x x (U.mk_has_type t1 (S.bv_to_name x) t2)
           in
           match problem.relation with
           | EQ     -> mk_eq2 wl (TProb problem) t1 t2
           | SUB    -> has_type_guard t1 t2, wl
           | SUBINV -> has_type_guard t2 t1, wl

       Guard Simplification

       Guards are simplified before being returned:

       let simplify_vc full_norm_allowed env t =
         let steps = [Env.Beta; Env.Eager_unfolding; Env.Simplify;
                      Env.Primops; Env.Exclude Env.Zeta] in
         let steps = if full_norm_allowed then steps else Env.NoFullNorm::steps in
         norm_with_steps steps env t

       ---
       Deferred Constraints

       When Constraints Are Deferred

       Constraints are deferred in several situations:

       1. Flex-flex non-patterns: When neither side is a pattern
       2. Flex-rigid with insufficient context: When the RHS has free variables not in the LHS context
       3. Universe constraints involving U_max: When structural matching is uncertain
       4. Match heuristics: When pattern matching needs more information
       5. Occurs check failures: When a uvar occurs in its proposed solution

       and giveup_or_defer (orig:prob) (wl:worklist) (reason:deferred_reason) (msg:lstring) : solution =
           if wl.defer_ok = DeferAny
           then begin
               if !dbg_Rel then
                   Format.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" ...;
               solve (defer reason msg orig wl)
           end
           else giveup wl msg orig

       Deferred Reasons

       type deferred_reason =
         | Deferred_occur_check_failed
         | Deferred_free_names_check_failed
         | Deferred_univ_constraint
         | Deferred_flex
         | Deferred_flex_flex_nonpattern
         | Deferred_first_order_heuristic_failed
         | Deferred_delay_match_heuristic
         | Deferred_to_user_tac
         | Deferred_not_a_pattern

       Resolution of Deferred Constraints

       Deferred constraints are re-attempted when the counter increases:

       | None -> (* No more attempting problems *)
           match view probs.wl_deferred with
           | VCons _ _ ->
             let attempt, rest = probs.wl_deferred |> CList.partition
                                   (fun (c, _, _, _) -> c < probs.ctr) in
             (* c < probs.ctr means this problem was deferred before progress was made *)
             match view attempt with
             | VNil -> Success (as_deferred probs.wl_deferred, ...)
             | _ -> solve ({probs with attempting=...; wl_deferred=rest})

       ---
       Normalization Interaction

       When Normalization Occurs

       Normalization is used extensively:

       1. Before comparison: Types are reduced to weak head normal form
       2. For refinement extraction: base_and_refinement normalizes to expose refinements
       3. For delta unfolding: head_matches_delta unfolds definitions to find matching heads

       let whnf env t =
         let norm steps t = t |> U.unmeta |> N.normalize steps env |> SS.compress |> U.unlazy_emb in
         let steps =
           (if should_strongly_reduce t
             then [Env.Exclude Env.Zeta; Env.UnfoldUntil delta_constant]
             else [Env.Weak; Env.HNF])
           @ [Env.Beta; Env.Reify; Env.Primops]
         in
         norm steps t

       Head Matching with Delta

       The head_matches_delta function tries to make heads match through unfolding:

       let head_matches_delta env logical smt_ok t1 t2 : (match_result & option (typ&typ)) =
           let rec aux retry n_delta t1 t2 =
               let r = head_matches env t1 t2 in
               match r with
               | MisMatch (Some d1, Some d2) when d1=d2 ->
                 reduce_both_and_try_again d1 r
               | MisMatch (Some d1, Some d2) ->
                 reduce_one_and_try_again d1 d2
               | HeadMatch _ | FullMatch ->
                 success n_delta r t1 t2

       ---
       Debugging Subtyping Failures

       Debug Toggles

       The file defines numerous debug toggles:

       let dbg_Discharge            = Debug.get_toggle "Discharge"
       let dbg_EQ                   = Debug.get_toggle "EQ"
       let dbg_ExplainRel           = Debug.get_toggle "ExplainRel"
       let dbg_Rel                  = Debug.get_toggle "Rel"
       let dbg_RelBench             = Debug.get_toggle "RelBench"
       let dbg_RelDelta             = Debug.get_toggle "RelDelta"
       let dbg_RelTop               = Debug.get_toggle "RelTop"
       let dbg_LayeredEffectsApp    = Debug.get_toggle "LayeredEffectsApp"

       Error Explanation

       The explain function provides detailed error messages:

       let explain wl d (s : lstring) =
           if !dbg_ExplainRel || !dbg_Rel
           then Format.fmt4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
                              (Range.string_of_range <| p_loc d)
                              (prob_to_string' wl d)
                              (p_reason d |> String.concat "\n\t>")
                              (Thunk.force s)
           else (* Simplified error message *)

       Common Failure Patterns

       1. Occurs check failure: A uvar appears in its own solution
       2. Free names check failure: RHS has variables not in LHS context
       3. Head mismatch: Incompatible type constructors
       4. Effect mismatch: No subtyping path between effects
       5. Arity mismatch: Different numbers of arguments/binders

       ---
       Top-Level Interface

       Type Equality

       let try_teq smt_ok env t1 t2 : option guard_t =
         let prob, wl = new_t_problem (empty_worklist env) env t1 EQ t2 None (Env.get_range env) in
         with_guard env prob <| solve_and_commit (singleton wl prob smt_ok) (fun _ -> None)

       let teq env t1 t2 : guard_t =
           match try_teq true env t1 t2 with
           | None -> Err.basic_type_error env ...; trivial_guard
           | Some g -> g

       Subtyping

       let check_subtyping env t1 t2 =
           let prob, x, wl = new_t_prob (empty_worklist env) env t1 SUB t2 in
           let env_x = Env.push_bv env x in
           with_guard env_x prob <| solve_and_commit (singleton wl prob smt_ok) (fun _ -> None)
           |> Option.map (fun g -> (x, g))

       Computation Subtyping

       let sub_comp env c1 c2 =
           let prob, wl = new_problem (empty_worklist env) env c1 SUB c2 None ... in
           let wl = { wl with repr_subcomp_allowed = true } in
           with_guard env (CProb prob) <| solve_and_commit (singleton wl prob true) (fun _ -> None)

       ---
       Implicit Resolution

       The file also handles resolution of implicit arguments through the resolve_implicits' function, which:

       1. Runs meta-argument tactics for uvars with attached tactics
       2. Caches typeclass resolutions to avoid redundant work
       3. Handles single-valued implicits (unit types)
       4. Checks implicit solutions against expected types

       let rec until_fixpoint acc implicits : tagged_implicits =
           let out, changed, defer_open_metas = acc in
           match implicits with
           | [] ->
             if changed then until_fixpoint ([], false, true) (List.map fst out)
             else if defer_open_metas then until_fixpoint ([], false, false) (List.map fst out)
             else (* Try other resolution strategies *)
           | hd::tl ->
             if unresolved ctx_u && flex_uvar_has_meta_tac ctx_u
             then (* Run tactic and continue *)
             else if unresolved ctx_u
             then until_fixpoint ((hd, Implicit_unresolved)::out, changed, defer_open_metas) tl
             else (* Check and discharge *)

       ---
       Summary

       The Rel.fst module implements F*'s sophisticated type relation checking through:

       1. A worklist-based constraint solver that processes problems by rank
       2. Higher-order pattern unification with fallbacks to quasi-patterns and imitation
       3. Careful handling of flex-flex constraints through intersection of contexts
       4. Universe constraint solving with structural matching and inequality resolution
       5. Effect subtyping through effect lattices and indexed effect combinators
       6. Guard generation for SMT-assisted verification
       7. Strategic deferral of constraints that may become solvable with more information

       Understanding this module is essential for anyone working on F*'s type system, adding new type formers, or debugging complex type inference failures.
  ⎿  Done (12 tool uses · 167.5k tokens · 3m 14s)

● elite-bug-hunter(F* Ch7: Normalization & NBE)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering NORMALIZATION AND NBE.

       Explore /home/grigory/Downloads/FStar/src/typechecker/ extensively.

       Focus on:
       1. Read FStarC.TypeChecker.Normalize.fst completely (145KB) - document normalization
       2. Read FStarC.TypeChecker.NBE.fst completely - document Normalization by Evaluation
       3. Read FStarC.TypeChecker.NBETerm.fst - understand NBE term representation
       4. Read FStarC.TypeChecker.Cfg.fst - understand normalization configuration
       5. Understand primops (Primops.Base.fst and specific primops)

       Your chapter should include:
       - Reduction strategies (full, weak head, etc.)
       - Delta unfolding rules
       - Iota reduction (match)
       - Zeta reduction (let)
       - Beta reduction
       - NBE algorithm explanation
       - Configuration options (unfold hints, steps)
       - Memoization and caching
       - When to use normalization vs NBE
       - Performance considerations

       Read at least 8 files, provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive information. Let me write the detailed documentation chapter:

       ---
       F* Normalization and Normalization by Evaluation (NBE)

       Chapter Overview

       This chapter provides an in-depth examination of F*'s term normalization subsystem, comprising two complementary implementations: the traditional substitution-based normalizer (FStarC.TypeChecker.Normalize) and Normalization by Evaluation (FStarC.TypeChecker.NBE). These
       components are fundamental to F*'s type checking, proof automation, and extraction pipelines.

       ---
       1. Introduction to Normalization in F*

       Normalization in F* serves multiple critical purposes:

       1. Type checking: Reducing types to canonical forms for comparison
       2. Proof automation: Simplifying verification conditions before SMT encoding
       3. Code extraction: Evaluating compile-time computations during extraction to OCaml/F#/C
       4. Tactic execution: Running Meta-F* tactics at compile time

       F* provides two normalization engines that can be selected via configuration:

       - Traditional Normalizer: A substitution-based, environment-machine style normalizer implemented in FStarC.TypeChecker.Normalize.fst (3299 lines)
       - NBE (Normalization by Evaluation): A definitional interpreter that compiles F* terms to host-language (OCaml) values, implemented in FStarC.TypeChecker.NBE.fst (1538 lines)

       ---
       2. Normalization Configuration (FStarC.TypeChecker.Cfg)

       The normalization configuration is defined in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Cfg.fsti (lines 38-72):

       type fsteps = {
            beta : bool;                 // Beta reduction: (fun x -> e) v --> e[x/v]
            iota : bool;                 // Iota reduction: match on constructors
            zeta : bool;                 // Zeta reduction: let x = e in e' --> e'[x/e]
            zeta_full : bool;            // Full zeta (even recursive lets)
            weak : bool;                 // Weak reduction (don't descend under binders)
            hnf  : bool;                 // Head normal form only
            primops : bool;              // Reduce primitive operations
            do_not_unfold_pure_lets : bool;
            unfold_until : option S.delta_depth;
            unfold_only  : option (list I.lid);
            unfold_once  : option (list I.lid);
            unfold_fully : option (list I.lid);
            unfold_attr  : option (list I.lid);
            unfold_qual  : option (list string);
            unfold_namespace: option (Path.forest string bool);
            dont_unfold_attr : option (list I.lid);
            pure_subterms_within_computations : bool;
            simplify : bool;             // Logical simplification (True /\ t --> t, etc.)
            erase_universes : bool;
            allow_unbound_universes : bool;
            reify_ : bool;               // Reify monadic computations
            compress_uvars : bool;
            no_full_norm : bool;
            check_no_uvars : bool;
            unmeta : bool;
            unascribe : bool;
            in_full_norm_request: bool;
            weakly_reduce_scrutinee:bool;
            nbe_step:bool;               // Use NBE instead of traditional normalizer
            for_extraction:bool;
            unrefine:bool;
            default_univs_to_zero:bool;
            tactics : bool;
       }

       The full configuration record (cfg) at lines 96-107 includes additional fields:

       type cfg = {
            steps: fsteps;
            tcenv: Env.env;
            debug: debug_switches;
            delta_level: list Env.delta_level;  // Controls definition unfolding
            primitive_steps: PSMap.t primitive_step;
            strong : bool;                       // Under a binder
            memoize_lazy : bool;
            normalize_pure_lets: bool;
            reifying : bool;
            compat_memo_ignore_cfg: bool;
       }

       ---
       3. Reduction Strategies

       3.1 Beta Reduction

       Beta reduction substitutes arguments into function bodies. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Normalize.fst (lines 1532-1600), the normalizer handles beta reduction through closures:

       | Tm_app {hd; args} ->
           let head = SS.compress hd in
           begin match head.n with
           (* Beta reduction: (fun x -> body) arg *)
           | Tm_abs {bs=binders; body; rc_opt=lopt} ->
             (* Build closure environment with arguments *)
             let rec beta binders args env' : term =
               match binders, args with
               | [], [] -> norm cfg env' stack body
               | bs, [] -> 
                   (* Partial application - rebuild abstraction *)
                   rebuild cfg env stack (abs binders body lopt)
               | [], args ->
                   (* Over-application - normalize body then apply remaining *)
                   norm cfg env' (App(...) :: stack) body
               | b::bs, (a,_)::args ->
                   let env' = (Some (S.mk_binder b),
                              Clos(env, a, fresh_memo(), false),
                              fresh_memo()) :: env' in
                   beta bs args env'

       The key insight is that beta reduction is implemented by extending the environment with a closure mapping the bound variable to the argument, rather than performing explicit substitution.

       3.2 Iota Reduction (Pattern Matching)

       Iota reduction handles match expressions. The implementation at lines 2645-2726 uses pattern matching logic:

       let rec matches_pat (scrutinee_orig:term) (p:pat)
         : either (list (bv & term)) bool =
           (* Inl ts: p matches t and ts are bindings for the branch *)
           (* Inr false: p definitely does not match t *)
           (* Inr true: p may match t, but scrutinee is open, cannot decide *)
           let scrutinee = U.unmeta scrutinee_orig in
           let head, args = U.head_and_args scrutinee in
           match p.v with
           | Pat_var bv -> Inl [(bv, scrutinee_orig)]
           | Pat_dot_term _ -> Inl []
           | Pat_constant s ->
             match scrutinee.n with
             | Tm_constant s' when eq_const s s' -> Inl []
             | _ -> Inr (not (is_cons head))
           | Pat_cons(fv, _, arg_pats) ->
             match (U.un_uinst head).n with
             | Tm_fvar fv' when fv_eq fv fv' ->
               matches_args [] (List.rev args_rev) arg_pats
             | _ -> Inr (not (is_cons head))

       The normalizer only performs iota reduction when the iota step is enabled and the scrutinee is a constructor or constant. If the scrutinee is an open term (a variable), reduction blocks.

       3.3 Zeta Reduction (Let Bindings)

       Zeta reduction unfolds let bindings. The decision logic at lines 656-677 of the Normalize file:

       | Tm_let {lbs=(false, [lb]); body} -> // non-recursive let
         if Cfg.should_reduce_local_let cfg lb
         then (* Reduce: extend environment with let-bound value *)
           if cfg.steps.for_extraction && U.is_unit lb.lbtyp && U.is_pure_or_ghost_effect lb.lbeff
           then let env = (mk_t <| Constant Unit) :: env in
                translate cfg env body
           else let env = translate_letbinding cfg env lb :: env in
                translate cfg env body
         else (* Don't reduce: create UnreducedLet accumulator *)
           let name = freshen_bv (Inl?.v lb.lbname) in
           mk_t <| Accu(UnreducedLet(name, Thunk.mk typ, Thunk.mk def, Thunk.mk body, lb), [])

       For recursive let bindings, the zeta flag controls whether to unfold. From Unfolding.fst (lines 90-93):

       | Some (Inr ({sigquals=qs; sigel=Sig_let {lbs=(is_rec, _)}}, _), _), _ when
               is_rec && not cfg.steps.zeta && not cfg.steps.zeta_full ->
           log_unfolding cfg (fun () -> Format.print_string " >> Recursive definition but not doing Zeta\n");
           no

       3.4 Delta Reduction (Definition Unfolding)

       Delta reduction unfolds definitions based on the delta_level configuration. The complete decision logic is in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Normalize.Unfolding.fst (lines 18-174):

       let should_unfold cfg should_reify fv qninfo : should_unfold_res =
           let yes   = true  , false , false, false in  (* unfold normally *)
           let no    = false , false , false, false in  (* don't unfold *)
           let fully = true  , true  , false, false in  (* unfold and normalize result fully *)
           let reif  = true  , false , true,  false in  (* unfold for reification *)
           let once  = true  , false , false, true  in  (* unfold exactly once *)

           (* ... decision logic ... *)

           let default_unfolding () =
               yesno <| (cfg.delta_level |> BU.for_some (function
                    | NoDelta -> false
                    | InliningDelta | Eager_unfolding_only -> true
                    | Unfold l -> Common.delta_depth_greater_than
                                  (Env.delta_depth_of_fv cfg.tcenv fv) l))
           in

       The result type encodes four possible outcomes:

       - Should_unfold_no: Do not unfold
       - Should_unfold_yes: Unfold normally
       - Should_unfold_fully: Unfold and fully normalize the result
       - Should_unfold_once: Unfold exactly once (useful for debugging)
       - Should_unfold_reify: Unfold for effect reification

       ---
       4. The Traditional Normalizer Architecture

       4.1 Core Data Structures

       The normalizer uses an environment-machine style with closures and a stack. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Normalize.fst (lines 101-129):

       type closure =
         | Clos of env & term & cfg_memo (env & term) & bool 
           // memo for lazy evaluation; bool marks fixpoint
         | Univ of universe  // universe terms (no free variables)
         | Dummy              // placeholder for binders under strong reduction

       and env = list (option binder & closure & memo subst_t)

       type stack_elt =
        | Arg      of closure & aqual & Range.t
        | UnivArgs of list universe & Range.t
        | MemoLazy of cfg_memo (env & term)
        | Match    of env & option match_returns_ascription & branches &
                      option residual_comp & cfg & Range.t
        | Abs      of env & binders & env & option residual_comp & Range.t
        | App      of env & term & aqual & Range.t
        | CBVApp   of env & term & aqual & Range.t
        | Meta     of env & S.metadata & Range.t
        | Let      of env & binders & letbinding & Range.t

       type stack = list stack_elt

       Environment: A list of triples containing:
       1. An optional binder (for documentation/debugging)
       2. A closure representing the bound value
       3. A memo cell for caching computed substitutions

       Stack: Records the evaluation context, including pending arguments, match branches, and abstraction reconstruction frames.

       4.2 The Main Normalization Loop

       The core normalization is implemented as mutually recursive functions norm and rebuild. The general pattern (lines 1500-1700+):

       and norm (cfg:cfg) (env:env) (stack:stack) (t:term) : term =
         (* t is normalized in environment env, with stack as continuation *)
         match (SS.compress t).n with

         | Tm_delayed _ -> failwith "Impossible"

         | Tm_constant c when cfg.steps.primops ->
             (* Primitives: try to reduce *)
             let t = maybe_simplify cfg env stack t in
             rebuild cfg env stack t

         | Tm_bvar x ->
             (* Bound variable: look up in environment *)
             begin match List.nth_opt env x.index with
             | Some (_, Clos(env', t', m, _), _) ->
                 (* Found closure: normalize it *)
                 norm cfg env' stack t'
             | _ -> failwith "de Bruijn index out of bounds"
             end

         | Tm_app {hd; args} ->
             (* Application: push arguments on stack, normalize head *)
             let stack = List.fold_right
               (fun (a,q) stack -> Arg(Clos(env,a,fresh_memo(),false), q, a.pos)::stack)
               args stack in
             norm cfg env stack hd

         | Tm_abs {bs; body; rc_opt} when not (cfg.steps.weak || cfg.steps.hnf) ->
             (* Strong reduction: descend under binder *)
             (* ... *)

         | Tm_match {scrutinee; brs; ...} ->
             (* Push match frame, normalize scrutinee *)
             let stack = Match(env, ..., brs, ...) :: stack in
             norm cfg env stack scrutinee

       4.3 Rebuild Phase

       The rebuild function reconstructs terms from normal forms (lines 2261-2473):

       and rebuild (cfg:cfg) (env:env) (stack:stack) (t:term) : term =
         match stack with
         | [] -> t  (* Done! *)

         | Meta(_, m, r)::stack ->
             let t = mk (Tm_meta {tm=t; meta=m}) r in
             rebuild cfg env stack t

         | MemoLazy r::stack ->
             set_memo cfg r (env, t);  (* Memoize result *)
             rebuild cfg env stack t

         | Arg (Clos(env_arg, tm, m, _), aq, r) :: stack ->
             (* Rebuild application *)
             if cfg.steps.hnf && not (is_partial_primop_app cfg t) then
                let arg = closure_as_term cfg env_arg tm in
                rebuild cfg env_arg stack (extend_app t (arg, aq) r)
             else
                (* Normalize argument, possibly with memoization *)
                match read_memo cfg m with
                | Some (_, a) -> rebuild cfg env_arg stack (extend_app t (a, aq) r)
                | None ->
                    let stack = MemoLazy m :: App(env, t, aq, r) :: stack in
                    norm cfg env_arg stack tm

         | Match(env', asc_opt, branches, lopt, cfg, r) :: stack ->
             (* Try to reduce match *)
             if cfg.steps.iota
             then matches scrutinee branches
             else norm_and_rebuild_match ()

       ---
       5. Normalization by Evaluation (NBE)

       5.1 Theoretical Background

       NBE is inspired by the paper "Full Reduction at Full Throttle" (Boespflug et al., 2011). As noted in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.NBE.fst (lines 53-78):

       (* Broadly, the algorithm implemented here is inspired by

          Full Reduction at Full Throttle:
            https://dl.acm.org/citation.cfm?id=2178141

          Except, we don't implement any of the native tricks in the OCaml
          runtime for compiling inductives and pattern matching. So, you
          could see what we're doing here as, perhaps, "Full Reduction at
          Half Throttle".

          More classically, what we have here is a definitional interpreter,
          in the tradition of Reynolds' Definitional Interpreters:
            https://dl.acm.org/citation.cfm?id=805852 (1972)

          The broad idea of the algorithm is sketched for a tiny lambda
          calculus in examples/metatheory/FullReductionInterpreter.fst
       *)

       The core insight: translate F* terms into OCaml values (the host language), leverage OCaml's native function application for beta reduction, then read back the resulting values to F* syntax.

       5.2 NBE Term Representation

       The semantic domain is defined in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.NBETerm.fsti (lines 54-174):

       type constant =
         | Unit | Bool of bool | Int of int | String of string & Range.t
         | Char of FStar.Char.char | Range of Range.t | SConst of sconst | Real of string

       type atom =
         | Var of var                    // Irreducible variable
         | Match of t & (unit -> ...) & (unit -> list branch) & (unit -> ...)
         | UnreducedLet of var & Thunk.t t & Thunk.t t & Thunk.t t & letbinding
         | UnreducedLetRec of list (var & t & t) & t & list letbinding
         | UVar of Thunk.t S.term

       and lam_shape =
         | Lam_bs of (list t & binders & option S.residual_comp)
         | Lam_args of (list arg)
         | Lam_primop of (S.fv & list arg)

       and t' =
         | Lam of { interp : list (t & aqual) -> t; shape : lam_shape; arity : int }
         | Accu of atom & args           // Blocked computation (variable applied to args)
         | Construct of fv & list universe & args  // Data constructor application
         | FV of fv & list universe & args         // Free variable application
         | Constant of constant
         | Type_t of universe
         | Univ of universe
         | Unknown
         | Arrow of either (Thunk.t S.term) (list arg & comp)
         | Refinement of (t -> t) & (unit -> arg)
         | Reflect of t
         | Quote of S.term & S.quoteinfo
         | Lazy of (either S.lazyinfo (Dyn.dyn & emb_typ)) & Thunk.t t
         | Meta of t & Thunk.t S.metadata
         | TopLevelLet of letbinding & int & args
         | TopLevelRec of letbinding & int & list bool & args
         | LocalLetRec of int & letbinding & list letbinding & list t & args & int & list bool

       and t = { nbe_t : t'; nbe_r : Range.t }

       Key observations:

       1. Lam: Functions are represented as OCaml functions (interp), plus metadata (shape) for readback
       2. Accu: Accumulator for blocked computations (e.g., variable applied to arguments)
       3. Construct: Fully applied data constructors
       4. FV: Partially applied or blocked free variables

       5.3 The Translate Function

       Translation from F* syntax to semantic values (NBE.fst lines 389-713):

       let rec translate (cfg:config) (bs:list t) (e:term) : t =
           match (SS.compress e).n with
           | Tm_constant c -> mk_t <| Constant (translate_constant c)

           | Tm_bvar db ->  // de Bruijn variable
             if db.index < List.length bs
             then List.nth bs db.index
             else failwith "de Bruijn index out of bounds"

           | Tm_abs {bs=xs; body; rc_opt=resc} ->
             mk_t <| Lam {
               interp = (fun ys -> translate cfg (List.append (List.map fst ys) bs) body);
               shape = Lam_bs (bs, xs, resc);
               arity = List.length xs;
             }

           | Tm_app {hd; args} ->
             iapp cfg (translate cfg bs hd)
                      (List.map (fun x -> (translate cfg bs (fst x), snd x)) args)

           | Tm_match {scrutinee=scrut; brs=branches; ...} ->
             let scrut = translate cfg bs scrut in
             match (unlazy_unmeta scrut).nbe_t with
             | Construct(c, us, args_rev) ->
                 (* Scrutinee is a constructor - try to match *)
                 match pickBranch cfg scrut branches with
                 | Some (branch, args) ->
                   translate cfg (List.fold_left (fun bs x -> x::bs) bs args) branch
                 | None -> mkAccuMatch scrut make_returns make_branches make_rc
             | _ -> mkAccuMatch scrut make_returns make_branches make_rc

       5.4 The iapp Function (Application)

       NBE application handles multiple cases (NBE.fst lines 721-881):

       and iapp (cfg : config) (f:t) (args:args) : t =
         match (unlazy_unmeta f).nbe_t with

         | Lam {interp=f; shape; arity=n} ->
           let m = List.length args in
           if m < n then
             (* Partial application: create new lambda *)
             mk <| Lam { interp = (fun l -> f (List.append l arg_values_rev));
                         shape = ...; arity = n-m }
           else if m = n then
             (* Exact application: call OCaml function *)
             f (List.rev args)
           else
             (* Over-application: apply, then apply remaining *)
             let (args, args') = List.splitAt n args in
             iapp cfg (f (List.rev args)) args'

         | Accu (a, ts) ->
             (* Blocked term: accumulate more arguments *)
             mk <| Accu (a, List.rev_append args ts)

         | Construct (i, us, ts) ->
             (* Data constructor: accumulate arguments *)
             let (us', ts') = aux args us ts in
             mk <| Construct (i, us', ts')

         | TopLevelRec (lb, arity, decreases_list, args') ->
             (* Recursive function: check if safe to unfold *)
             let args = List.append args' args in
             if List.length args >= arity then
               let should_reduce, _, _ =
                 should_reduce_recursive_definition args decreases_list in
               if not should_reduce then
                 (* Don't unfold: return as FV with args *)
                 iapp cfg (mkFV (Inr?.v lb.lbname) [] []) args
               else
                 (* Safe to unfold: translate body with arguments *)
                 let univs, rest = BU.first_N (List.length lb.lbunivs) args in
                 iapp cfg (translate cfg (List.rev (List.map fst univs)) lb.lbdef) rest

       5.5 The Readback Function

       Reading back semantic values to F* syntax (NBE.fst lines 1224-1512):

       and readback (cfg:config) (x:t) : term =
           match x.nbe_t with
           | Constant Unit -> S.unit_const
           | Constant (Bool true) -> U.exp_true_bool
           | Constant (Int i) -> U.exp_int (show i)

           | Lam {interp=f; shape=Lam_bs (ctx, binders, rc); ...} ->
             (* Read back lambda by applying to fresh variables *)
             let ctx, binders_rev, accus_rev =
               List.fold_left
                 (fun (ctx, binders_rev, accus_rev) b ->
                   let x = b.binder_bv in
                   let tnorm = readback cfg (translate cfg ctx x.sort) in
                   let x = { S.freshen_bv x with sort = tnorm } in
                   let ax = mkAccuVar x in
                   let ctx = ax :: ctx in
                   ctx, ({b with binder_bv=x})::binders_rev, (ax, aqual)::accus_rev)
                 (ctx, [], [])
                 binders
             in
             let body = readback cfg (f accus_rev) in
             U.abs (List.rev binders_rev) body rc

           | Accu (Var bv, args) ->
             let args = readback_args cfg args in
             U.mk_app (S.bv_to_name bv) args

           | Construct (fv, us, args) ->
             let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
             let fv = S.mk (Tm_fvar fv) (S.range_of_fv fv) in
             U.mk_app (S.mk_Tm_uinst fv (List.rev us)) args

       ---
       6. Primitive Operations (Primops)

       6.1 Primop Structure

       Primitive operations are defined in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.Primops.Base.fst. Each primop must provide both a traditional interpretation and an NBE interpretation:

       let as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, f_nbe) : primitive_step = {
           name                           = l;
           arity                          = arity;
           univ_arity                     = u_arity;
           auto_reflect                   = None;
           strong_reduction_ok            = is_strong;
           requires_binder_substitution   = false;
           renorm_after                   = false;
           interpretation                 = f;       // Traditional normalizer
           interpretation_nbe             = f_nbe;   // NBE
       }

       6.2 Helper Functions for Primop Definition

       The module provides mk1, mk2, etc. helpers for common patterns (lines 183-246):

       let mk1 #a #r (u_arity : int) (name : Ident.lid)
         {| EMB.embedding a |} {| NBE.embedding a |}
         {| EMB.embedding r |} {| NBE.embedding r |}
         (f : a -> r) : primitive_step =
         let interp : interp_t = mk_interp1 f in
         let nbe_interp : nbe_interp_t = mk_nbe_interp1 f in
         as_primitive_step_nbecbs true (name, 1, u_arity, interp, nbe_interp)

       let mk2 #a #b #r (u_arity : int) (name : Ident.lid)
         {| EMB.embedding a |} {| NBE.embedding a |}
         {| EMB.embedding b |} {| NBE.embedding b |}
         {| EMB.embedding r |} {| NBE.embedding r |}
         (f : a -> b -> r) : primitive_step =
         let interp : interp_t = mk_interp2 f in
         let nbe_interp : nbe_interp_t = mk_nbe_interp2 f in
         as_primitive_step_nbecbs true (name, 2, u_arity, interp, nbe_interp)

       6.3 NBE Embedding System

       NBE uses its own embedding system (NBETerm.fsti lines 231-273):

       type nbe_cbs = {
          iapp : t -> args -> t;
          translate : term -> t;
       }

       class embedding (a:Type0) = {
         em  : nbe_cbs -> a -> t;            // Embed OCaml value as NBE term
         un  : nbe_cbs -> t -> option a;     // Unembed NBE term to OCaml value
         typ : unit -> t;                     // The type as an NBE term
         e_typ : unit -> emb_typ;
       }

       val embed   : embedding 'a -> nbe_cbs -> 'a -> t
       val unembed : embedding 'a -> nbe_cbs -> t -> option 'a

       Built-in embeddings include e_bool, e_string, e_char, e_int, e_list, e_option, and function types via e_arrow.

       ---
       7. Memoization and Caching

       7.1 Traditional Normalizer Memoization

       The normalizer uses memo cells to cache intermediate results. From Normalize.fst (lines 101-105):

       type closure =
         | Clos of env & term & cfg_memo (env & term) & bool

       The cfg_memo is a reference cell that can hold None or Some (env, term). The memoization validity check (lines 134-150):

       let cfg_equivalent (c1 c2 : Cfg.cfg) : bool =
         if c1.compat_memo_ignore_cfg then true
         else
           c1.steps =? c2.steps &&
           c1.delta_level =? c2.delta_level &&
           c1.strong = c2.strong &&
           c1.normalize_pure_lets = c2.normalize_pure_lets &&
           c1.reifying = c2.reifying

       Setting and reading memos (lines 156-168):

       let set_memo (cfg:cfg) (memo : cfg_memo (env & term)) (value : (env & term)) : unit =
         match !memo with
         | Some _ -> ()  // Already set
         | None -> memo := Some value

       let read_memo (cfg:cfg) (memo : cfg_memo (env & term)) : option (env & term) =
         match !memo with
         | Some (_, (env, term)) -> Some (env, term)
         | _ -> None

       7.2 NBE Caching

       NBE maintains an FV cache to avoid re-translating the same free variable (NBE.fst lines 155-183):

       type config = {
         core_cfg: Cfg.cfg;
         fv_cache: SMap.t t
       }

       let cache_add (cfg:config) (fv:fv) (v:t) =
         let lid = fv.fv_name in
         SMap.add cfg.fv_cache (string_of_lid lid) v

       let try_in_cache (cfg:config) (fv:fv) : option t =
         let lid = fv.fv_name in
         SMap.try_find cfg.fv_cache (string_of_lid lid)

       ---
       8. Simplification Rules

       The normalizer includes logical simplification rules (Normalize.fst lines 2020-2258):

       and maybe_simplify_aux (cfg:cfg) (env:env) (stack:stack) (tm:term) : term & bool =
           if not <| cfg.steps.simplify then tm, false
           else
           match (SS.compress tm).n with
           | Tm_app {hd={n=Tm_fvar fv}; args} ->
             (* Boolean simplifications *)
             if S.fv_eq_lid fv PC.and_lid then
               match args |> List.map simplify with
               | [(Some true, _); (_, (arg, _))]
               | [(_, (arg, _)); (Some true, _)] -> maybe_auto_squash arg, false
               | [(Some false, _); _]
               | [_; (Some false, _)] -> w U.t_false, false
               | _ -> squashed_head_un_auto_squash_args tm

             else if S.fv_eq_lid fv PC.or_lid then
               match args |> List.map simplify with
               | [(Some true, _); _]
               | [_; (Some true, _)] -> w U.t_true, false
               | [(Some false, _); (_, (arg, _))]
               | [(_, (arg, _)); (Some false, _)] -> maybe_auto_squash arg, false
               | _ -> squashed_head_un_auto_squash_args tm

             else if S.fv_eq_lid fv PC.imp_lid then
               match args |> List.map simplify with
               | [_; (Some true, _)]
               | [(Some false, _); _] -> w U.t_true, false
               | [(Some true, _); (_, (arg, _))] -> maybe_auto_squash arg, false
               | [(_, (p, _)); (_, (q, _))] ->
                 if U.term_eq p q then w U.t_true, false
                 else squashed_head_un_auto_squash_args tm

       ---
       9. When to Use Normalization vs NBE

       9.1 Selection Mechanism

       The normalizer checks for the nbe_step flag to decide which engine to use (Normalize.fst lines 2749-2773):

       let normalize_with_primitive_steps ps s e (t:term) =
         let is_nbe = is_nbe_request s in
         (* ... *)
         let r =
           if is_nbe
           then nbe_eval c s t
           else norm c [] [] t
         in r

       9.2 Performance Characteristics

       Traditional Normalizer:
       - Better for small terms with few beta reductions
       - More predictable memory behavior
       - Supports all features uniformly

       NBE:
       - Significantly faster for computation-heavy normalization
       - Leverages native OCaml function application
       - Particularly beneficial for tactics and extraction
       - Requires embeddings for all types involved in computation

       9.3 Typical Use Cases

       | Use Case                            | Recommended Engine             |
       |-------------------------------------|--------------------------------|
       | Type checking                       | Traditional                    |
       | SMT encoding                        | Traditional                    |
       | Tactic execution                    | NBE                            |
       | Extraction                          | NBE                            |
       | Heavy computation (e.g., norm_term) | NBE                            |
       | Debugging                           | Traditional (more predictable) |

       ---
       10. Performance Considerations

       10.1 Controlling Normalization Depth

       Use unfold_until, unfold_only, or unfold_fully to control how deep normalization goes:

       let whnf_steps = [Primops; Weak; HNF; UnfoldUntil delta_constant; Beta]
       let unfold_whnf env t = normalize whnf_steps env t

       10.2 Avoiding Exponential Blowup

       The normalizer includes safeguards against exponential term blowup:

       1. Memoization: Prevents redundant normalization of shared subterms
       2. UnreducedLet: Preserves let bindings during extraction to avoid duplication
       3. Weak reduction: The Weak and HNF flags avoid descending under binders unnecessarily

       10.3 Debugging Normalization

       Enable debug output via flags:

       type debug_switches = {
           gen              : bool;  // General normalization
           top              : bool;  // Top-level calls
           cfg              : bool;  // Configuration
           primop           : bool;  // Primitive operations
           unfolding        : bool;  // Delta unfolding decisions
           wpe              : bool;  // WP elaboration
           norm_delayed     : bool;  // Delayed terms
           print_normalized : bool;  // Print results
           debug_nbe        : bool;  // NBE-specific
       }

       ---
       11. Summary

       F*'s normalization system provides:

       1. Configurable reduction strategies via fsteps with fine-grained control over beta, iota, zeta, and delta reductions
       2. Two complementary engines:
         - Traditional substitution-based normalizer for general-purpose use
         - NBE for computation-heavy scenarios leveraging OCaml's native evaluation
       3. Sophisticated delta unfolding with multiple criteria: depth-based, attribute-based, qualifier-based, and namespace-based
       4. Memoization to avoid redundant computation
       5. Logical simplification rules for proof automation
       6. Primop framework enabling efficient evaluation of built-in operations in both engines

       The key architectural insight is that NBE translates F* syntax to OCaml values (translate), performs reduction via OCaml function application (iapp), and converts results back to syntax (readback). This leverages the host language's efficient function application while
       maintaining the ability to produce syntactic normal forms.
  ⎿  Done (22 tool uses · 135.5k tokens · 3m 56s)

● elite-bug-hunter(F* Ch8: Effect System)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering THE EFFECT SYSTEM.

       Explore /home/grigory/Downloads/FStar/src/typechecker/ extensively.

       Focus on:
       1. Read FStarC.TypeChecker.TcEffect.fst completely (105KB) - document effect elaboration
       2. Read FStarC.TypeChecker.DMFF.fst (71KB) - document dependent types in effects
       3. Understand effect definitions in ulib (FStar.Pure, FStar.ST, etc.)
       4. Understand effect combinators (bind, return, lift)

       Your chapter should include:
       - What effects are in F* (Pure, Ghost, ST, etc.)
       - How effects are declared and elaborated
       - Effect indexing and pre/post conditions
       - Effect polyvariance
       - Layered effects
       - Effect lifting and subeffecting
       - Reifiable effects
       - The DMFF transformation
       - When to use which effect
       - Defining custom effects

       Read at least 8 files across src/typechecker and ulib. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive source material. Let me write the detailed documentation chapter on the F* effect system.

       ---
       THE F* EFFECT SYSTEM: A COMPREHENSIVE REFERENCE

       1. INTRODUCTION TO EFFECTS IN F*

       F* is a proof-oriented programming language that uses a sophisticated effect system to track computational effects in types. Effects capture information about what a computation may do beyond computing a pure value---it may diverge, access mutable state, throw exceptions,
       perform I/O, or have other side effects.

       The effect system serves multiple critical purposes:

       1. Verification Precision: Effects allow F* to verify that code meets its specification by tracking pre- and postconditions through WP (weakest precondition) transformers
       2. Extraction Correctness: Effects determine how code is extracted to target languages (OCaml, F#, C)
       3. Erasure: Ghost computations are erased during extraction since they are computationally irrelevant
       4. Modularity: Custom effects enable domain-specific verification with tailored reasoning principles

       The effect system has evolved significantly, from traditional WP-indexed effects to the modern "layered effects" that provide more flexible indexing.

       ---
       2. CORE PRIMITIVE EFFECTS

       2.1 The PURE Effect

       The foundational effect in F* is PURE, defined in /home/grigory/Downloads/FStar/ulib/Prims.fst (lines 430-441):

       total
       new_effect {
         PURE : a: Type -> wp: pure_wp a -> Effect
         with
           return_wp    = pure_return0
         ; bind_wp      = pure_bind_wp0
         ; if_then_else = pure_if_then_else0
         ; ite_wp       = pure_ite_wp0
         ; stronger     = pure_stronger
         ; close_wp     = pure_close_wp0
         ; trivial      = pure_trivial
       }

       PURE is indexed by a type a (the result type) and a weakest precondition wp: pure_wp a. The WP type is defined as (lines 333-347):

       let pure_wp' (a: Type) = pure_post a -> GTot pure_pre
       let pure_wp_monotonic0 (a:Type) (wp:pure_wp' a) =
         forall (p q:pure_post a). (forall (x:a). p x ==> q x) ==> (wp p ==> wp q)
       let pure_wp (a: Type) = wp:pure_wp' a{pure_wp_monotonic a wp}

       Key insight: A pure_wp transforms postconditions to preconditions and must satisfy monotonicity---if postcondition p implies q pointwise, then wp p must imply wp q.

       The Tot effect is defined as PURE with a trivial WP (lines 458-462):

       unfold let pure_null_wp0 (a: Type) : pure_wp a = 
         fun (p: pure_post a) -> forall (any_result: a). p any_result

       effect Tot (a: Type) = PURE a (pure_null_wp0 a)

       The Hoare-style Pure effect abbreviation allows specifying pre- and postconditions directly (lines 447-449):

       effect Pure (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
         PURE a (fun (p: pure_post a) -> pre /\ (forall (pure_result: a). post pure_result ==> p pure_result))

       2.2 The GHOST Effect

       GHOST is logically equivalent to PURE but nominally distinct, allowing computationally irrelevant operations. From /home/grigory/Downloads/FStar/ulib/Prims.fst (lines 480-498):

       total
       new_effect GHOST = PURE

       sub_effect PURE ~> GHOST { lift_wp = purewp_id }

       effect Ghost (a: Type) (pre: Type) (post: pure_post' a pre) =
         GHOST a (fun (p: pure_post a) -> pre /\ (forall (ghost_result: a). post ghost_result ==> p ghost_result))

       effect GTot (a: Type) = GHOST a (pure_null_wp0 a)

       GHOST computations are erased during extraction. The FStar.Ghost.erased type (from /home/grigory/Downloads/FStar/ulib/FStar.Ghost.fsti) provides a way to wrap values that should not exist at runtime:

       [@@ erasable]
       new val erased ([@@@strictly_positive] a: Type u#a) : Type u#a

       val reveal: #a: Type u#a -> erased a -> GTot a
       val hide: #a: Type u#a -> a -> Tot (erased a)

       2.3 The DIV Effect

       DIV captures potentially divergent computations. From /home/grigory/Downloads/FStar/ulib/FStar.Pervasives.fsti (lines 240-253):

       new_effect {
         DIV : a:Type -> wp:pure_wp a -> Effect
         with
           return_wp = pure_return
         ; bind_wp = pure_bind_wp
         ; if_then_else = pure_if_then_else
         ; ite_wp = pure_ite_wp
         ; stronger = pure_stronger
         ; close_wp = pure_close_wp
         ; trivial = pure_trivial
       }

       sub_effect PURE ~> DIV { lift_wp = purewp_id }

       DIV has the same WP combinators as PURE, but is interpreted with partial correctness semantics---the specification only holds if the computation terminates.

       ---
       3. EFFECT COMBINATORS

       Every effect must define a set of combinators that enable the typechecker to compose computations and reason about their specifications.

       3.1 Return Combinator

       The return_wp combinator lifts a pure value into the effect. From /home/grigory/Downloads/FStar/ulib/Prims.fst (lines 361-364):

       unfold let pure_return0 (a: Type) (x: a) : pure_wp a =
         fun (p: pure_post a) -> forall (return_val: a). return_val == x ==> p return_val

       This says: "to satisfy any postcondition p after returning x, we need p x to hold."

       3.2 Bind Combinator

       The bind_wp combinator sequences two computations. From /home/grigory/Downloads/FStar/ulib/Prims.fst (lines 370-377):

       unfold let pure_bind_wp0 (a b: Type) (wp1: pure_wp a) (wp2: (a -> GTot (pure_wp b))) : pure_wp b =
         fun (p: pure_post b) -> wp1 (fun (bind_result_1: a) -> wp2 bind_result_1 p)

       This composes WPs: to satisfy p after both computations, we need wp1 to hold with a continuation that, given the intermediate result, requires wp2 to produce p.

       3.3 Conditional Combinators

       Two combinators handle conditionals:

       if_then_else for simple branching (lines 394-397):
       unfold let pure_if_then_else0 (a p: Type) (wp_then wp_else: pure_wp a) : pure_wp a =
         fun (post: pure_post a) -> wp_then post /\ (~p ==> wp_else post)

       ite_wp for avoiding postcondition duplication (lines 407-410):
       unfold let pure_ite_wp0 (a: Type) (wp: pure_wp a) : pure_wp a =
         fun (post: pure_post a) ->
         forall (k: pure_post a). (forall (x: a). {:pattern (guard_free (k x))} post x ==> k x) ==> wp k

       3.4 Subsumption (Stronger)

       The stronger combinator expresses when one WP is stronger than another (line 414):

       unfold let pure_stronger (a: Type) (wp1 wp2: pure_wp a) =
         forall (p: pure_post a). wp1 p ==> wp2 p

       3.5 Universal Closure

       The close_wp combinator closes over a binder (line 421):

       unfold let pure_close_wp0 (a b: Type) (wp: (b -> GTot (pure_wp a))) : pure_wp a =
         fun (p: pure_post a) -> forall (b: b). wp b p

       ---
       4. EFFECT TEMPLATES AND INSTANTIATION

       4.1 The STATE_h Template

       F* provides effect templates that can be instantiated with specific types. From /home/grigory/Downloads/FStar/ulib/FStar.Pervasives.fsti (lines 290-360):

       let st_pre_h (heap: Type) = heap -> GTot Type0
       let st_post_h' (heap a pre: Type) = a -> _: heap{pre} -> GTot Type0
       let st_post_h (heap a: Type) = st_post_h' heap a True
       let st_wp_h (heap a: Type) = st_post_h heap a -> Tot (st_pre_h heap)

       new_effect {
         STATE_h (heap: Type) : result: Type -> wp: st_wp_h heap result -> Effect
         with
           return_wp = st_return heap
         ; bind_wp = st_bind_wp heap
         ; if_then_else = st_if_then_else heap
         ; ite_wp = st_ite_wp heap
         ; stronger = st_stronger heap
         ; close_wp = st_close_wp heap
         ; trivial = st_trivial heap
       }

       4.2 Instantiating STATE_h

       The FStar.ST module instantiates STATE_h with a concrete heap type. From /home/grigory/Downloads/FStar/ulib/FStar.ST.fst (lines 26-77):

       new_effect GST = STATE_h heap

       unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:heap) = wp (fun a -> p a h)
       sub_effect DIV ~> GST = lift_div_gst

       new_effect STATE = GST
       sub_effect GST ~> STATE = lift_gst_state

       effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
         STATE a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))

       effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

       ---
       5. SUB-EFFECTING (EFFECT LIFTING)

       Effects form a partial order through sub-effecting declarations. A lift from effect M to effect N provides:
       1. A way to embed M computations in N contexts
       2. A transformation of M's WP to N's WP

       From /home/grigory/Downloads/FStar/ulib/FStar.Pervasives.fsti (lines 451-453):

       unfold let lift_div_exn (a: Type) (wp: pure_wp a) (p: ex_post a) = wp (fun a -> p (V a))
       sub_effect DIV ~> EXN { lift_wp = lift_div_exn }

       The typechecker validates lifts in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.TcEffect.fst (lines 2462-2573). Key validation:

       let tc_lift env sub r =
         ...
         let ed_src = Env.get_effect_decl env sub.source in
         let ed_tgt = Env.get_effect_decl env sub.target in
         
         if ed_src |> U.is_layered || ed_tgt |> U.is_layered
         then tc_layered_lift (Env.set_range env r) sub
         else
           let a, wp_a_src = monad_signature env sub.source ... in
           let expected_k = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
           ...

       The lift must be universe-polymorphic in exactly one universe.

       ---
       6. LAYERED EFFECTS

       Layered effects are a more flexible effect system introduced to support indexed effects where indices are not WPs. They allow effects to be parameterized by arbitrary types.

       6.1 Layered Effect Structure

       A layered effect provides:
       - signature: The effect's type signature
       - repr: A representation type for computations
       - return: Monadic return
       - bind: Monadic bind
       - subcomp: Subsumption/coercion between effect indices
       - if_then_else: Conditional combinator

       From /home/grigory/Downloads/FStar/ulib/FStar.Tactics.Effect.fsti (lines 103-113):

       [@@ default_effect "FStar.Tactics.Effect.Tac"]
       reflectable
       effect {
         TAC (a:Type) (wp:tac_wp_t a)
         with { repr=tac_repr;
                return=tac_return;
                bind=tac_bind;
                if_then_else=tac_if_then_else;
                subcomp=tac_subcomp;
                close = tac_close }
       }

       6.2 The repr Type

       The representation type defines what a computation "is" internally. For TAC:

       let tac_repr (a:Type) (wp:tac_wp_t a) = ref_proofstate -> Dv a

       For the monotonic state effect MST (from /home/grigory/Downloads/FStar/ulib/experimental/FStar.MST.fst, lines 26-38):

       type repr (a:Type) (state:Type u#2) (rel:P.preorder state) (req:pre_t state) (ens:post_t state a) =
         s0:state ->
         DIV (a & state)
           (as_pure_wp (fun p ->
             req s0 /\
             (forall (x:a) (s1:state). (ens s0 x s1 /\ rel s0 s1) ==> p (x, s1))))

       6.3 Layered Effect Combinators

       The return combinator (FStar.MST.fst, lines 39-48):
       let return (a:Type) (x:a) (state:Type u#2) (rel:P.preorder state)
         : repr a state rel (fun _ -> True) (fun s0 r s1 -> r == x /\ s0 == s1)
         = fun s0 -> x, s0

       The bind combinator (lines 50-67):
       let bind (a:Type) (b:Type) (state:Type u#2) (rel:P.preorder state)
         (req_f:pre_t state) (ens_f:post_t state a)
         (req_g:a -> pre_t state) (ens_g:a -> post_t state b)
         (f:repr a state rel req_f ens_f)
         (g:(x:a -> repr b state rel (req_g x) (ens_g x)))
         : repr b state rel
           (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
           (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
         = fun s0 -> let x, s1 = f s0 in (g x) s1

       The subcomp combinator for effect subsumption (lines 69-84):
       let subcomp (a:Type) (state:Type u#2) (rel:P.preorder state)
         (req_f:pre_t state) (ens_f:post_t state a)
         (req_g:pre_t state) (ens_g:post_t state a)
         (f:repr a state rel req_f ens_f)
         : Pure (repr a state rel req_g ens_g)
           (requires (forall s. req_g s ==> req_f s) /\
                     (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
           (ensures fun _ -> True)
         = f

       6.4 Effect Parameters

       Effect parameters are indices that don't change through computation. Marked with [@@@effect_param]:

       effect {
         MSTATE (a:Type)
                ([@@@ effect_param] state:Type u#2)
                ([@@@ effect_param] rel:P.preorder state)
                (req:pre_t state)
                (ens:post_t state a)
         with { repr; return; bind; subcomp; if_then_else }
       }

       ---
       7. EFFECT ELABORATION IN THE TYPECHECKER

       The typechecker elaborates effect declarations in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.TcEffect.fst.

       7.1 Layered Effect Typechecking

       From lines 1208-1217:
       let tc_layered_eff_decl env0 (ed : S.eff_decl) (quals : list qualifier) (attrs : list S.attribute) =
         Errors.with_ctx (Format.fmt1 "While checking layered effect definition `%s`" (string_of_lid ed.mname)) (fun () ->
           if !dbg_LayeredEffectsTc then
             Format.print1 "Typechecking layered effect: \n\t%s\n" (show ed);

           if List.length ed.univs <> 0 || List.length ed.binders <> 0 then
             raise_error ed.mname Errors.Fatal_UnexpectedEffect
               ("Binders are not supported for layered effects (" ^ (string_of_lid ed.mname) ^")");

       The signature must have form a:Type -> <indices> -> Effect:
       let a, u = fresh_a_and_u_a "a" in
       let rest_bs =
         TcUtil.layered_effect_indices_as_binders env r ed.mname (sig_us, sig_t) u (a.binder_bv |> S.bv_to_name) in
       let bs = a::rest_bs in
       let k = U.arrow bs (S.mk_Total S.teff) in

       7.2 Bind Shape Validation

       The bind combinator must have a specific shape. From lines 1369-1391:
       let bind_repr, bind_kind =
         Errors.with_ctx ("While checking the bind combinator") (fun () ->
           let bind_repr_ts = ed |> U.get_bind_repr |> Option.must in
           let bind_us, bind_t, bind_ty = check_and_gen "bind_repr" 2 bind_repr_ts in
           
           let k, kind = validate_indexed_effect_bind_shape env
             ed.mname ed.mname ed.mname
             sig_ts sig_ts sig_ts
             (Some repr_ts) (Some repr_ts) (Some repr_ts)
             us ty r num_effect_params
             (U.has_attribute ed.eff_attrs PC.bind_has_range_args_attr) in

       ---
       8. THE DMFF TRANSFORMATION

       DMFF (Dijkstra Monads For Free) automatically derives WP combinators from a monadic definition. Implemented in /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.DMFF.fst.

       8.1 Overview

       Given an effect with a representation type and return/bind, DMFF generates:
       - WP type from the representation
       - WP combinators (stronger, if_then_else, close_wp, trivial)

       8.2 The Star Transformation

       The core of DMFF is the "star transformation" that converts types. From lines 561-590:

       and star_type' env t =
         let t = SS.compress t in
         match t.n with
         | Tm_arrow {bs=binders} ->
             let binders = List.map (fun b ->
               {b with binder_bv={b.binder_bv with sort = star_type' env b.binder_bv.sort}}
             ) binders in
             match is_monadic_arrow t.n with
             | N hn ->
                 mk (Tm_arrow {bs=binders; comp=mk_Total (star_type' env hn)})
             | M a ->
                 mk (Tm_arrow {
                   bs=binders @ [ S.mk_binder_with_attrs (S.null_bv (mk_star_to_type env a))
                                 (S.as_bqual_implicit false) None []];
                   comp=mk_Total U.ktype0})

       For monadic arrows (H_0 -> ... -> H_n -M-> A), the transformation produces:
       H_0* -> ... -> H_n* -> (A* -> Type) -> Type

       8.3 Generating WP Combinators

       DMFF generates combinators like wp_if_then_else (lines 308-321):

       let wp_if_then_else =
         let result_comp = (mk_Total ((U.arrow [ S.null_binder wp_a; S.null_binder wp_a ] (mk_Total wp_a)))) in
         let c = S.gen_bv "c" None U.ktype in
         U.abs (binders @ S.binders_of_list [ a; c ]) (
           let l_ite = fvar_with_dd PC.ite_lid None in
           U.ascribe (
             U.mk_app c_lift2 (List.map S.as_arg [
               U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
             ])
           ) (Inr result_comp, None, false)
         ) (Some (U.residual_comp_of_comp result_comp))

       8.4 The CPS and Elaboration

       DMFF performs CPS transformation. From lines 1347-1352:

       let cps_and_elaborate (env:FStarC.TypeChecker.Env.env) (ed:S.eff_decl)
         : list S.sigelt & S.eff_decl & option S.sigelt =
         let effect_binders_un, signature_un = SS.open_term ed.binders (ed.signature |> U.effect_sig_ts |> snd) in
         let effect_binders, env, _ = TcTerm.tc_tparams env effect_binders_un in
         let signature, _ = TcTerm.tc_trivial_guard env signature_un in

       ---
       9. REIFIABLE AND REFLECTABLE EFFECTS

       9.1 Reification

       A reifiable effect allows converting an effectful computation to its representation. The reify keyword extracts the underlying representation:

       let x : repr a indices = reify (computation)

       9.2 Reflection

       A reflectable effect allows converting a representation back to an effectful computation. From /home/grigory/Downloads/FStar/ulib/experimental/FStar.MST.fst (lines 115-128):

       let get (#state:Type u#2) (#rel:P.preorder state) ()
           : MSTATE state state rel (fun _ -> True) (fun s0 r s1 -> s0 == r /\ r == s1)
         = MSTATE?.reflect (fun s0 -> s0, s0)

       let put (#state:Type u#2) (#rel:P.preorder state) (s:state)
           : MSTATE unit state rel (fun s0 -> rel s0 s) (fun _ _ s1 -> s1 == s)
         = MSTATE?.reflect (fun _ -> (), s)

       9.3 Marking Effects Reflectable

       Effects are marked reflectable in their declaration:

       reflectable
       effect {
         MSTATE (a:Type) ...
         with { repr; return; bind; subcomp; if_then_else }
       }

       ---
       10. POLYMONADIC BINDS

       Polymonadic binds allow composing computations from different effects. From /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.TcEffect.fst (lines 2665-2720):

       let tc_polymonadic_bind env (m:lident) (n:lident) (p:lident) (ts:S.tscheme)
         : (S.tscheme & S.tscheme & S.indexed_effect_combinator_kind) =
         let eff_name = Format.fmt3 "(%s, %s) |> %s)"
           (m |> ident_of_lid |> string_of_id)
           (n |> ident_of_lid |> string_of_id)
           (p |> ident_of_lid |> string_of_id) in

         check_polymonadic_bind_for_erasable_effects env m n p r;

         let (us, t, ty) = check_and_gen env eff_name "polymonadic_bind" 2 ts in

       A polymonadic bind (M, N) |> P composes an M computation with an N continuation to produce a P computation.

       ---
       11. ERASABILITY AND GHOST EFFECTS

       11.1 Erasable Effects

       An effect can be marked erasable, meaning computations in that effect are erased during extraction. The typechecker validates lifts involving erasable effects (lines 2446-2460):

       let check_lift_for_erasable_effects env (m1:lident) (m2:lident) (r:Range.t) : unit =
         let err reason = raise_error r Errors.Fatal_UnexpectedEffect ... in
         let m1 = Env.norm_eff_name env m1 in
         if lid_equals m1 PC.effect_GHOST_lid
         then err "user-defined lifts from GHOST effect are not allowed"
         else
           let m1_erasable = Env.is_erasable_effect env m1 in
           let m2_erasable = Env.is_erasable_effect env m2 in
           if m2_erasable && not m1_erasable && not (lid_equals m1 PC.effect_PURE_lid)
           then err "cannot lift a non-erasable effect to an erasable effect unless the non-erasable effect is PURE"

       11.2 The erased Type

       The erased type provides computationally irrelevant values:

       [@@ erasable]
       new val erased ([@@@strictly_positive] a: Type u#a) : Type u#a

       The erasable attribute tells the compiler to extract this type to unit.

       ---
       12. WHEN TO USE WHICH EFFECT

       12.1 Decision Guide

       | Effect         | When to Use                              |
       |----------------|------------------------------------------|
       | Tot            | Pure total functions                     |
       | Pure           | Total functions with pre/post conditions |
       | GTot           | Ghost total computations (erased)        |
       | Ghost          | Ghost with pre/post (erased)             |
       | Lemma          | Proof-only computations                  |
       | Dv             | Potentially divergent                    |
       | ST/State       | Heap-manipulating code                   |
       | Stack          | Stack-allocated code (LowStar)           |
       | Custom layered | Domain-specific effects                  |

       12.2 Effect Hierarchy

           PURE (Tot, Pure)
             |
             +---> GHOST (GTot, Ghost, Lemma)
             |
             +---> DIV (Dv, Div)
                     |
                     +---> EXN (Ex, Exn)
                     |
                     +---> STATE_h (ST, St)
                     |
                     +---> ALL_h (All)

       ---
       13. DEFINING CUSTOM EFFECTS

       13.1 Traditional WP-Indexed Effect

       let my_wp (a: Type) = (a -> Type0) -> Type0

       new_effect {
         MY_EFFECT : a:Type -> wp:my_wp a -> Effect
         with
           return_wp = ...
         ; bind_wp = ...
         ; if_then_else = ...
         ; ite_wp = ...
         ; stronger = ...
         ; close_wp = ...
         ; trivial = ...
       }

       13.2 Layered Effect Definition

       type my_repr (a:Type) (pre:Type0) (post:a -> Type0) = 
         unit -> Pure a (requires pre) (ensures post)

       let my_return (a:Type) (x:a) : my_repr a True (fun r -> r == x) = fun () -> x

       let my_bind (a b:Type) (pre_f:Type0) (post_f:a -> Type0)
                   (pre_g:a -> Type0) (post_g:a -> b -> Type0)
                   (f:my_repr a pre_f post_f) (g:(x:a -> my_repr b (pre_g x) (post_g x)))
         : my_repr b (pre_f /\ (forall x. post_f x ==> pre_g x))
                     (fun r -> exists x. post_f x /\ post_g x r)
         = fun () -> let x = f () in g x ()

       effect {
         MY_LAYERED (a:Type) (pre:Type0) (post:a -> Type0)
         with { repr = my_repr; return = my_return; bind = my_bind; ... }
       }

       ---
       14. CONCLUSION

       The F* effect system is a powerful mechanism for tracking and reasoning about computational effects. Key takeaways:

       1. WP-indexed effects provide the traditional approach where effects carry weakest precondition transformers
       2. Layered effects offer more flexibility by allowing arbitrary effect indices
       3. Sub-effecting creates a lattice of effects with automatic lifting
       4. DMFF automatically derives WP combinators from monadic definitions
       5. Reification and reflection bridge effectful and pure code
       6. Erasability enables ghost code that exists only for verification

       Understanding the effect system is essential for writing verified F* code, as it determines what specifications can be expressed and how computations compose.

       ---
       Source Files Referenced:
       - /home/grigory/Downloads/FStar/ulib/Prims.fst - Core PURE/GHOST effects
       - /home/grigory/Downloads/FStar/ulib/FStar.Pervasives.fsti - DIV, STATE_h, EXN, ALL_h
       - /home/grigory/Downloads/FStar/ulib/FStar.ST.fst - STATE instantiation
       - /home/grigory/Downloads/FStar/ulib/FStar.Ghost.fsti - Erased types
       - /home/grigory/Downloads/FStar/ulib/FStar.Tactics.Effect.fsti - Layered TAC effect
       - /home/grigory/Downloads/FStar/ulib/experimental/FStar.MST.fst - Layered monotonic state
       - /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.TcEffect.fst - Effect elaboration
       - /home/grigory/Downloads/FStar/src/typechecker/FStarC.TypeChecker.DMFF.fst - DMFF transformation

  ⎿  Done (25 tool uses · 144.4k tokens · 3m 41s)

● elite-bug-hunter(F* Ch9: SMT Encoding)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering SMT ENCODING.

       Explore /home/grigory/Downloads/FStar/src/smtencoding/ extensively.

       Focus on:
       1. Read FStarC.SMTEncoding.Encode.fst completely (113KB) - document main encoding
       2. Read FStarC.SMTEncoding.EncodeTerm.fst (80KB) - document term encoding
       3. Read FStarC.SMTEncoding.Term.fst - document SMT term representation
       4. Read FStarC.SMTEncoding.Solver.fst - document Z3 integration
       5. Read FStarC.SMTEncoding.Pruning.fst - document query optimization
       6. Read FStarC.SMTEncoding.Z3.fst - document Z3-specific handling
       7. Read FStarC.SMTEncoding.ErrorReporting.fst - document error translation

       Your chapter should include:
       - How F* types map to SMT sorts
       - How F* terms map to SMT terms
       - Fuel encoding for recursion
       - Patterns and triggers
       - Quantifier instantiation strategy
       - Query pruning heuristics
       - Z3 interaction protocol
       - Counterexample generation
       - Timeout handling
       - When proofs fail - debugging strategies

       Read all SMT encoding files. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive data from the SMT encoding subsystem. Let me write the detailed documentation chapter.

       ---
       F* SMT Encoding: A Comprehensive Technical Reference

       Chapter Overview

       This chapter provides an in-depth analysis of F*'s SMT encoding subsystem, which translates F* types, terms, and proof obligations into the SMT-LIB format understood by Z3 and other SMT solvers. The encoding is the critical bridge between F*'s rich dependent type system
       and the decidable first-order logic of SMT solvers.

       ---
       1. SMT Sort and Term Representation

       1.1 Core Sort System

       F* encodes its type system into a small set of SMT sorts defined in /home/grigory/Downloads/FStar/src/smtencoding/FStarC.SMTEncoding.Term.fsti (lines 28-39):

       type sort =
         | Bool_sort
         | Int_sort
         | String_sort
         | Real_sort
         | BitVec_sort of int        (* Fixed-width bit vectors *)
         | Array of sort & sort      (* SMT arrays *)
         | Arrow of sort & sort      (* Function sorts *)
         | Sort of string            (* Named sorts *)

       The most important derived sorts are defined in FStarC.SMTEncoding.Term.fst (lines 69-75):

       let Term_sort = Sort "Term"      (* Universal term sort *)
       let Fuel_sort = Sort "Fuel"      (* Fuel for recursion *)
       let univ_sort = Sort "Universe"  (* Universe levels *)
       let dummy_sort = Sort "Dummy"    (* Placeholder sort *)

       Critical Insight: F* uses a single Term_sort to represent ALL F* values, regardless of their F* type. Type information is encoded separately through typing predicates like HasType. This is the classic "many-sorted to unsorted" encoding approach.

       1.2 Term Representation

       Terms are represented as an algebraic data type in FStarC.SMTEncoding.Term.fsti (lines 51-82):

       type term' =
         | Integer   of string
         | String    of string
         | Real      of string
         | BoundV    of int                      (* de Bruijn indices *)
         | FreeV     of fv                       (* Free variables *)
         | App       of op & list term           (* Applications *)
         | Quant     of qop & list (list term) & (* Quantifiers with patterns *)
                        option int &              (* Weight for Z3 *)
                        list sort &               (* Bound variable sorts *)
                        term                      (* Body *)
         | Let       of list term & term         (* Let bindings *)
         | Labeled   of term & Errors.error_message & Range.t  (* Error locations *)
         | LblPos    of term & string            (* Z3 labels for counterexamples *)

       1.3 Operator Encoding

       The op type captures all SMT operations, from arithmetic to uninterpreted functions. Key operators from Term.fsti (lines 84-134):

       type op =
         | TrueOp | FalseOp | Not | And | Or | Imp | Iff | Eq
         | LT | LTE | GT | GTE | Add | Sub | Div | Mul | Mod | RealDiv
         | Minus                              (* Unary negation *)
         | ITE                                (* If-then-else *)
         | Var of string                      (* Uninterpreted function *)
         | BvAnd | BvOr | BvXor | BvNot       (* Bitvector ops *)
         | BvShl of int | BvShr of int        (* Bit shifts *)
         | BvUlt | BvUext of int              (* Bitvector comparisons *)
         | BvToNat | NatToBv of int           (* Conversions *)

       ---
       2. Type-to-Sort Mapping

       2.1 The Universal Term Sort Strategy

       Unlike simpler type systems, F* does NOT map each F* type to a distinct SMT sort. Instead, ALL F* values inhabit the single Term_sort. Type membership is encoded through typing predicates.

       From FStarC.SMTEncoding.EncodeTerm.fst (lines 182-215), the core typing predicates:

       let mk_HasType v t         = mkApp ("HasType", [v; t])
       let mk_HasTypeZ v t        = mkApp ("HasTypeZ", [v; t])
       let mk_HasTypeFuel f v t   = mkApp ("HasTypeFuel", [f; v; t])
       let mk_HasTypeWithFuel f v t =
         match f with
         | None   -> mk_HasType v t
         | Some f -> mk_HasTypeFuel f v t

       Why this approach?

       1. Dependent Types: F* types can depend on terms. If types were SMT sorts, term-dependent types would be impossible to express.
       2. Universe Polymorphism: F* has a hierarchy of universes. A single sort allows polymorphic reasoning.
       3. Subtyping: Refinement types create implicit subtyping relationships easier to encode with predicates.

       2.2 Base Type Encoding

       Primitive F* types map to predicates over Term_sort. From EncodeTerm.fst (lines 156-180):

       let mk_tester (n:string) (t:term) = mkApp("is-" ^ n, [t])
       let boxIntFun   = "BoxInt"
       let boxBoolFun  = "BoxBool"  
       let boxStringFun = "BoxString"
       let boxRealFun  = "BoxReal"

       (* Encoding: bool becomes (BoxBool b) where b : Bool_sort *)
       let mk_BoxBool t  = mkApp(boxBoolFun, [t])
       let mk_BoxInt t   = mkApp(boxIntFun, [t])
       let mk_BoxString t = mkApp(boxStringFun, [t])
       let mk_BoxReal t  = mkApp(boxRealFun, [t])

       The boxing/unboxing strategy:
       - F* int values are encoded as (BoxInt i) where i : Int_sort
       - F* bool values are encoded as (BoxBool b) where b : Bool_sort
       - Unboxing retrieves the underlying SMT value: (IsInt (BoxInt i)) yields i

       2.3 Function Type Encoding

       Arrow types are encoded with the special Tm_arrow constructor. From EncodeTerm.fst (lines 217-223):

       let mk_term_projector_name lid (a:bv) = ...
       let mk_data_tester env l x = mkApp("is-" ^ (escape (string_of_lid l)), [x])

       Function application uses curried ApplyTT (term-term application):

       let mk_ApplyTT t1 t2 rng = mkApp'(Var "ApplyTT", [t1; t2]) rng
       let mk_Apply t args = List.fold_left (fun t arg -> mk_ApplyTT t (mkFreeV arg)) t args

       ---
       3. Term Encoding

       3.1 The Main Encoding Function

       The core term encoding is in FStarC.SMTEncoding.EncodeTerm.fst, function encode_term (lines 520-900+). The signature:

       val encode_term : term -> env_t -> (term & decls_t)

       Key cases:

       Variables (lines 540-560):
       | Tm_bvar x -> 
           (* Look up in environment *)
           lookup_bvar_binding env x
       | Tm_name x ->
           lookup_term_var env x
       | Tm_fvar fv ->
           lookup_free_var env fv.fv_name

       Applications (lines 620-720):
       | Tm_app {hd; args} ->
           let head, decls = encode_term hd env in
           let args_encoded, arg_decls = encode_args args env in
           mk_Apply head args_encoded, decls @ arg_decls

       Abstractions (lines 750-820):
       | Tm_abs {bs; body; rc_opt} ->
           (* For abstractions, we create a fresh function symbol *)
           let fsym = varops.fresh env.current_module_name "Tm_abs" in
           let f = mkFreeV (mk_fv (fsym, Term_sort)) in
           (* Encode the body with binders in scope *)
           let vars, guards, env', binder_decls, _ = encode_binders None bs env in
           let body_encoded, body_decls = encode_term body env' in
           (* Create axiom: forall xs. f xs = body *)
           ...

       3.2 Literal Encoding

       From EncodeTerm.fst (lines 580-620):

       | Tm_constant (Const_int (n, None)) ->
           mk_BoxInt (mkInteger n), []
       | Tm_constant (Const_bool true) ->
           mk_BoxBool mkTrue, []
       | Tm_constant (Const_bool false) ->
           mk_BoxBool mkFalse, []
       | Tm_constant (Const_string (s, _)) ->
           mk_BoxString (mk_String_const s), []

       3.3 Match Encoding

       Pattern matching is encoded through data constructor testers and projectors. From Encode.fst (lines 1313-1400):

       (* For data constructor D with fields f1...fn *)
       let ddconstrsym = ... (* D's symbol *)
       let fields = names |> List.mapi (fun n x ->
           { field_name = mk_term_projector_name d x;
             field_sort = Term_sort;
             field_projectible = n >= n_tps || injective_type_params })

       Match elimination generates:
       1. Tester: (is-Cons x) checks if x was built with Cons
       2. Projectors: (Cons_hd x) extracts the head field

       ---
       4. Fuel Encoding for Recursion

       4.1 The Fuel Mechanism

       Recursive function unfolding is controlled by "fuel" - a synthetic resource that limits how many times Z3 can unfold a recursive definition. This prevents infinite loops in the SMT solver.

       From FStarC.SMTEncoding.Encode.fst (lines 977-1000):

       let encode_rec_lbdefs bindings typs toks env =
         (* Create fuel variable *)
         let fuel = mk_fv (varops.fresh env.current_module_name "fuel", Fuel_sort) in
         let fuel_tm = mkFreeV fuel in
         
         (* For each recursive function f, create fuel-instrumented version g *)
         let gtoks, env = toks |> List.fold_left (fun (gtoks, env) (fvb, univ_names) ->
           let g = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented") in
           let gtok = varops.new_fvar (Ident.lid_add_suffix flid "fuel_instrumented_token") in
           ...
         )

       4.2 Fuel Sort and Constructors

       From Term.fst (lines 77-84):

       (* Fuel is a natural number encoded as:
          ZFuel         -- zero fuel
          SFuel(f)      -- successor (one more unfolding allowed)
          MaxFuel       -- the initial fuel amount
       *)
       let n_fuel (n:int) = 
         let rec aux n = if n = 0 then mkApp("ZFuel", []) 
                         else mkApp("SFuel", [aux (n-1)])
         in aux n

       4.3 Recursive Function Axioms

       For a recursive function f, the encoding generates (from Encode.fst lines 1063-1090):

       (* Equation with fuel guard *)
       let eqn_g = Util.mkAssume(
         mkForall' rng
           ([[gsapp]],                           (* Pattern *)
            Some 0,                               (* Weight = 0, controlled by fuel *)
            fuel::(univ_vars@vars),              (* Bound variables *)
            mkImp(guard, mkEq(gsapp, body_tm))), (* fuel-guarded equation *)
         Some "Equation for fuel-instrumented recursive function",
         "equation_with_fuel_" ^ g)

       (* Correspondence: f x = g MaxFuel x *)
       let eqn_f = Util.mkAssume(
         mkForall rng
           ([[app]], univ_vars@vars, mkEq(app, gmax)),
         Some "Correspondence of recursive function to instrumented version",
         "@fuel_correspondence_" ^ g)

       (* Fuel irrelevance: once you have enough fuel, more doesn't matter *)
       let eqn_g' = Util.mkAssume(
         mkForall rng
           ([[gsapp]], fuel::(univ_vars@vars),
            mkEq(gsapp, mk_g_app (Term.n_fuel 0::args))),
         Some "Fuel irrelevance",
         "@fuel_irrelevance_" ^ g)

       4.4 Initial Fuel Settings

       Controlled by command-line options. From Solver.fst (lines 251-260):

       let with_fuel_and_diagnostics settings label_assumptions =
           let n = settings.query_fuel in
           let i = settings.query_ifuel in
           [
             Util.mkAssume(mkEq(mkApp("MaxFuel", []), n_fuel n),
                           None, "@MaxFuel_assumption");
             Util.mkAssume(mkEq(mkApp("MaxIFuel", []), n_fuel i),
                           None, "@MaxIFuel_assumption");
             ...
           ]

       - --initial_fuel (default 2): Starting fuel for function unfolding
       - --max_fuel (default 8): Maximum fuel during retry
       - --initial_ifuel (default 1): Starting fuel for inductive type inversions
       - --max_ifuel (default 2): Maximum ifuel during retry

       ---
       5. Patterns and Triggers

       5.1 What Are Patterns?

       SMT patterns (triggers) control when quantified axioms are instantiated. Without patterns, the solver might instantiate axioms infinitely or miss critical instances.

       From Term.fsti (lines 66-72), patterns are lists of lists of terms:

       type qop = | Forall | Exists

       (* In Quant constructor: *)
       | Quant of qop &
                  list (list term) &  (* Patterns: disjunction of conjunctions *)
                  option int &        (* Optional weight *)
                  list sort &         (* Bound variable sorts *)
                  term                (* Quantifier body *)

       5.2 Pattern Generation Strategy

       F* generates patterns based on the structure of axioms. From EncodeTerm.fst (lines 380-420):

       (* For typing axioms: pattern on the typing judgment itself *)
       let ty_pred = mk_HasType vapp encoded_res_t in
       let typingAx = Util.mkAssume(
         mkForall rng ([[vapp]], univ_fvs@vars, mkImp(guard, ty_pred)),
         Some "free var typing",
         "typing_" ^ vname)

       (* For equations: pattern on the application *)
       let eqn = Util.mkAssume(
         mkForall rng ([[app]], vars, mkEq(app, body)),
         Some "Equation",
         "equation_" ^ vname)

       5.3 Multi-Pattern Disjunctions

       Some axioms need multiple patterns for bidirectional reasoning. From Encode.fst (lines 600-615):

       let name_tok_corr_formula vtok_app =
         mkForall rng
           ([[vtok_app]; [vapp]],  (* TWO patterns: token-form OR expanded-form *)
            vars,
            mkEq(vtok_app, vapp))

       This allows rewriting in both directions:
       - ApplyTT (f@tok) x --> f x
       - f x --> ApplyTT (f@tok) x

       5.4 The NoHoist Guard

       Some typing axioms are too eager. F* uses NoHoist to prevent Z3's simplifier from hoisting them out of their guard. From Encode.fst (lines 632-642):

       mkForall rng
         ([[vtok_app_r]],
          [ff],
          mkAnd(Term.mk_NoHoist f tok_typing,  (* Prevent hoisting *)
                name_tok_corr_formula vapp))

       ---
       6. Quantifier Instantiation Strategy

       6.1 E-Matching

       Z3 uses E-matching to instantiate quantifiers. When a ground term matches a pattern, the quantifier is instantiated with that term.

       F*'s encoding is designed to work well with E-matching:
       1. Function symbols in patterns: Patterns contain uninterpreted function applications
       2. Shallow patterns: Patterns are typically one level deep
       3. Multiple patterns for coverage: Important axioms have multiple trigger options

       6.2 Quantifier Weights

       F* assigns weights to control instantiation priority. From Encode.fst (line 1074):

       mkForall' rng
         ([[gsapp]],
          Some 0,        (* Weight = 0: highest priority, but controlled by fuel *)
          fuel::vars,
          body)

       Weight 0 means "instantiate eagerly" but the fuel guard prevents runaway instantiation.

       6.3 Skolemization

       Existential quantifiers are Skolemized. From EncodeTerm.fst (conceptually):

       (* exists x. P(x) becomes P(sk_x) where sk_x is a fresh constant *)

       ---
       7. Query Pruning Heuristics

       7.1 The Pruning Problem

       F* accumulates thousands of axioms during type-checking. Sending all of them to Z3 is slow and can cause timeouts. The pruning module (FStarC.SMTEncoding.Pruning.fst) selects only relevant axioms.

       7.2 Pruning State Structure

       From Pruning.fst (lines 56-76):

       type pruning_state = {
         defs_and_decls: list decl;
         defs_and_decls_map: PSMap.t decl;
         macro_freenames: PSMap.t (list string);  (* Macro body free names *)
         trigger_to_assumption: PSMap.t (list assumption);  (* Symbol -> axioms *)
         assumption_to_triggers: PSMap.t assumption_remaining_triggers;
         assumption_name_map: PSMap.t decl;
         ambients: list string;         (* Always-included axioms *)
         extra_roots: list assumption;  (* Additional starting points *)
         pruned_ambients: list string   (* Debug: what was pruned *)
       }

       7.3 The Pruning Algorithm

       From Pruning.fst (lines 482-515):

       let rec scan (ds: list assumption) : st unit =
         let! ctxt = get in
         (* Collect free names from all assumptions *)
         let new_syms = List.collect (fun a -> 
           List.collect macro_expand
             (List.map (mk_sym a.assumption_name)
               (elems (assumption_free_names a)))) ds in

         (* Find axioms waiting on these symbols *)
         match! trigger_pending_assumptions new_syms with
         | [] -> return ()  (* Fixed point reached *)
         | triggered ->
             (* Mark newly reachable axioms and continue *)
             let! to_scan = ... in
             scan to_scan

       Algorithm:
       1. Start with query goals as roots
       2. Find all free symbols in roots
       3. Find axioms whose patterns mention those symbols
       4. Add those axioms to reachable set
       5. Repeat until fixed point

       7.4 Excluded Symbols

       Some symbols are too common to be useful triggers. From Pruning.fst (lines 146-158):

       let exclude_names : RBSet.t string =
         from_list [
           "SFuel"; "ZFuel";
           "HasType"; "HasTypeZ"; "HasTypeFuel";
           "Valid"; "ApplyTT"; "ApplyTF";
           "Prims.lex_t"
         ]

       ---
       8. Z3 Interaction Protocol

       8.1 Process Management

       F* maintains a persistent Z3 process. From FStarC.SMTEncoding.Z3.fst (lines 224-293):

       type bgproc = {
           ask:      string -> string;
           refresh:  unit -> unit;
           restart:  unit -> unit;
           version:  unit -> string;
           ctxt:     SolverState.solver_state;
       }

       let bg_z3_proc =
           (* Manages background Z3 process *)
           let the_z3proc = mk_ref None in
           ...

       8.2 Query Protocol

       From Z3.fst (lines 438-490):

       let doZ3Exe log_file r fresh input label_messages queryid =
         let parse (z3out: string) =
           let lines = String.split ['\n'] z3out in
           let smt_output = smt_output_sections log_file r lines in
           (* Parse result, reason-unknown, unsat-core, statistics, labels *)
           ...
           match smt_output.smt_result with
           | ["unsat"]   -> UNSAT unsat_core
           | ["sat"]     -> SAT (labels, reason_unknown)
           | ["unknown"] -> UNKNOWN (labels, reason_unknown)
           | ["timeout"] -> TIMEOUT (labels, reason_unknown)
           | ["killed"]  -> KILLED

       8.3 Incremental Solving

       F* uses SMT-LIB2 incremental mode with push/pop. From Z3.fst (lines 397-430):

       let push msg =
         with_solver_state_unit SolverState.push;
         with_solver_state_unit (SolverState.give [Caption msg])

       let pop msg =
         with_solver_state_unit (SolverState.give [Caption msg]);
         with_solver_state_unit SolverState.pop

       let snapshot msg =
         let d = reading_solver_state SolverState.depth in
         push msg;
         d

       let rollback msg depth =
         (* Pop until we reach the target depth *)
         ...

       8.4 RLimit Translation

       Z3's rlimit controls resource usage. From Solver.fst (lines 243-248):

       let convert_rlimit (r : int) : int =
         let open FStar.Mul in
         if Misc.version_ge (Options.z3_version ()) "4.12.3" then
           500000 * r    (* Newer Z3: round number *)
         else
           544656 * r    (* Legacy: ~5 seconds at some point *)

       ---
       9. Counterexample Generation and Error Reporting

       9.1 Error Labels

       F* instruments queries with labels to identify failing subgoals. From FStarC.SMTEncoding.ErrorReporting.fst (lines 43-50):

       let fresh_label : Errors.error_message -> Range.t -> term -> label & term =
           fun message range t ->
               let l = incr __ctr; Format.fmt1 "label_%s" (show !__ctr) in
               let lvar = mk_fv (l, Bool_sort) in
               let label = (lvar, message, range) in
               let lterm = mkFreeV lvar in
               let lt = Term.mkOr(lterm, t) range in  (* label \/ goal *)
               label, lt

       The trick: (label_n \/ actual_goal). In a counterexample:
       - If label_n = false, then actual_goal must have failed
       - Z3 reports which labels are false in its model

       9.2 Goal Labeling

       From ErrorReporting.fst (lines 59-110):

       let label_goals use_env_msg r q =
           let rec aux default_msg ropt post_name_opt labels q =
             match q.tm with
             | App(Imp, [lhs; rhs]) ->
                 (* Only label the consequent *)
                 let labels, rhs = aux default_msg ropt post_name_opt labels rhs in
                 labels, mkImp(lhs, rhs)

             | App(And, conjuncts) ->
                 (* Label each conjunct *)
                 let labels, conjuncts = BU.fold_map (aux ...) labels conjuncts in
                 labels, Term.mk_and_l conjuncts q.rng

             | Quant(Forall, pats, iopt, sorts, body) ->
                 (* Descend into body *)
                 let labels, body = aux default_msg ropt post_name_opt labels body in
                 labels, Term.mk (Quant(Forall, pats, iopt, sorts, body)) q.rng

             | _ -> (* Atomic goal: add label *)
                 let lab, q = fresh_label default_msg ropt q.rng q in
                 lab::labels, q
           in
           aux (Errors.mkmsg "Assertion failed") None None [] q

       9.3 Detailed Error Analysis

       When a proof fails, F* can isolate which subgoal failed. From ErrorReporting.fst (lines 313-380):

       let detail_errors hint_replay env all_labels askZ3 =
           let elim labs = 
             (* Assume all labels are true, effectively disabling them *)
             labs |> List.map (fun (l, _, _) ->
               Assume { assumption_term = mkEq(mkFreeV l, mkTrue); ... })
           in

           (* Try each label in isolation *)
           let rec linear_check eliminated errors active =
               match active with
               | [] -> (* Return results *)
                   List.map (fun x -> x, true) eliminated @
                   List.map (fun x -> x, false) errors
               | hd::tl ->
                   let decls = elim (eliminated @ errors @ tl) in
                   let result = askZ3 decls in  (* Only hd is active *)
                   match result.z3result_status with
                   | UNSAT _ -> linear_check (hd::eliminated) errors tl
                   | _ -> linear_check eliminated (hd::errors) tl
           in
           linear_check [] [] all_labels

       ---
       10. Timeout Handling and Retry Strategies

       10.1 Query Settings

       From Solver.fst (lines 217-234):

       type query_settings = {
           query_env: env_t;
           query_decl: decl;
           query_name: string;
           query_index: int;
           query_range: Range.t;
           query_fuel: int;
           query_ifuel: int;
           query_rlimit: int;
           query_hint: option UC.unsat_core;
           query_errors: list errors;
           query_all_labels: error_labels;
           query_suffix: list decl;
           query_hash: option string;
           query_can_be_split_and_retried: bool;
           query_term: Syntax.term;
           query_record_hints: bool;
       }

       10.2 Fuel Escalation

       When a query fails, F* tries with more fuel. From Solver.fst (lines 851-895):

       let make_solver_configs can_split is_retry env all_labels query query_term suffix =
           let default_settings = {
               query_fuel = Options.initial_fuel();
               query_ifuel = Options.initial_ifuel();
               query_rlimit = rlimit;
               ...
           } in

           (* Generate configurations with increasing fuel *)
           let fuel_settings =
             if Options.max_fuel() > Options.initial_fuel() then
               [{ default_settings with
                  query_fuel = Options.max_fuel();
                  query_ifuel = Options.max_ifuel() }]
             else []
           in
           ...

       10.3 Query Splitting

       Complex queries can be split into subgoals. From Solver.fst (lines 433-436):

       if settings.query_can_be_split_and_retried
       then raise SplitQueryAndRetry
       else (* Report all labels as potential failures *)

       10.4 Hint System

       F* can record and replay successful proof strategies. From Solver.fst (lines 70-112):

       let initialize_hints_db filename refresh =
           recorded_hints := [];
           let val_filename = Options.hint_file_for_src norm_src_filename in
           match read_hints val_filename with
           | HintsOK hints ->
               replaying_hints := Some hints.hints
           | MalformedJson -> ...
           | UnableToOpen -> ...

       let record_hint settings z3result =
           if not (Options.record_hints()) then () else
           match z3result.z3result_status with
           | UNSAT unsat_core ->
               store_hint { hint_name = settings.query_name;
                            hint_index = settings.query_index;
                            fuel = settings.query_fuel;
                            ifuel = settings.query_ifuel;
                            unsat_core = unsat_core;
                            ... }

       ---
       11. Debugging Failed Proofs

       11.1 Command-Line Options

       Key debugging options:
       - --query_stats: Show detailed timing and fuel usage
       - --detail_errors: Isolate failing subgoals
       - --detail_hint_replay: Debug hint replay failures
       - --log_queries: Write SMT queries to files
       - --z3rlimit N: Increase timeout (in abstract units)
       - --fuel N / --ifuel N: Increase unfolding limits

       11.2 Query Logging

       From Z3.fst (lines 55-100):

       let query_logging =
           let write_to_log fresh str =
             if fresh
             then write_to_new_log str
             else append_to_log str
           in
           { set_module_name = ...; write_to_log = ...; close_log = ... }

       Log files are named queries-ModuleName.smt2 and contain:
       - All declarations and axioms
       - The negated goal
       - (check-sat) and (get-info) commands

       11.3 Understanding "Unknown" Results

       From Solver.fst (lines 390-416):

       let incomplete_count, canceled_count, unknown_count, z3_overflow_bug_count =
         List.fold_left (fun (ic, cc, uc, bc) err ->
           let err = BU.substring_from err.error_reason 
                       (String.length "unknown because ") in
           match () with
           | _ when BU.starts_with err "(incomplete" ->
               (ic + 1, cc, uc, bc)  (* Z3 gave up *)
           | _ when BU.starts_with err "canceled" || 
                    BU.starts_with err "(resource" ||
                    BU.starts_with err "timeout" ->
               (ic, cc + 1, uc, bc)  (* Timeout *)
           | _ when BU.starts_with err "Overflow" ->
               (ic, cc, uc, bc + 1)  (* Z3 bug *)
           | _ -> (ic, cc, uc + 1, bc)
         ) (0, 0, 0, 0) settings.query_errors

       Interpreting results:
       - incomplete: Z3 gave up on quantifier instantiation. Try adding more fuel or explicit lemma applications.
       - canceled/timeout/resource limits reached: Increase --z3rlimit.
       - Overflow: Z3 internal bug. Try --split_queries.

       11.4 SMT Profiling

       With --print_z3_statistics, F* reports:
       - rlimit-count: Resources consumed
       - Modules contributing axioms to the proof
       - Specific axiom names in the unsat core

       From Solver.fst (lines 556-656), the unsat core parsing extracts F* source names from Z3 axiom names.

       ---
       12. Advanced Topics

       12.1 Universe Encoding

       F* universes map to SMT terms. From EncodeTerm.fst:

       let encode_univ_name (u:univ_name) =
         let uv = mk_fv (Ident.string_of_id u, univ_sort) in
         uv, mkFreeV uv

       Universe constraints become SMT inequalities.

       12.2 Effectful Computation Encoding

       For SMT-reifiable effects, F* encodes their reification. From Util.fst (lines 117-138):

       let is_smt_reifiable_effect en l =
         let l = TcEnv.norm_eff_name en l in
         TcEnv.is_reifiable_effect en l &&
         not (l |> TcEnv.get_effect_decl en |> U.is_layered)

       Only non-layered reifiable effects (like STATE from DM4F) get SMT encoding.

       12.3 Injectivity and Constructor Axioms

       For inductive types, F* generates (from Encode.fst lines 1190-1240):

       1. Inversion axiom: If HasType x (T args), then x is one of the constructors
       2. Typing intro: Constructor application has the right type
       3. Subterm ordering: Constructor arguments precede the constructed term (for termination)

       ---
       Summary

       F*'s SMT encoding is a sophisticated translation from dependent types to first-order logic:

       1. Single Term Sort: All values inhabit Term_sort; types become predicates
       2. Fuel Mechanism: Controls recursive unfolding to ensure termination
       3. Pattern Strategy: Careful trigger selection for efficient E-matching
       4. Pruning: Transitive closure over symbol dependencies
       5. Incremental Solving: Persistent Z3 process with push/pop
       6. Error Localization: Label instrumentation identifies failing subgoals
       7. Hint System: Record/replay successful proof strategies

       The encoding balances expressiveness (dependent types, effects, universes) with SMT solver efficiency (patterns, fuel, pruning). Understanding this encoding is essential for debugging F* proofs and writing SMT-friendly specifications.
  ⎿  Done (17 tool uses · 129.0k tokens · 3m 44s)

● elite-bug-hunter(F* Ch10: Tactics System)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering THE TACTICS SYSTEM.

       Explore /home/grigory/Downloads/FStar/src/tactics/ extensively.

       Focus on:
       1. Read FStarC.Tactics.V2.Basic.fst completely (115KB) - document V2 tactics
       2. Read FStarC.Tactics.V1.Basic.fst (90KB) - compare V1 tactics
       3. Read FStarC.Tactics.InterpFuns.fst (113KB) - document tactic interpretation
       4. Read FStarC.Tactics.Monad.fst - document the tactic monad
       5. Read FStarC.Tactics.Embedding.fst - document embedding
       6. Read FStarC.Tactics.CtrlRewrite.fst - document rewriting
       7. Read FStarC.Tactics.Hooks.fst - document hooks

       Your chapter should include:
       - The tactic monad (proofstate manipulation)
       - V1 vs V2 API differences
       - Built-in tactics (apply, intro, rewrite, etc.)
       - Goal management
       - Proof state inspection
       - Term quoting and antiquoting
       - Writing custom tactics
       - Debugging tactics
       - Performance considerations
       - Examples of useful tactic patterns

       Read at least 8 files. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have read all the key files. Let me write a comprehensive documentation chapter on F*'s Tactics System.

       ---
       F* TACTICS SYSTEM: A COMPREHENSIVE REFERENCE

       1. Introduction and Architecture Overview

       The F* Tactics System provides a metaprogramming facility allowing users to write proof scripts that manipulate proof goals and construct proof terms programmatically. Unlike traditional tactics systems, F* tactics are written in the same language as the object programs
       and can be verified themselves.

       The tactics implementation spans several key modules in /home/grigory/Downloads/FStar/src/tactics/:

       | File                           | Size  | Purpose                              |
       |--------------------------------|-------|--------------------------------------|
       | FStarC.Tactics.Monad.fst       | 14KB  | The tactic monad and core operations |
       | FStarC.Tactics.Types.fst       | 5KB   | Proofstate, goal, and control types  |
       | FStarC.Tactics.V2.Basic.fst    | 116KB | V2 built-in tactic implementations   |
       | FStarC.Tactics.V1.Basic.fst    | 90KB  | V1 built-in tactics (deprecated)     |
       | FStarC.Tactics.Interpreter.fst | 17KB  | Tactic execution engine              |
       | FStarC.Tactics.InterpFuns.fst  | 113KB | Primitive step registration          |
       | FStarC.Tactics.Embedding.fst   | 23KB  | Term embedding/unembedding           |
       | FStarC.Tactics.CtrlRewrite.fst | 16KB  | Controlled rewriting combinator      |
       | FStarC.Tactics.Hooks.fst       | 40KB  | VC preprocessing with tactics        |

       ---
       2. The Tactic Monad

       2.1 Core Type Definition

       The tactic monad is defined in /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fsti:30-31:

       (* Type of tactics *)
       type tac (a:Type0) : Type0 =
         ref proofstate -> a

       This is a state monad with mutable state (using ref proofstate) for efficiency. The monad instance is defined at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:127-130:

       let ret (x:'a) : tac 'a =
         fun _ -> x

       let bind (t1:tac 'a) (t2:'a -> tac 'b) : tac 'b =
         fun ps ->
           let x = t1 ps in
           t2 x ps

       instance monad_tac : monad tac = {
           return = ret;
           bind   = bind;
       }

       2.2 Running Tactics

       Tactics are executed via the run function at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:111-114:

       let run (t:tac 'a) (ps:proofstate) : __result 'a =
         let ps = mk_ref ps in
         let x = t ps in
         Success (x, !ps)

       The run_safe variant catches exceptions:

       let run_safe t ps =
           run t ps

       2.3 Exception Handling

       Tactics can fail using the fail function, which raises a TacticFailure exception at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:150-156:

       let fail_doc (msg:error_message) =
         fun ps ->
               if !dbg_TacFail then
                 do_dump_proofstate (!ps) ("TACTIC FAILING: " ^ renderdoc (hd msg));
               raise <| TacticFailure (msg, None)

       let fail msg = fail_doc [text msg]

       The catch combinator provides exception recovery with UF graph rollback at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:158-170:

       let catch (t : tac 'a) : tac (either exn 'a) =
           mk_tac (fun ps ->
                   let idtable = !ps.main_context.identifier_info in
                   let tx = UF.new_transaction () in
                   try
                     let Success (a, q) = run t ps in
                     UF.commit tx;
                     Success (Inr a, q)
                   with | m ->
                       UF.rollback tx;
                       ps.main_context.identifier_info := idtable;
                       Success (Inl m, ps)
                  )

       Key insight: On failure, the unification graph is rolled back to prevent partial modifications from polluting the state.

       ---
       3. Proofstate Structure

       3.1 Goal Type

       A goal represents a typing judgment to be proven. Defined at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Types.fsti:39-46:

       //A goal is typically of the form
       //    G |- ?u : t
       // where context = G
       //       witness = ?u (although more generally, witness is a partial solution)
       //       goal_ty = t
       type goal = {
           goal_main_env: env;
           goal_ctx_uvar : ctx_uvar;
           opts    : FStarC.Options.optionstate; // option state for this particular goal
           is_guard : bool; // Marks whether this goal arose from a guard during tactic runtime
           label : string; // A user-defined description
       }

       3.2 Proofstate Type

       The proofstate contains all information needed during tactic execution. Defined at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Types.fsti:58-91:

       type proofstate = {
           main_context : env;          //the shared top-level context for all goals
           all_implicits: implicits ;   //all the implicits currently open, partially resolved

           goals        : list goal;    //all the goals remaining to be solved
           smt_goals    : list goal;    //goals that have been deferred to SMT

           // Read-only, for splice tactics
           splice_quals : list qualifier;
           splice_attrs : list attribute;

           depth        : int;          //depth for tracing and debugging
           __dump       : proofstate -> string -> unit; // callback to dump proofstate
           psc          : PO.psc;       //primitive step context where we started execution
           entry_range  : Range.t;      //position of entry, set by the user
           guard_policy : guard_policy; //what to do with guards arising during tactic exec
           freshness    : int;          //a simple freshness counter for the fresh tactic
           tac_verb_dbg : bool;         //whether to print verbose debugging messages

           local_state  : PSMap.t term; // local metaprogram state

           urgency      : int;          // Used by emacs to decide whether to pop open a buffer
           dump_on_failure : bool;      // Whether to dump proofstate on failure
       }

       3.3 Guard Policy

       The guard_policy type controls how verification conditions arising during tactic execution are handled. Defined at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Types.fsti:47-53:

       type guard_policy =
           | Goal      // Turn guard into a goal
           | SMT       // Push to SMT goals (async)
           | SMTSync   // Send to SMT synchronously
           | Force     // Force discharge without SMT
           | ForceSMT  // Force discharge with SMT
           | Drop      // Unsound: drop the guard

       ---
       4. Goal Management

       4.1 Basic Goal Operations

       The monad provides several primitives for goal manipulation at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:232-304:

       (* Get current goal *)
       let cur_goal : tac goal =
         bind cur_goals (function
         | [] -> fail "No more goals"
         | hd::tl -> ...)

       (* Set the current set of goals / SMT goals *)
       let set_goals (gs:list goal) : tac unit =
           bind get (fun ps ->
           set ({ ps with goals = gs }))

       (* Add goals to the beginning of the list *)
       let add_goals (gs:list goal) : tac unit =
           bind get (fun ps ->
           check_valid_goals gs;
           set ({ps with goals=gs@ps.goals}))

       (* Add goals to the end of the list *)
       let push_goals (gs:list goal) : tac unit =
           bind get (fun ps ->
           set ({ps with goals=ps.goals@gs}))

       (* Drop the first goal *)
       let dismiss : tac unit =
           bind get (fun ps ->
           set ({ps with goals=List.tl ps.goals}))

       4.2 Focus and Divide

       The focus combinator runs a tactic on just the first goal at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:443-445:

       let focus (f:tac 'a) : tac 'a =
           let! (a, _) = divide 1 f (return ()) in
           return a

       The divide combinator splits goals and runs separate tactics at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:420-439:

       let divide (n:int) (l : tac 'a) (r : tac 'b) : tac ('a & 'b) =
         let! p = get in
         let! lgs, rgs =
           try return (List.splitAt n p.goals) with
           | _ -> fail "divide: not enough goals"
         in
         let lp = { p with goals = lgs; smt_goals = [] } in
         set lp;!
         let! a = l in
         let! lp' = get in
         let rp = { lp' with goals = rgs; smt_goals = [] } in
         set rp;!
         let! b = r in
         let! rp' = get in
         let p' = { rp' with goals = lp'.goals @ rp'.goals;
                             smt_goals = lp'.smt_goals @ rp'.smt_goals @ p.smt_goals }
         in
         set p';!
         remove_solved_goals;!
         return (a, b)

       4.3 Creating New Goals

       New goals are created via unification variables at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:311-325:

       let new_uvar (reason:string) (env:env) (typ:typ)
                    (sc_opt:option should_check_uvar)
                    (uvar_typedness_deps:list ctx_uvar)
                    (rng:Range.t)
         : tac (term & ctx_uvar) =
           let should_check =
             match sc_opt with
             | Some sc -> sc
             | _ -> Strict
           in
           let u, ctx_uvar, g_u =
               Env.new_tac_implicit_var reason rng env typ should_check uvar_typedness_deps None false
           in
           bind (add_implicits (Listlike.to_list g_u.implicits)) (fun _ ->
           ret (u, fst ctx_uvar))

       ---
       5. V2 Built-in Tactics

       5.1 Introduction Tactics

       intro introduces a binder from an arrow type. At /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:739-788:

       (*
         [intro]:
         Initial goal: G |- ?u : (t -> t')
         Next goal:  `G, x:t |- ?v : t'`
         with `?u := (fun (x:t) -> ?v @ [NM(x, 0)])`
       *)
       let intro () : tac RD.binding = wrap_err "intro" <| (
           let! goal = cur_goal in
           match arrow_one_whnf (goal_env goal) (goal_type goal) with
           | Some (env', b, c) ->
               let typ' = U.comp_result c in
               let! body, ctx_uvar =
                 new_uvar "intro" env' typ'
                          (Some (should_check_goal_uvar goal))
                          (goal_typedness_deps goal)
                          (rangeof goal) in
               let sol = U.abs [b] body (Some (U.residual_comp_of_comp c)) in
               set_solution goal sol ;!
               let g = mk_goal env' ctx_uvar goal.opts goal.is_guard goal.label in
               replace_cur g ;!
               return (binder_to_binding b)
           | None ->
               fail1 "goal is not an arrow (%s)" (tts (goal_env goal) (goal_type goal))
           )

       intros introduces multiple binders at once at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:792-819.

       5.2 Application Tactics

       t_apply applies a term to solve the current goal at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1022-1080:

       let t_apply (uopt:bool) (only_match:bool) (tc_resolved_uvars:bool) (tm:term) : tac unit = wrap_err "apply" <| (
           let! goal = cur_goal in
           let e = goal_env goal in
           let! tm, typ, guard = __tc e tm in
           let typ = bnorm e typ in
           let! uvs = try_unify_by_application (Some should_check) only_match e typ (goal_type goal) (rangeof goal) in
           let w = List.fold_right (fun (uvt, q, _) w -> U.mk_app w [(uvt, q)]) uvs tm in
           solve' goal w ;!
           // ... add subgoals for uvars
           )

       t_apply_lemma applies a lemma (function with Lemma effect) at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1099-1211.

       5.3 Exact and Solve

       t_exact provides an exact solution to the goal at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:927-940:

       let t_exact try_refine set_expected_typ tm : tac unit = wrap_err "exact" <| (
           match! catch (__exact_now set_expected_typ tm) with
           | Inr r -> return r
           | Inl e when not (try_refine) -> traise e
           | Inl e ->
             // try refine_intro first
             match! catch (norm [NormSteps.Delta] ;! refine_intro () ;! __exact_now set_expected_typ tm) with
             | Inr r -> return r
             | Inl _ -> traise e)

       5.4 Rewriting Tactics

       rewrite rewrites using an equality hypothesis at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1224-1263:

       let rewrite (hh:RD.binding) : tac unit = wrap_err "rewrite" <| (
           let! goal = cur_goal in
           let bv = (binding_to_binder hh).binder_bv in
           match split_env bv (goal_env goal) with
           | Some (e0, bv, bvs) ->
             match destruct_eq e0 bv.sort with
             | Some (x, e) ->
               match (SS.compress x).n with
               | Tm_name x ->
                 let s = [NT(x, e)] in
                 let t = goal_type goal in
                 let t' = SS.subst s t in
                 // ... create new goal with substituted type
           )

       grewrite generalized rewriting at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1271-1304 creates an equality goal.

       5.5 Reflexivity

       t_trefl proves reflexive equalities at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1463-1595:

       let _t_trefl (allow_guards:bool) (l : term) (r : term) : tac unit =
         let! g = cur_goal in
         let attempt (l : term) (r : term) : tac bool =
           match! do_unify_maybe_guards allow_guards must_tot (goal_env g) l r with
           | None -> return false
           | Some guard ->
             solve' g U.exp_unit ;!
             // handle guard based on allow_guards flag
         in
         match! attempt l r with
         | true -> return ()
         | false ->
           // normalize and retry
           let norm = N.normalize [...] (goal_env g) in
           match! attempt (norm l) (norm r) with
           | true -> return ()
           | false -> fail2 "cannot unify (%s) and (%s)" ls rs

       5.6 Normalization

       norm normalizes the goal type at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:847-854:

       let norm (s : list NormSteps.norm_step) : tac unit =
           let! goal = cur_goal in
           let steps = [Env.Reify; Env.DontUnfoldAttr [PC.tac_opaque_attr]]@(Cfg.translate_norm_steps s) in
           let t = normalize steps (goal_env goal) (goal_type goal) in
           replace_cur (goal_with_type goal t)

       5.7 Destruct

       t_destruct destructs an inductive value creating branches at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Basic.fst:1868-2017. This is a complex tactic that:
       1. Type-checks the scrutinee
       2. Looks up the inductive type's constructors
       3. Creates a goal for each constructor branch
       4. Builds a match expression as the solution

       ---
       6. V1 vs V2 API Differences

       F* provides two versions of the tactics API. V2 is the current recommended version.

       6.1 Key Differences

       1. Reflection Data Types: V2 uses FStarC.Reflection.V2.Data, V1 uses FStarC.Reflection.V1.Data
       2. Binding Representation:
         - V1: Uses binder directly
         - V2: Uses RD.binding which wraps bv information
       3. Monadic Style:
         - V1 at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V1.Basic.fst:63-65:
         let ret #a (x:a) : tac a = return x
       let bind #a #b : tac a -> (a -> tac b) -> tac b = ( let! )
       let idtac : tac unit = return ()
         - V2 uses the monad class directly with let! and return from FStarC.Class.Monad
       4. Term Normalization: V1 normalizes whnf on destruct_eq, V2 does not by default.
       5. Error Handling: V2 has richer error messages using fail_doc with structured documents.

       ---
       7. Tactic Interpretation

       7.1 Primitive Step Registration

       Tactics are registered as primitive reduction steps. From /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.InterpFuns.fst:72-105:

       let mk_tac_step_1 univ_arity nm f nbe_f : PO.primitive_step =
         let lid = builtin_lid nm in
         set_auto_reflect 1 <|
           PO.mk2' univ_arity lid
             (fun a ps -> Some (run_wrap nm (f a) ps))
             (fun a ps -> Some (run_wrap nm (nbe_f a) ps))

       The auto_reflect setting allows tactics to be called directly without explicit reflection.

       7.2 Embedding and Unembedding

       The interpreter must convert between F* terms and OCaml values. From /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Interpreter.fst:114-174:

       let unembed_tactic_0 (eb:embedding 'b) (embedded_tac_b:term) (ncb:norm_cb) : tac 'b = fun ps ->
           let ps0 = !ps in
           let rng = embedded_tac_b.pos in

           (* First, reify it from Tac a into __tac a *)
           let embedded_tac_b = U.mk_reify embedded_tac_b (Some PC.effect_TAC_lid) in

           let tm = S.mk_Tm_app embedded_tac_b
                                [S.as_arg (embed rng ps ncb)]
                                 rng in

           let steps = [Env.Weak; Env.Reify; Env.UnfoldUntil delta_constant; 
                        Env.DontUnfoldAttr [PC.tac_opaque_attr];
                        Env.Primops; Env.Unascribe; Env.Tactics] in

           let norm_f = if Options.tactics_nbe ()
                        then NBE.normalize
                        else N.normalize_with_primitive_steps
           in
           let result = norm_f (primitive_steps ()) steps ps0.main_context tm in

           match unembed result ncb with
           | Some b -> b
           | None ->
               (* The tactic got stuck, provide helpful error message *)
               Errors.raise_error ps0.main_context Errors.Fatal_TacticGotStuck [...]

       7.3 Proofstate Embedding

       The proofstate is embedded as a lazy value at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Embedding.fst:134-145:

       instance e_ref_proofstate : embedding ref_proofstate = e_lazy Lazy_ref_proofstate fstar_tactics_ref_proofstate.t
       instance e_proofstate : embedding proofstate = e_lazy Lazy_proofstate fstar_tactics_proofstate.t
       instance e_goal       : embedding goal       = e_lazy Lazy_goal fstar_tactics_goal.t

       ---
       8. Controlled Rewriting

       The ctrl_rewrite tactic provides fine-grained control over term rewriting. From /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.CtrlRewrite.fst:429-453:

       let ctrl_rewrite
           (dir : direction)
           (controller : controller_ty)
           (rewriter   : rewriter_ty)
         : tac unit
         = wrap_err "ctrl_rewrite" <| (
           let! ps = get in
           let g, gs = match ps.goals with
                       | g::gs -> g, gs
                       | [] -> failwith "no goals"
           in
           dismiss_all ;!
           let gt = (goal_type g) in
           let! gt' = do_ctrl_rewrite g dir controller rewriter (goal_env g) gt in
           push_goals gs ;!
           let g = goal_with_type g gt' in
           add_goals [g]
           )

       8.1 Control Flags

       The controller can return three flags at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Types.fsti:122-125:

       type ctrl_flag =
           | Continue  // Keep descending
           | Skip      // Skip this subterm
           | Abort     // Abort entire traversal

       8.2 Direction

       Rewriting can proceed top-down or bottom-up at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Types.fsti:127-129:

       type direction =
           | TopDown
           | BottomUp

       ---
       9. Hooks and VC Preprocessing

       The hooks module integrates tactics into verification condition preprocessing. From /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Hooks.fst:54-64:

       let run_tactic_on_typ
               (rng_tac : Range.t) (rng_goal : Range.t)
               (tactic:term) (env:Env.env) (typ:term)
                           : list goal // remaining goals
                           & term // witness
                           =
           let rng = range_of_rng (use_range rng_tac) (use_range rng_goal) in
           let ps, w = FStarC.Tactics.V2.Basic.proofstate_of_goal_ty rng env typ in
           let tactic_already_typed = false in
           let gs, _res = run_tactic_on_ps rng_tac rng_goal false e_unit () e_unit tactic tactic_already_typed ps in
           gs, w

       9.1 Polarity-Aware Traversal

       The by_tactic_interp function handles with_tactic markers based on polarity at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Hooks.fst:114-177:

       let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : tres =
           let hd, args = U.head_and_args t in
           match (U.un_uinst hd).n, args with
           | Tm_fvar fv, [(tactic, None); (assertion, None)]
                   when S.fv_eq_lid fv PC.by_tactic_lid ->
               match pol with
               | StrictlyPositive | Pos ->
                   let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
                   Simplified (FStarC.Syntax.Util.t_true, gs)
               | Neg ->
                   // In negative position, peel away tactics
                   Simplified (assertion, [])

       ---
       10. Writing Custom Tactics

       10.1 Basic Structure

       A custom tactic is a function returning tac 'a:

       let my_tactic () : Tac unit =
         let g = cur_goal () in
         let t = goal_type g in
         // ... manipulate the goal
         exact (`())

       10.2 Useful Patterns

       Sequencing with ;;!:
       let multi_step () : Tac unit =
         intro ();!
         norm [delta];!
         trivial ()

       Backtracking with or_else:
       let try_tactics () : Tac unit =
         or_else (fun () -> exact (`1))
                 (fun () -> exact (`2))

       Iteration over goals:
       let solve_all () : Tac unit =
         iter_goals (fun () -> trivial ())

       10.3 Debugging Tips

       1. Use dump to inspect the proofstate:
       dump "before intro"
       2. Enable debug flags:
       --debug Tac --debug TacUnify
       3. Set verbosity:
       set_dump_on_failure true

       ---
       11. Performance Considerations

       11.1 NBE vs Normalizer

       Tactics can run via the normalizer or NBE (Normalization by Evaluation). From /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Interpreter.fst:136-140:

       let norm_f = if Options.tactics_nbe ()
                    then NBE.normalize
                    else N.normalize_with_primitive_steps

       NBE is often faster for large terms. Enable with --tactics_nbe.

       11.2 Core Checking

       Goal registration for core checking can be expensive. At /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.Monad.fst:66-104:

       let register_goal (g:goal) =
         if not (Options.compat_pre_core_should_register()) then () else
         let env = goal_env g in
         if env.phase1 || Options.lax () then () else
         // ... expensive core type checking

       11.3 Guard Policy Selection

       Different guard policies have different performance characteristics:

       - Force: Fastest if guards are trivial
       - SMT: Defers to background SMT
       - SMTSync: Blocks until SMT finishes
       - Goal: Creates explicit goals (slowest but most control)

       ---
       12. Primitive Operations Reference

       The complete list of V2 primitives is registered at /home/grigory/Downloads/FStar/src/tactics/FStarC.Tactics.V2.Primops.fst:69-283:

       | Primitive        | Description                 |
       |------------------|-----------------------------|
       | get              | Get current proofstate      |
       | intro            | Introduce a binder          |
       | intros           | Introduce multiple binders  |
       | revert           | Revert a binder             |
       | clear            | Clear a binder from context |
       | rewrite          | Rewrite using equality      |
       | grewrite         | Generalized rewrite         |
       | t_exact          | Provide exact solution      |
       | t_apply          | Apply a term                |
       | t_apply_lemma    | Apply a lemma               |
       | t_trefl          | Reflexivity                 |
       | t_destruct       | Destruct inductive          |
       | norm             | Normalize goal              |
       | norm_term_env    | Normalize a term            |
       | dump             | Dump proofstate             |
       | tc               | Type-check a term           |
       | tcc              | Type-check returning comp   |
       | ctrl_rewrite     | Controlled rewriting        |
       | set_options      | Set options for goal        |
       | lget/lset        | Local state operations      |
       | alloc/read/write | Mutable references          |

       ---
       13. Summary

       The F* tactics system provides a powerful metaprogramming facility that:

       1. Uses a state monad (tac) with mutable proofstate
       2. Manages goals as typing judgments with unification variables
       3. Provides both V1 (deprecated) and V2 APIs
       4. Supports exception handling with UF graph rollback
       5. Integrates with the normalizer and NBE for execution
       6. Offers fine-grained control via guard policies and controlled rewriting
       7. Hooks into VC preprocessing for automatic proof search

       The architecture separates concerns cleanly:
       - Types.fst: Data structures
       - Monad.fst: Core monad operations
       - V2.Basic.fst: Tactic implementations
       - Interpreter.fst: Execution engine
       - Embedding.fst: Term conversion
       - Hooks.fst: Integration with type-checker
  ⎿  Done (17 tool uses · 171.1k tokens · 3m 13s)

● elite-bug-hunter(F* Ch11: Reflection API)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering REFLECTION AND META-PROGRAMMING.

       Explore /home/grigory/Downloads/FStar/src/reflection/ extensively.

       Focus on:
       1. Read FStarC.Reflection.V2.Builtins.fst completely - document V2 reflection
       2. Read FStarC.Reflection.V2.Embeddings.fst - document embeddings
       3. Read FStarC.Reflection.V2.NBEEmbeddings.fst - document NBE embeddings
       4. Read FStarC.Reflection.V1.Builtins.fst - compare V1 reflection
       5. Explore ulib/FStar.Reflection.*.fst files - understand the user-facing API

       Your chapter should include:
       - What reflection means in F*
       - Reifying terms at compile time
       - Inspecting and constructing terms
       - V1 vs V2 API differences
       - The embedding/reification cycle
       - Quotation and splicing
       - Use cases for reflection
       - Generating code via reflection
       - Type-safe meta-programming patterns
       - Limitations and caveats

       Read at least 10 files across src/reflection and ulib. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have gathered enough information to write the comprehensive documentation chapter. Let me present it:

       ---
       F* Reflection and Meta-Programming

       Chapter Overview

       This chapter provides a comprehensive guide to F*'s reflection and meta-programming facilities. These features allow programs to inspect and manipulate their own syntax at compile time, enabling powerful code generation, proof automation, and domain-specific language
       implementation.

       ---
       1. Introduction: What is Reflection in F*?

       Reflection in F* provides the ability to reify terms at compile time -- that is, to treat F* syntax as first-class data that can be inspected, analyzed, and constructed programmatically. This capability is fundamental to F*'s tactics and metaprogramming system.

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Builtins.fst:49-55:

       (* This file provides implementation for reflection primitives in F*.
        *
        * Users can be exposed to (mostly) raw syntax of terms when working in
        * a metaprogramming effect (such as TAC). These effects are irrelevant
        * for runtime and cannot, of course, be used for proof (where syntax
        * inspection would be completely inconsistent
        *)

       The key insight is that reflection operates at compile time only. Syntax inspection would be inconsistent in proofs because it would violate parametricity -- we want to prove properties about all terms of a given type, not about the specific syntax used to represent those
       terms.

       Core Concepts

       1. Abstract Types: The fundamental types like term, comp, binder, sigelt are abstract -- their internal representation is hidden from userspace code.
       2. View Types: For each abstract type, there is a corresponding "view" type (e.g., term_view, comp_view) that exposes the structure as an algebraic data type.
       3. Inspect/Pack Functions: These are the primitives that convert between abstract types and views:
         - inspect_*: Reveals the structure of an abstract value
         - pack_*: Constructs an abstract value from a view

       ---
       2. The Inspect/Pack Pattern

       The fundamental pattern in F* reflection is the inspect/pack duality. For every abstract syntax type, there is a view type and a pair of functions to convert between them.

       2.1 Term Views

       From /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Data.fsti:140-158:

       noeq
       type term_view =
         | Tv_Var    : v:namedv -> term_view
         | Tv_BVar   : v:bv -> term_view
         | Tv_FVar   : v:fv -> term_view
         | Tv_UInst  : v:fv -> us:universes -> term_view
         | Tv_App    : hd:term -> a:argv -> term_view
         | Tv_Abs    : bv:binder -> body:term -> term_view
         | Tv_Arrow  : bv:binder -> c:comp -> term_view
         | Tv_Type   : universe -> term_view
         | Tv_Refine : b:simple_binder -> ref:term -> term_view
         | Tv_Const  : vconst -> term_view
         | Tv_Uvar   : nat -> ctx_uvar_and_subst -> term_view
         | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> term_view
         | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> term_view
         | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> term_view
         | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> term_view
         | Tv_Unknown  : term_view // An underscore: _
         | Tv_Unsupp : term_view // failed to inspect, not supported

       Each constructor represents a different kind of F* term:

       | Constructor    | Description                         |
       |----------------|-------------------------------------|
       | Tv_Var         | A named variable (free in the term) |
       | Tv_BVar        | A bound variable (de Bruijn index)  |
       | Tv_FVar        | A fully-qualified top-level name    |
       | Tv_UInst       | An fvar with universe instantiation |
       | Tv_App         | Function application                |
       | Tv_Abs         | Lambda abstraction                  |
       | Tv_Arrow       | Function type (Pi type)             |
       | Tv_Type        | The Type universe                   |
       | Tv_Refine      | Refinement type                     |
       | Tv_Const       | Literal constant                    |
       | Tv_Uvar        | Unification variable                |
       | Tv_Let         | Let binding                         |
       | Tv_Match       | Pattern match                       |
       | Tv_AscribedT/C | Type/comp ascription                |
       | Tv_Unknown     | An underscore _                     |
       | Tv_Unsupp      | Unsupported syntax                  |

       2.2 Implementation of inspect_ln

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Builtins.fst:192-289:

       let rec inspect_ln (t:term) : term_view =
           let t = t |> SS.compress_subst in
           match t.n with
           | Tm_meta {tm=t} ->
               inspect_ln t

           | Tm_name bv ->
               Tv_Var bv

           | Tm_bvar bv ->
               Tv_BVar bv

           | Tm_fvar fv ->
               Tv_FVar fv

           | Tm_uinst (t, us) ->
             (match t.n with
              | Tm_fvar fv -> Tv_UInst (fv, us)
              | _ -> failwith "Reflection::inspect_ln: uinst for a non-fvar node")

           | Tm_ascribed {tm=t; asc=(Inl ty, tacopt, eq)} ->
               Tv_AscribedT (t, ty, tacopt, eq)

           // ... more cases ...

           | Tm_app {hd; args} ->
               let (a, q) = last args in
               let q' = inspect_aqual q in
               Tv_App (U.mk_app hd (init args), (a, q'))

       Key implementation details:

       1. Compression: Terms are first compressed to push delayed substitutions (SS.compress_subst)
       2. Meta-stripping: Tm_meta nodes are transparently stripped
       3. Unary representation: n-ary applications are converted to unary for the view
       4. Qualification handling: Argument qualifiers (implicit, explicit, etc.) are converted to aqualv

       2.3 Bijection Lemmas

       The reflection API guarantees that inspect and pack are inverses of each other. From /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Builtins.fsti:79-81:

       val pack_inspect_inv : (t:term) -> Lemma (~(Tv_Unsupp? (inspect_ln t)) ==> pack_ln (inspect_ln t) == t)
       val inspect_pack_inv : (tv:term_view) -> Lemma (inspect_ln (pack_ln tv) == tv)

       These lemmas are crucial for reasoning about code that manipulates terms via views -- they ensure the view abstraction is complete and consistent.

       2.4 Precedence Guarantees

       From /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Builtins.fsti:32-46:

       (** "Inspecting" a term: reveal one level of its syntax via the type
       term_view.

       Crucially, this function guarantees that the result "precedes" the
       argument, since it is morally exposing the subterms of [t] in the view.
       This can be justified by this model of [term] and [term_view]:

         type term = | Pack of term_view
         let pack_ln = Pack
         let inspect_ln (Pack tv) = tv

       Where inspect_ln would give exactly this guarantee on its result. *)

       val inspect_ln     : (t:term) -> tv:term_view{tv << t}

       The tv << t guarantee means that recursively inspecting a term will always terminate, which is essential for writing total functions that traverse syntax.

       ---
       3. The V1 vs V2 API

       F* provides two versions of the reflection API: V1 (legacy) and V2 (current). The key differences are:

       3.1 Variable Representation

       V1 (from /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V1.Data.fsti:96-114):
       noeq
       type term_view =
         | Tv_Var    : v:bv -> term_view       // Uses bv for both
         | Tv_BVar   : v:bv -> term_view       // named and bound vars
         | Tv_Refine : bv:bv -> sort:typ -> ref:term -> term_view
         | Tv_Let    : recf:bool -> attrs:(list term) -> bv:bv -> ty:typ -> def:term -> body:term -> term_view

       V2 (from /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Data.fsti:141-153):
       noeq
       type term_view =
         | Tv_Var    : v:namedv -> term_view   // Named variables are distinct
         | Tv_BVar   : v:bv -> term_view       // Bound variables (de Bruijn)
         | Tv_Refine : b:simple_binder -> ref:term -> term_view
         | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> term_view

       The V2 API makes a clearer distinction:
       - namedv: Named/free variables with unique identifiers
       - bv: Bound variables with de Bruijn indices
       - simple_binder: Binders without qualifiers or attributes (used in refinements and lets)

       3.2 Identifier Representation

       V1 uses a pair of string and range:
       type ident = string & range
       type univ_name = ident

       V2 uses the primitive ident type directly:
       (* In V2, ident is a primitive type *)
       type ident_view = string & range
       val inspect_ident : i:ident -> iv:ident_view{iv << i}
       val pack_ident    : ident_view -> ident

       3.3 Binder Views

       V1 exposes the bv directly:
       noeq
       type binder_view = {
         binder_bv : bv;
         binder_qual : aqualv;
         binder_attrs : list term;
         binder_sort : typ;
       }

       V2 uses sealed names (provably equal):
       noeq
       type binder_view = {
         sort   : typ;
         qual   : aqualv;
         attrs  : list term;
         ppname : ppname_t;  // sealed string
       }

       The V2 design is cleaner because:
       1. Pretty-print names are sealed, so all binders with the same structure are provably equal
       2. The sort is directly accessible, not buried in a bv
       3. Clear separation between the binding occurrence and the type

       ---
       4. The Embedding/Reification Cycle

       Embeddings are the mechanism by which F* values are converted to and from terms. This is essential for:
       1. Implementing reflection primitives
       2. Normalizing metaprograms
       3. Extracting reflection code to OCaml

       4.1 Embedding Structure

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Embeddings.fst:43-48:

       (* We only use simple embeddings here *)
       let mk_emb f g t =
           mk_emb (fun x r _topt _norm -> f r x)
                  (fun x _norm -> g x)
                  (term_as_fv t)
       let embed {|embedding 'a|} r (x:'a) = embed x r None id_norm_cb
       let try_unembed {|embedding 'a|} x : option 'a = try_unembed x id_norm_cb

       An embedding consists of:
       - embed: Convert a value to its term representation
       - unembed: Try to recover a value from a term
       - typ: The F* type of the embedded values

       4.2 Lazy Embeddings

       For large or complex structures, F* uses lazy embeddings that wrap values as blobs:

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Embeddings.fst:70-84:

       (* The lazy embeddings: just embedding whatever value as a blob inside a Tm_Lazy node. *)
       let e_bv                 : embedding bv                 = EMB.e_lazy Lazy_bv fstar_refl_bv
       let e_namedv             : embedding namedv             = EMB.e_lazy Lazy_namedv fstar_refl_namedv
       let e_binder             : embedding binder             = EMB.e_lazy Lazy_binder fstar_refl_binder
       let e_fv                 : embedding fv                 = EMB.e_lazy Lazy_fvar fstar_refl_fv
       let e_comp               : embedding comp               = EMB.e_lazy Lazy_comp fstar_refl_comp
       let e_universe           : embedding universe           = EMB.e_lazy Lazy_universe fstar_refl_universe
       let e_ident              : embedding I.ident            = EMB.e_lazy Lazy_ident fstar_refl_ident
       let e_env                : embedding env                = EMB.e_lazy Lazy_env fstar_refl_env
       let e_sigelt             : embedding sigelt             = EMB.e_lazy Lazy_sigelt fstar_refl_sigelt
       let e_letbinding         : embedding letbinding         = EMB.e_lazy Lazy_letbinding fstar_refl_letbinding

       Lazy embeddings:
       1. Store the actual value as a dynamically-typed blob
       2. Only expand when needed (e.g., when pattern-matching)
       3. Preserve sharing and avoid redundant conversions

       4.3 Term Embedding with Antiquotations

       The most complex embedding is for terms, which must handle antiquotations:

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Embeddings.fst:93-124:

       let e_term_aq aq =
           let embed_term (rng:Range.t) (t:term) : term =
               let qi = { qkind = Quote_static; antiquotations = aq } in
               S.mk (Tm_quoted (t, qi)) rng
           in
           let rec unembed_term (t:term) : option term =
               let apply_antiquotations (t:term) (aq:antiquotations) : option term =
                   let shift, aqs = aq in
                   let aqs = List.rev aqs in
                   // Try to unembed all antiquotations
                   Option.bind (mapM_opt unembed_term aqs) (fun aq_ts ->
                   let subst_open, subst =
                      aq_ts
                      |> List.mapi (fun i at ->
                           let x = S.new_bv None S.t_term in
                           DB(shift+i, x), NT (x, at))
                      |> List.unzip
                   in
                   Some (SS.subst subst <| SS.subst subst_open t))
               in
               let t = U.unmeta t in
               match (SS.compress t).n with
               | Tm_quoted (tm, qi) ->
                   apply_antiquotations tm qi.antiquotations
               | _ -> None
           in
           mk_emb embed_term unembed_term S.t_term

       Antiquotations allow "escaping" from a quotation to splice in computed values. The shift tracking ensures de Bruijn indices remain correct.

       4.4 Unfolding Lazy Values

       When lazy values need to be inspected, they are unfolded:

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Embeddings.fst:782-835:

       let unfold_lazy_bv (i : lazyinfo) : term =
           let bv : bv = undyn i.blob in
           S.mk_Tm_app fstar_refl_pack_bv.t [S.as_arg (embed i.rng (inspect_bv bv))]
                       i.rng

       let unfold_lazy_binder (i : lazyinfo) : term =
           let binder : binder = undyn i.blob in
           S.mk_Tm_app fstar_refl_pack_binder.t [S.as_arg (embed i.rng (inspect_binder binder))]
                       i.rng

       The unfolding pattern is:
       1. Extract the blob from the lazy node
       2. Inspect it to get the view
       3. Embed the view as a term
       4. Wrap in the appropriate pack_* call

       ---
       5. NBE Embeddings

       F* has two normalization engines:
       1. KAM (Krivine Abstract Machine): The traditional term-based normalizer
       2. NBE (Normalization by Evaluation): A faster evaluator using native OCaml values

       Both require embeddings, but they differ in representation.

       5.1 NBE Term Representation

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.NBEEmbeddings.fst:37-40:

       (*
        * embed   : from compiler to user
        * unembed : from user to compiler
        *)

       NBE uses a different term representation (NBETerm.t) that directly represents values in normal form.

       5.2 NBE Embedding Example

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.NBEEmbeddings.fst:145-166:

       let e_aqualv =
           let embed_aqualv cb (q : aqualv) : t =
               match q with
               | Data.Q_Explicit -> mkConstruct ref_Q_Explicit.fv [] []
               | Data.Q_Implicit -> mkConstruct ref_Q_Implicit.fv [] []
               | Data.Q_Meta t   -> mkConstruct ref_Q_Meta.fv [] [as_arg (embed e_term cb t)]
           in
           let unembed_aqualv cb (t : t) : option aqualv =
               match t.nbe_t with
               | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
               | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
               | Construct (fv, [], [(t, _)]) when S.fv_eq_lid fv ref_Q_Meta.lid ->
                   Option.bind (unembed e_term cb t) (fun t ->
                   Some (Data.Q_Meta t))
               | _ ->
                   Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded aqualv: %s" (t_to_string t));
                   None
           in
           mk_emb embed_aqualv unembed_aqualv (...)

       Key differences from KAM embeddings:
       - Uses mkConstruct instead of S.mk_Tm_app
       - Pattern matches on Construct nodes instead of term syntax
       - Arguments are accumulated backwards (important implementation detail!)

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.NBEEmbeddings.fst:48-55:

       (* PLEASE NOTE: Construct and FV accumulate their arguments BACKWARDS. That is,
        * the expression (f 1 2) is stored as FV (f, [], [Constant (Int 2); Constant (Int 1)].
        * So be careful when calling mkFV/mkConstruct and matching on them. *)

       (* On that note, we use this (inefficient, FIXME) hack in this module *)
       let mkFV fv us ts = mkFV fv (List.rev us) (List.rev ts)
       let mkConstruct fv us ts = mkConstruct fv (List.rev us) (List.rev ts)

       ---
       6. Quotation and Splicing

       F* supports quotation syntax to create terms and splicing to insert computed terms into quotations.

       6.1 Static vs Dynamic Quotation

       From the term syntax, quotation can be:
       - Static (Quote_static): The quoted term is embedded as-is at compile time
       - Dynamic (Quote_dynamic): The term is computed and then quoted

       From /home/grigory/Downloads/FStar/src/syntax/FStarC.Syntax.Syntax.fst:718-719:

       | Tm_quoted (_, {qkind=Quote_static}) -> "Tm_quoted(static)"
       | Tm_quoted (_, {qkind=Quote_dynamic}) -> "Tm_quoted(dynamic)"

       6.2 Quotation Syntax

       In F* source code:

       (* Static quotation - creates a term at compile time *)
       let term_true : term = `true

       (* Dynamic quotation with antiquotation *)
       let make_app (f : term) (x : term) : term =
         `((`#f) (`#x))

       The backtick () introduces a quotation, and #` inside a quotation introduces an antiquotation (splice).

       6.3 Antiquotation Implementation

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Embeddings.fst:99-116:

       let apply_antiquotations (t:term) (aq:antiquotations) : option term =
           let shift, aqs = aq in
           let aqs = List.rev aqs in
           // Try to unembed all antiquotations
           Option.bind (mapM_opt unembed_term aqs) (fun aq_ts ->
           // Create a substitution of the DB indices of t for the antiquotations
           let subst_open, subst =
              aq_ts
              |> List.mapi (fun i at ->
                   let x = S.new_bv None S.t_term in
                   DB(shift+i, x), NT (x, at))
              |> List.unzip
           in
           // Substitute and return
           Some (SS.subst subst <| SS.subst subst_open t))

       Antiquotations work by:
       1. Storing spliced terms in a list
       2. Representing splice points as bound variables
       3. Substituting the actual terms when unembedding

       ---
       7. The Interpreter: Registering Primitives

       Reflection primitives are implemented in OCaml/F* and registered with the normalizer.

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Interpreter.fst:94-204:

       let reflection_primops : list PO.primitive_step = [
         (****** Inspecting/packing various kinds of syntax ******)
         mk1 "inspect_ln"
           #RE.e_term #_
           #NRE.e_term #_
           RB.inspect_ln;

         mk1 "pack_ln"
           #_ #RE.e_term
           #_ #NRE.e_term
           RB.pack_ln;

         mk1 "inspect_fv" RB.inspect_fv;
         mk1 "pack_fv" RB.pack_fv;
         mk1 "inspect_comp" RB.inspect_comp;
         mk1 "pack_comp" RB.pack_comp;
         // ... many more ...
       ]

       let _ = List.iter FStarC.TypeChecker.Cfg.register_extra_step reflection_primops

       The mk1, mk2, mk3 helpers create primitive steps that:
       1. Unembed arguments from terms
       2. Call the actual implementation
       3. Embed the result back to a term
       4. Work for both KAM and NBE normalization

       7.1 Safety Requirements

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Interpreter.fst:79-92:

       (*
        * NOTE: all primitives must be carefully inspected to make sure they
        * do not break the abstraction barrier imposed by the term_view.
        * Otherwise, the pack_inspect_inv and inspect_pack_inv lemmas could
        * likely be used to derive a contradiction.
        *
        * The way to go about adding new primitives is to implement them in the
        * FStarC.Reflection.V2.Builtins module and implement them using the (internal)
        * inspect_ln and pack_ln functions, which means they should not break
        * the view abstraction.
        *
        * _Any_ call to functions elsewhere, say term_to_string or
        * Util.term_eq, will _very likely_ be inconsistent with the view.
        *)

       This is critical: primitives must respect the view abstraction, or the bijection lemmas become unsound.

       ---
       8. Derived Operations

       The reflection library provides many derived operations built on top of the primitives.

       8.1 Term Construction Helpers

       From /home/grigory/Downloads/FStar/ulib/FStar.Reflection.V2.Derived.fst:91-106:

       let rec mk_app (t : term) (args : list argv) : Tot term (decreases args) =
           match args with
           | [] -> t
           | (x::xs) -> mk_app (pack_ln (Tv_App t x)) xs

       let mk_e_app (t : term) (args : list term) : Tot term =
           let e t = (t, Q_Explicit) in
           mk_app t (List.Tot.Base.map e args)

       let rec mk_tot_arr_ln (bs: list binder) (cod : term) : Tot term (decreases bs) =
           match bs with
           | [] -> cod
           | (b::bs) -> pack_ln (Tv_Arrow b (pack_comp (C_Total (mk_tot_arr_ln bs cod))))

       8.2 Term Inspection Helpers

       From /home/grigory/Downloads/FStar/ulib/FStar.Reflection.V2.Derived.fst:29-33:

       let rec inspect_ln_unascribe (t:term) : tv:term_view{tv << t /\ notAscription tv} =
           match inspect_ln t with
           | Tv_AscribedT t' _ _ _
           | Tv_AscribedC t' _ _ _ -> inspect_ln_unascribe t'
           | tv -> tv

       8.3 Binder Construction

       From /home/grigory/Downloads/FStar/ulib/FStar.Reflection.V2.Derived.fst:56-65:

       let mk_binder (nm : string) (sort : typ) : simple_binder =
         let bv : binder_view = {
           ppname = seal nm;
           qual   = Q_Explicit;
           attrs  = [];
           sort   = sort;
         }
         in
         inspect_pack_binder bv;
         pack_binder bv

       ---
       9. Formula Reflection

       F* provides specialized support for reflecting logical formulas, making it easier to write proof tactics.

       From /home/grigory/Downloads/FStar/ulib/FStar.Reflection.V2.Formula.fst:52-74:

       [@@plugin]
       noeq type comparison =
         | Eq     of option typ  (* Propositional equality (eq2), maybe annotated *)
         | BoolEq of option typ  (* Decidable, boolean equality (eq), maybe annotated *)
         | Lt | Le | Gt | Ge     (* Orderings, at type `int` (and subtypes) *)

       [@@plugin]
       noeq type formula =
         | True_  : formula
         | False_ : formula
         | Comp   : comparison -> term -> term -> formula
         | And    : term -> term -> formula
         | Or     : term -> term -> formula
         | Not    : term -> formula
         | Implies: term -> term -> formula
         | Iff    : term -> term -> formula
         | Forall : bv -> typ -> term -> formula
         | Exists : bv -> typ -> term -> formula
         | App    : term -> term -> formula
         | Name   : namedv -> formula
         | FV     : fv -> formula
         | IntLit : int -> formula
         | F_Unknown : formula

       The term_as_formula function recognizes standard logical connectives:

       let term_as_formula' (t:term) : Tac formula =
           match inspect_unascribe t with
           | Tv_FVar fv | Tv_UInst fv _ ->
               let qn = inspect_fv fv in
               if qn = true_qn then True_
               else if qn = false_qn then False_
               else FV fv
           | Tv_App h0 t -> begin
               let (h, ts) = collect_app h0 in
               match inspect h, ts@[t] with
               | Tv_FVar fv, [(a1, Q_Implicit); (a2, Q_Explicit); (a3, Q_Explicit)] ->
                   let qn = inspect_fv fv in
                   if qn = eq2_qn then Comp (Eq (Some a1)) a2 a3
                   // ... etc ...

       ---
       10. Use Cases for Reflection

       10.1 Proof Automation

       The most common use case is implementing tactics that automate proof steps:

       let my_tactic () : Tac unit =
         let goal = cur_goal () in
         match term_as_formula goal with
         | And p q ->
           // Split conjunction goal into two subgoals
           apply_lemma (`conj_intro);
           // ... handle subgoals ...
         | Implies p q ->
           // Introduce hypothesis
           let _ = intro () in ()
         | _ -> fail "Unexpected goal shape"

       10.2 Code Generation

       Reflection can generate code at compile time:

       let rec mk_nested_pair (ts : list term) : term =
           match ts with
           | [] -> `()
           | [t] -> t
           | t::ts -> `((`#t, `#(mk_nested_pair ts)))

       10.3 Generic Programming

       Reflection enables deriving instances for type classes:

       let derive_show_for_record (env : env) (nm : name) : Tac (list decl) =
         match lookup_typ env nm with
         | Some se ->
           match inspect_sigelt se with
           | Sg_Inductive nm univs params typ ctors ->
             // Generate show instance based on constructors
             // ...
           | _ -> fail "Not an inductive type"
         | None -> fail "Type not found"

       ---
       11. Working with Sigelts

       Sigelts (signature elements) represent top-level definitions.

       11.1 Sigelt Views

       From /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Data.fsti:188-214:

       noeq
       type sigelt_view =
         | Sg_Let :
             (r:bool) ->           // is recursive?
             (lbs:list letbinding) ->
             sigelt_view

         | Sg_Inductive :
             (nm:name) ->              // name of the inductive type
             (univs:list univ_name) -> // universe variables
             (params:binders) ->       // parameters
             (typ:typ) ->              // the type annotation
             (cts:list ctor) ->        // constructors
             sigelt_view

         | Sg_Val :
             (nm:name) ->
             (univs:list univ_name) ->
             (typ:typ) ->
             sigelt_view

         | Unk

       11.2 Querying the Environment

       From /home/grigory/Downloads/FStar/ulib/FStar.Stubs.Reflection.V2.Builtins.fsti:124-162:

       (** Lookup a top-level definition in the environment *)
       val lookup_typ : env -> name -> option sigelt

       (** Returns all top-level sigelts marked with a given attribute *)
       val lookup_attr_ses : attr:term -> env -> list sigelt

       (** As [lookup_attr_ses], but just returns the names *)
       val lookup_attr : term -> env -> list fv

       (** Returns all top-level names in an environment *)
       val all_defs_in_env : env -> list fv

       (** Returns all top-level names in a given module *)
       val defs_in_module : env -> name -> list fv

       11.3 Attributes and Qualifiers

       (** Get/set attributes on sigelts *)
       val sigelt_attrs     : sigelt -> list term
       val set_sigelt_attrs : list term -> sigelt -> sigelt

       (** Get/set qualifiers on sigelts *)
       val sigelt_quals     : sigelt -> list qualifier
       val set_sigelt_quals : list qualifier -> sigelt -> sigelt

       ---
       12. Limitations and Caveats

       12.1 Compile-Time Only

       Reflection only works at compile time within metaprogramming effects. You cannot:
       - Inspect terms at runtime
       - Use reflection in extracted code
       - Depend on term syntax in proofs

       12.2 Unsupported Syntax

       Some syntax forms are not exposed through views:
       - Mutually recursive let bindings (partially supported)
       - Some pattern forms
       - Effect definitions
       - Module structure

       The Tv_Unsupp constructor indicates syntax that could not be inspected.

       12.3 View Abstraction

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Builtins.fst:744-763:

       (*
        * Why doesn't this call into Syntax.Util.term_eq? Because that function
        * can expose details that are not observable in the userspace view of
        * terms, and hence that function cannot be safely exposed if we wish to
        * maintain the lemmas stating that pack/inspect are inverses of each
        * other.
        *
        * In other words, we need this function to be implemented consistently
        * with the view to make sure it is a _function_ in userspace, and maps
        * (propositionally) equal terms to equal results.
        *)

       The term_eq primitive must be consistent with the view abstraction. Internal F* term equality might distinguish terms that are equal according to their views.

       12.4 Environment Dependency

       Some operations require an environment (env), which is only available within a tactic:

       val lookup_typ : env -> name -> option sigelt
       val lookup_attr : term -> env -> list fv

       Operations that appear pure but actually depend on the environment (like looking up whether an fv is a data constructor) use a global hook:

       From /home/grigory/Downloads/FStar/src/reflection/FStarC.Reflection.V2.Builtins.fst:63-79:

       (* This is a hack, but it allows to lookup the constructor sigelts when
       inspecting a Sig_inductive_typ. *)
       let get_env () : Env.env =
         match !N.reflection_env_hook with
         | None -> failwith "impossible: env_hook unset in reflection"
         | Some e -> e

       ---
       13. Summary

       F*'s reflection system provides:

       1. Abstract syntax types (term, comp, binder, etc.) that hide internal representation
       2. View types that expose structure as algebraic data types
       3. Inspect/pack functions with bijection guarantees
       4. Two API versions (V1 legacy, V2 current) with different variable handling
       5. Dual normalization support (KAM and NBE) via separate embedding modules
       6. Quotation and antiquotation for creating and splicing terms
       7. Environment queries for looking up definitions and attributes
       8. Formula reflection for proof automation

       The system is carefully designed to:
       - Maintain soundness (no proof-level syntax inspection)
       - Support total recursive traversals (precedence guarantees)
       - Enable efficient normalization (lazy embeddings)
       - Preserve the view abstraction (consistent term equality)

       When using reflection, always prefer:
       - V2 API for new code
       - inspect_ln_unascribe to skip ascriptions
       - Derived helpers over raw inspect/pack
       - Formula reflection for proof tactics

  ⎿  Done (26 tool uses · 161.5k tokens · 3m 59s)

● elite-bug-hunter(F* Ch12: ML Extraction)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering CODE EXTRACTION TO ML.

       Explore /home/grigory/Downloads/FStar/src/extraction/ extensively.

       Focus on:
       1. Read FStarC.Extraction.ML.Term.fst completely (97KB) - document term extraction
       2. Read FStarC.Extraction.ML.Modul.fst (53KB) - document module extraction
       3. Read FStarC.Extraction.ML.Code.fst - document code generation
       4. Read FStarC.Extraction.ML.Syntax.fst - document ML AST
       5. Read FStarC.Extraction.ML.UEnv.fst - document extraction environment
       6. Read FStarC.Extraction.ML.RemoveUnusedParameters.fst - document optimization
       7. Explore extraction_design.txt if present

       Your chapter should include:
       - How F* types map to OCaml types
       - How effects are erased or handled
       - Extraction of proofs (erasure)
       - Module system translation
       - Type class extraction
       - Handling of Ghost, Erased
       - Inline annotations
       - noextract annotations
       - F# vs OCaml differences
       - Debugging extraction issues

       Read at least 8 files. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have comprehensive information from the key extraction files. Let me write the documentation chapter:

       ---
       F* Code Extraction to ML: A Comprehensive Reference

       1. Introduction and Overview

       F* (FStar) is a proof-oriented programming language with dependent types, effects, and refinement types. One of its key features is the ability to extract verified code to efficient target languages including OCaml and F#. This chapter provides an in-depth analysis of
       F*'s extraction infrastructure, based on the implementation in /home/grigory/Downloads/FStar/src/extraction/.

       The extraction pipeline transforms F* terms, types, and module structures into ML (OCaml/F#) code. The core principle is to preserve computational behavior while erasing proofs and specification-level constructs. As stated in the design document
       (extraction_design.txt:63-67):

       The main invariant:

             erase(G) |- e <= N  tau  || E
         ==> erase(G) |-ML  E : (erase tau)

       This means that if an F* expression e extracts to ML expression E at type tau, then E is well-typed at the erased type erase(tau) in the corresponding ML environment.

       2. ML AST Structure (FStarC.Extraction.ML.Syntax)

       The extraction process generates an intermediate ML AST before printing to actual OCaml or F# code. Understanding this AST is fundamental to understanding extraction.

       2.1 ML Types

       From FStarC.Extraction.ML.Syntax.fsti:57-63:

       type mlty =
       | MLTY_Var   of mlident
       | MLTY_Fun   of mlty & e_tag & mlty
       | MLTY_Named of list mlty & mlpath
       | MLTY_Tuple of list mlty
       | MLTY_Top   (* Obj.t in OCaml; System.Object in F# *)
       | MLTY_Erased (* a type that extracts to unit *)

       Key observations:

       1. MLTY_Fun carries an explicit effect tag (e_tag) between domain and codomain, used internally but not printed in output code.
       2. MLTY_Top represents the universal type - Obj.t in OCaml or System.Object in F#. This is used when F* types cannot be expressed in ML's type system.
       3. MLTY_Erased represents types that extract to unit. This is crucial for proof erasure.

       2.2 Effect Tags

       From FStarC.Extraction.ML.Syntax.fsti:48-51:

       type e_tag =
         | E_PURE      (* Pure computations *)
         | E_ERASABLE  (* Computations whose results can be erased *)
         | E_IMPURE    (* Effectful computations *)

       The extraction maintains effect information to determine what can be erased and to preserve evaluation order for impure computations.

       2.3 ML Expressions

       From FStarC.Extraction.ML.Syntax.fsti:124-150:

       and mlexpr' =
       | MLE_Const  of mlconstant
       | MLE_Var    of mlident
       | MLE_Name   of mlpath
       | MLE_Let    of mlletbinding & mlexpr
       | MLE_App    of mlexpr & list mlexpr
       | MLE_TApp   of mlexpr & list mlty     (* Type applications - preserved for Karamel *)
       | MLE_Fun    of list mlbinder & mlexpr
       | MLE_Match  of mlexpr & list mlbranch
       | MLE_Coerce of mlexpr & mlty & mlty   (* Obj.magic in OCaml *)
       | MLE_CTor   of mlpath & list mlexpr   (* Fully applied constructors *)
       | MLE_Seq    of list mlexpr
       | MLE_Tuple  of list mlexpr
       | MLE_Record of list mlsymbol & mlsymbol & list (mlsymbol & mlexpr)
       | MLE_Proj   of mlexpr & mlpath
       | MLE_If     of mlexpr & mlexpr & option mlexpr
       | MLE_Raise  of mlpath & list mlexpr
       | MLE_Try    of mlexpr & list mlbranch

       Note that MLE_TApp (type application) is preserved in the AST even though OCaml does not have explicit type applications. This is important for Karamel extraction to C, which requires explicit type information.

       2.4 Metadata Annotations

       From FStarC.Extraction.ML.Syntax.fsti:85-109, extraction preserves various metadata:

       type meta =
         | Mutable
         | Assumed
         | Private
         | NoExtract
         | CInline
         | Substitute
         | GCType
         | PpxDerivingShow
         | Comment of string
         | StackInline
         | CPrologue of string
         | CEpilogue of string
         | Erased
         | HasValDecl of FStarC.Range.t
         | CNoInline
         ...

       These metadata tags influence both ML and C (via Karamel) extraction.

       3. The Extraction Environment (FStarC.Extraction.ML.UEnv)

       The extraction environment maintains the mapping between F* names and their ML counterparts, handling several concerns:

       3.1 Environment Structure

       From FStarC.Extraction.ML.UEnv.fst:104-116:

       type uenv = {
         env_tcenv:TypeChecker.Env.env;           (* Underlying typechecker environment *)
         env_bindings:list mlbinding;             (* Names in scope with their types *)
         env_mlident_map:PSMap.t mlident;         (* Used names (for freshness) *)
         env_remove_typars:RemoveUnusedParameters.env_t;
         mlpath_of_lid:PSMap.t mlpath;            (* F* lid -> ML path mapping *)
         env_fieldname_map:PSMap.t mlident;       (* Record field names *)
         mlpath_of_fieldname:PSMap.t mlpath;
         tydefs:list tydef;                       (* Type abbreviations *)
         type_names:list (fv&mlpath);             (* Inductive type names *)
         tydef_declarations:PSMap.t bool;
         currentModule: mlpath
       }

       3.2 Binding Types

       From FStarC.Extraction.ML.UEnv.fsti:35-52:

       type ty_binding = {
         ty_b_name:mlident;
         ty_b_ty:mlty
       }

       type exp_binding = {
         exp_b_name:mlident;
         exp_b_expr:mlexpr;
         exp_b_tscheme:mltyscheme;
         exp_b_eff: e_tag
       }

       type mlbinding =
         | Bv  of bv & ty_or_exp_b        (* Local variable *)
         | Fv  of fv & exp_binding        (* Top-level name *)
         | ErasedFv of fv                 (* Name was erased via noextract *)

       3.3 Naming Conventions

       The environment enforces ML naming conventions (FStarC.Extraction.ML.UEnv.fst:382-399):

       let rename_conventional (s:string) (is_local_type_variable:bool) : string =
         (* Type variables must begin with ' and cannot have _ as second char *)
         (* Term variables must begin with letter or _ *)
         (* Invalid characters are replaced *)

       The environment also maintains sets of used names to ensure freshness (FStarC.Extraction.ML.UEnv.fst:421-434):

       let find_uniq ml_ident_map root_name is_local_type_variable =
         let rec aux i root_name =
           let target_mlident = if i = 0 then root_name else root_name ^ (show i) in
           match PSMap.try_find ml_ident_map target_mlident with
             | Some x -> aux (i+1) root_name
             | None -> target_mlident, PSMap.add ml_ident_map target_mlident ""
         in
         ...

       This ensures that identifiers like x, x1, x2 are generated to avoid shadowing.

       4. Term Extraction (FStarC.Extraction.ML.Term)

       The term extraction module is the heart of the extraction process. It transforms F* terms to ML expressions while tracking types and effects.

       4.1 Core Extraction Functions

       The main entry point is term_as_mlexpr (FStarC.Extraction.ML.Term.fst:1383-1386):

       and term_as_mlexpr (g:uenv) (e:term) : (mlexpr & e_tag & mlty) =
           let e, f, t = !ref_term_as_mlexpr g e in
           let e, f = maybe_promote_effect e f t in
           e, f, t

       Returns a triple: the ML expression, its effect tag, and its ML type.

       4.2 Type Extraction

       Types are extracted via term_as_mlty (FStarC.Extraction.ML.Term.fst:856-858):

       let term_as_mlty g t0 =
           let t = N.normalize extraction_norm_steps (tcenv_of_uenv g) t0 in
           translate_term_to_mlty g t

       The normalization steps are crucial (FStarC.Extraction.ML.Term.fst:644-660):

       let extraction_norm_steps =
         let extraction_norm_steps_core =
           [Env.AllowUnboundUniverses;
            Env.EraseUniverses;
            Env.Inlining;
            Env.Eager_unfolding;
            Env.Exclude Env.Zeta;   (* Don't unfold recursive definitions *)
            Env.Primops;
            Env.Unascribe;
            Env.ForExtraction] in
         ...

       4.3 Determining if a Term is a Type

       From FStarC.Extraction.ML.Term.fst:216-308, is_type determines whether a term should be treated as a type (and potentially erased):

       let rec is_type_aux env t =
           let t = SS.compress t in
           match t.n with
           | Tm_type _
           | Tm_refine _
           | Tm_arrow _ -> true
           | Tm_fvar fv -> UEnv.is_type_name env fv
           | Tm_name x -> is_arity env x.sort
           ...

       4.4 Effect to E_Tag Translation

       From FStarC.Extraction.ML.Term.fst:120-150:

       let effect_as_etag =
           let cache = SMap.create 20 in
           let rec delta_norm_eff g (l:lident) = ... in
           fun g l ->
           let l = delta_norm_eff g l in
           if lid_equals l PC.effect_PURE_lid
           then E_PURE
           else if TcEnv.is_erasable_effect (tcenv_of_uenv g) l
           then E_ERASABLE
           else ...
                E_IMPURE

       4.5 Handling Type Applications

       When encountering polymorphic terms without F* type applications (due to implicit instantiation), extraction generates explicit ML type arguments (FStarC.Extraction.ML.Term.fst:451-478):

       let instantiate_maybe_partial (g:uenv) (e:mlexpr) (eff:e_tag) (s:mltyscheme) (tyargs:list mlty) =
           let vars, t = s in
           let n_vars = List.length vars in
           let n_args = List.length tyargs in
           if n_args = n_vars then ... (* Exact match *)
           else if n_args < n_vars then
                (* Partial application - fill with MLTY_Erased and eta-expand *)
                let extra_tyargs = rest_vars |> List.map (fun _ -> MLTY_Erased) in
                ...

       4.6 Type Coercion (Obj.magic)

       When F* types are more precise than what ML can express, Obj.magic (or box in F#) is inserted (FStarC.Extraction.ML.Term.fst:523-593):

       let apply_coercion (pos:Range.t) (g:uenv) (e:mlexpr) (ty:mlty) (expect:mlty) : mlexpr =
           if Util.codegen_fsharp()
           then (* F# magics can be unsound - warn *)
             FStarC.Errors.log_issue pos Errors.Warning_NoMagicInFSharp [...]
           (* Smart coercion that pushes coercions into term structure *)
           let rec aux (e:mlexpr) ty expect = ...

       The coercion logic is intelligent - it pushes coercions into function bodies and match branches rather than wrapping entire terms.

       4.7 Extracting Let Bindings

       Let binding extraction handles generalization and the value restriction (FStarC.Extraction.ML.Term.fst:1225-1341):

       let rec extract_lb_sig (g:uenv) (lbs:letbindings) : list lb_sig =
           let maybe_generalize {lbname; lbeff; lbtyp; lbdef; lbattrs} =
               (* Handle polymorphic bindings *)
               match lbtyp.n with
               | Tm_arrow {bs; comp=c} when (List.hd bs |> is_type_binder g) ->
                  (* Type binders get erased *)
                  (* If not a value after erasure, add unit argument for value restriction *)
                  let add_unit = not (is_fstar_value body) || not (U.is_pure_comp c) in
                  ...

       When a polymorphic definition is not a syntactic value, a unit argument is added to satisfy ML's value restriction.

       4.8 Extracting Pattern Matching

       Pattern extraction (FStarC.Extraction.ML.Term.fst:933-1119) handles:

       1. Dot patterns (inaccessible patterns) - erased
       2. Constructor patterns - translated with proper eta-expansion
       3. Integer patterns - may become when clauses for bigint

       let rec extract_one_pat (imp : bool) (g:uenv) (p:S.pat) (expected_ty:mlty) ...
           : uenv & option (mlpattern & list mlexpr) & bool =
           match p.v with
           | Pat_constant (Const_int (c, swopt)) when Options.codegen() <> Some Options.Krml ->
               (* Convert integer patterns to when clauses if not Karamel *)
               ...
           | Pat_var x ->
               (* Extend environment with variable at expected ML type, not F* computed type *)
               let g, x, _ = extend_bv g x ([], expected_ty) false imp in
               ...

       4.9 Extracting Applications

       Application extraction (FStarC.Extraction.ML.Term.fst:1673-1736) recursively processes arguments:

       let rec extract_app is_data (mlhead, mlargs_f) (f, t) restArgs =
           match restArgs, t with
           | [], _ -> (* Done - eta-expand if data constructor *)
               maybe_eta_data_and_project_record g is_data t (mk_head())

           | (arg, _)::rest, MLTY_Fun (formal_t, f', t)
                   when (is_type g arg && type_leq g formal_t ml_unit_ty) ->
             (* Type argument gets erased to unit *)
             extract_app is_data (mlhead, (ml_unit, E_PURE)::mlargs_f) (join f f', t) rest

           | (e0, _)::rest, MLTY_Fun(tExpected, f', t) ->
             (* Regular argument - check and possibly coerce *)
             let e0, tInferred = check_term_as_mlexpr g e0 expected_effect tExpected in
             extract_app is_data (mlhead, (e0, expected_effect)::mlargs_f) (join_l [f;f'], t) rest

       5. Module Extraction (FStarC.Extraction.ML.Modul)

       Module extraction orchestrates the extraction of entire F* modules.

       5.1 Extracting Type Definitions

       From FStarC.Extraction.ML.Modul.fst:350-411, type abbreviations are extracted:

       let extract_typ_abbrev env quals attrs lb : env_t & iface & list mlmodule1 =
           (* Normalize the type *)
           let lbtyp = N.normalize [Env.Beta; Env.UnfoldUntil delta_constant; ...] tcenv lbtyp in
           (* Eta expand the definition *)
           let lbdef = N.eta_expand_with_type tcenv lbdef lbtyp in
           (* Extract binders and body *)
           let env1, ml_bs = binders_as_mlty_binders env bs in
           let body = Term.term_as_mlty env1 body |> Util.eraseTypeDeep ... in
           ...

       5.2 Extracting Inductive Types

       Inductive types are bundled and extracted together (FStarC.Extraction.ML.Modul.fst:920-996):

       let extract_bundle env se =
           let extract_ctor (env_iparams:env_t) (ml_tyvars:list ty_param) (env:env_t) (ctor: data_constructor) =
               let mlt = Util.eraseTypeDeep ... (Term.term_as_mlty env_iparams ctor.dtyp) in
               let tys = (ml_tyvars, mlt) in
               let fvv = lid_as_fv ctor.dname None in
               let env, mls, _ = extend_fv env fvv tys false in
               env, (mls, List.zip names (argTypes mlt))
           in
           ...

       5.3 Extracting Reifiable Effects

       When an effect is marked for extraction via reification (FStarC.Extraction.ML.Modul.fst:544-623):

       let extract_reifiable_effect g ed : uenv & iface & list mlmodule1 =
           (* Extract return *)
           let return_tm, ty_sc = extract_fv (ed |> U.get_return_repr |> ...) in
           let return_nm, return_lid, return_b, g = extend_with_monad_op_name g ed "return" ty_sc in
           (* Extract bind *)
           let bind_tm, ty_sc = extract_fv (ed |> U.get_bind_repr |> ...) in
           let bind_nm, bind_lid, bind_b, g = extend_with_monad_op_name g ed "bind" ty_sc in
           (* Extract actions *)
           let g, actions = BU.fold_map extract_action g ed.actions in
           ...

       5.4 NoExtract Handling

       From FStarC.Extraction.ML.Modul.fst:732-756:

       let sigelt_has_noextract (se:sigelt) : bool =
         let has_noextract_qualifier = List.contains S.NoExtract se.sigquals in
         let has_noextract_attribute = get_noextract_to se (Options.codegen ()) in
         match Options.codegen () with
         | Some Options.Krml ->
           (* Karamel needs both qualifier AND attribute *)
           has_noextract_qualifier && has_noextract_attribute
         | _ ->
           (* OCaml/F# need either *)
           has_noextract_qualifier || has_noextract_attribute

       let mark_sigelt_erased (se:sigelt) (g:uenv) : uenv =
         List.fold_right (fun lid g -> extend_erased_fv g (S.lid_as_fv lid None))
                         (U.lids_of_sigelt se) g

       6. Type Parameter Optimization (FStarC.Extraction.ML.RemoveUnusedParameters)

       F# does not allow unused type parameters in type abbreviations. This module removes them.

       6.1 The Algorithm

       From FStarC.Extraction.ML.RemoveUnusedParameters.fst:180-244:

       let elim_tydef (env:env_t) name metadata parameters mlty =
           let mlty = elim_mlty env mlty in
           let freevars = freevars_of_mlty mlty in
           let _, parameters, entry =
               List.fold_left
                 (fun (i, params, entry) param ->
                    let p = param.ty_param_name in
                    if mem p freevars then (* Used - keep *)
                      i+1, param::params, Retain::entry
                    else begin
                      if can_eliminate i || must_eliminate i
                      then i+1, params, Omit::entry
                      else if Options.codegen() = Some Options.FSharp
                      then (* F# requires removal - error if can't *)
                           FStarC.Errors.log_issue ... Error_RemoveUnusedTypeParameter ...
                           raise Drop_tydef
                      else i+1, param::params, Retain::entry
                    end)
                 (0, [], [])
                 parameters
           in
           extend_env env name (List.rev entry), ...

       6.2 Attribute Control

       The remove_unused_type_parameters attribute allows explicit control:

       [@@ remove_unused_type_parameters [0; 2]]
       type t (a:Type) (b:Type) (c:Type) = b  (* Removes a and c *)

       7. Code Generation (FStarC.Extraction.ML.Code)

       The Code module pretty-prints the ML AST to actual OCaml/F# syntax.

       7.1 F# vs OCaml Differences

       From FStarC.Extraction.ML.Code.fst:356-358 (MLTY_Top handling):

       | MLTY_Top ->
         if Util.codegen_fsharp()
         then text "obj"
         else text "Obj.t"

       From FStarC.Extraction.ML.Code.fst:369-373 (Coercion):

       | MLE_Coerce (e, t, t') ->
         let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
         if Util.codegen_fsharp()
         then parens (reduce [text "Prims.unsafe_coerce "; doc])
         else parens (reduce [text "Obj.magic "; parens doc])

       7.2 Keyword Handling

       From FStarC.Extraction.ML.Syntax.fst:34-68, both OCaml and F# keyword lists are maintained:

       let ocamlkeywords = [
         "and"; "as"; "assert"; "asr"; "begin"; "class";
         "constraint"; "do"; "done"; "downto"; "else"; "end";
         ...
       ]

       let fsharpkeywords = [
         "abstract"; "and"; "as"; "assert"; "base"; "begin";
         ...
         (* F#-specific *)
         "inline"; "interface"; "internal"; "lazy";
         ...
       ]

       8. Proof and Ghost Code Erasure

       8.1 Erasability Determination

       The core erasure logic is in the typechecker, but extraction relies on it (FStarC.Extraction.ML.Term.fst:829-834):

       if TcUtil.must_erase_for_extraction (tcenv_of_uenv g) t0
       then MLTY_Erased
       else let mlt = aux g t0 in ...

       8.2 Ghost Effect Handling

       From FStarC.Extraction.ML.Term.fst:1491-1501:

       | Tm_meta {tm=t; meta=Meta_monadic_lift (m1, _m2, _ty)}
         when effect_as_etag g m1 = E_ERASABLE ->
         (* Lifting from an erasable effect - erase *)
         ml_unit, E_ERASABLE, MLTY_Erased

       8.3 Erased Type Handling

       The Erased type constructor wraps values that should be erased. When encountered, extraction produces unit:

       | MLTY_Erased -> ml_unit

       9. Handling Inline and NoExtract Annotations

       9.1 inline_for_extraction

       Definitions marked inline_for_extraction are inlined during normalization before extraction. This is controlled by the normalization steps including Env.Inlining.

       9.2 noextract

       From FStarC.Extraction.ML.Modul.fst:769-772:

       let rec extract_sigelt_iface (g:uenv) (se:sigelt) : uenv & iface =
           if sigelt_has_noextract se then
             let g = mark_sigelt_erased se g in
             g, empty_iface
           else ...

       The noextract qualifier completely removes definitions from extracted code. References to erased definitions trigger errors unless also marked noextract.

       10. Extension Mechanism

       F* supports extraction extensions for custom handling (FStarC.Extraction.ML.Modul.fst:62-77):

       let extension_extractor_table : SMap.t extension_extractor = SMap.create 20

       let register_extension_extractor (ext:string) (callback:extension_extractor) =
         SMap.add extension_extractor_table ext callback

       let lookup_extension_extractor (ext:string) =
         match SMap.try_find extension_extractor_table ext with
         | None -> if Plugins.autoload_plugin ext then ... else None
         | r -> r

       Extensions can provide custom extraction logic for specific definitions.

       11. Debugging Extraction Issues

       11.1 Debug Toggles

       From FStarC.Extraction.ML.Term.fst:48-49:

       let dbg_Extraction     = Debug.get_toggle "Extraction"
       let dbg_ExtractionNorm = Debug.get_toggle "ExtractionNorm"

       Enable with --debug Extraction or --debug ExtractionNorm.

       11.2 Common Issues

       1. Obj.magic insertions: Occur when F* types are more precise than ML types. The extraction logs coercion sites when debug is enabled.
       2. Value restriction violations: Polymorphic definitions that are not syntactic values get unit arguments added.
       3. Unused type parameters (F#): Will cause extraction failure unless marked with remove_unused_type_parameters.
       4. References to noextract definitions: Produce error Error_CallToErased.

       11.3 Error Messages

       From FStarC.Extraction.ML.Term.fst:79-111:

       let err_ill_typed_application env (t : term) mlhead (args : args) (ty : mlty) =
           Errors.raise_error t Fatal_IllTyped
              (Format.fmt4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n" ...)

       let err_value_restriction (t:term) =
           Errors.raise_error t Fatal_ValueRestriction
              (Format.fmt2 "Refusing to generalize because of the value restriction: (%s) %s" ...)

       12. Summary: The Extraction Pipeline

       1. Normalization: Types and terms are normalized with extraction-specific steps (inline, erase universes, unfold abbreviations)
       2. Type Translation: F* types become ML types via term_as_mlty, with dependent types erased to unit or Obj.t
       3. Term Translation: F* terms become ML expressions via term_as_mlexpr, with proofs erased and effects tracked
       4. Module Assembly: Module structures are preserved, with type definitions, let bindings, and exceptions translated
       5. Optimization: Unused type parameters are removed (essential for F#)
       6. Code Generation: ML AST is pretty-printed to OCaml or F# syntax

       The extraction preserves computational behavior while erasing specification-level constructs, maintaining type safety through careful use of Obj.magic where necessary.
  ⎿  Done (16 tool uses · 167.5k tokens · 3m 10s)

● elite-bug-hunter(F* Ch13: Karamel Extraction)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering KARAMEL (Low*) EXTRACTION TO C.

       Explore /home/grigory/Downloads/FStar/src/extraction/ and related files.

       Focus on:
       1. Read FStarC.Extraction.Krml.fst completely (58KB) - document Karamel IR
       2. Understand the Low* subset of F*
       3. Explore ulib/LowStar..fst files - document the Low library
       4. Understand buffer operations and memory management

       Your chapter should include:
       - What is Low* and its restrictions
       - The Karamel IR format
       - How F* terms map to C constructs
       - Buffer types and operations
       - Stack vs heap allocation
       - Modifies clauses and framing
       - inline_for_extraction usage
       - noextract for proof-only code
       - HACL* as an example
       - Common extraction patterns
       - Debugging C extraction issues

       Read files in src/extraction and ulib/LowStar*. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have gathered comprehensive information to write the documentation chapter. Let me compose it:

       ---
       Chapter: Karamel (Low*) Extraction to C

       1. Introduction to Low* and Karamel

       Low* is a subset of F* designed for systems programming that extracts to efficient, readable C code. The name comes from "Low-level F*" and the extraction toolchain is called Karamel (formerly KaRaMeL). This pipeline enables writing verified low-level code in F* while
       targeting C as the output language.

       The extraction process follows two stages:

       1. F to ML Syntax: F first extracts to an internal ML-like intermediate representation (defined in FStarC.Extraction.ML.Syntax)
       2. ML to Karamel IR: The ML representation is then translated to the Karamel IR (defined in FStarC.Extraction.Krml.fst)
       3. Karamel to C: The external Karamel tool then compiles this IR to C code

       This chapter documents the Low* library, the Karamel IR, memory management patterns, and extraction mechanisms.

       ---
       2. The Low* Subset of F*

       Low* restricts F* to constructs that map cleanly to C. The key principles are:

       2.1 Restrictions and Requirements

       Supported Constructs:
       - Fixed-width machine integers (FStar.Int8, FStar.UInt32, etc.)
       - Mutable buffers (LowStar.Buffer)
       - Stack-allocated arrays
       - Heap-allocated memory (manually managed or GC'd)
       - First-order functions
       - Flat records and tagged unions
       - While loops and structured control flow

       Unsupported or Restricted Constructs:
       - Higher-order functions (must be eliminated before extraction)
       - Closures (no runtime closure representation in C)
       - Recursive types with infinite depth
       - General polymorphism (monomorphized during extraction)
       - Dependent types (erased at extraction time)

       2.2 The Memory Model

       Low* uses the HyperStack memory model from F*, which provides:

       - Regions: Hierarchical memory organization (stack frames, heap regions)
       - References: Mutable cells containing single values
       - Buffers: Contiguous arrays of elements

       From /home/grigory/Downloads/FStar/ulib/FStar.HyperStack.ST.fsti:201-228:

       (* Stack effect - maintains the stack discipline *)
       effect Stack (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
              STATE a
                    (fun (p:st_post a) (h:mem) -> pre h /\
                     (forall a h1. (pre h /\ post h a h1 /\ equal_domains h h1) ==> p a h1))

       (* ST effect - low-level allocation without stack constraints *)
       effect ST (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
              STATE a
                    (fun (p:st_post a) (h:mem) -> pre h /\
                     (forall a h1. (pre h /\ post h a h1 /\ equal_stack_domains h h1) ==> p a h1))

       (* StackInline - indicates inlining into caller's frame *)
       effect StackInline (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
              STATE a
                    (fun (p:st_post a) (h:mem) -> pre h /\ is_stack_region (get_tip h) /\
                     (forall a h1. (pre h /\ post h a h1 /\ inline_stack_inv h h1) ==> p a h1))

       ---
       3. The Karamel IR Format

       The Karamel IR is defined in /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst. It represents a C-like intermediate language.

       3.1 Version and Compatibility

       From FStarC.Extraction.Krml.fst:37-49:

       (** CHANGELOG
       - v24: Added type applications to expressions
       - v25: Added type parameters for globals
       - v26: Flags for DExternal and DType's
       - v27: Added PConstant
       - v28: Added TConstBuf
       - v29: Added SizeT and PtrdiffT widths
       - v30: Added EBufDiff
       - v31: Added `meta` field to binders (for CInline)
       *)
       let current_version: version = 31

       3.2 Declaration Types

       From FStarC.Extraction.Krml.fst:53-62:

       type decl =
         | DGlobal of list flag & lident & int & typ & expr
             (* Global variable: flags, name, type params, type, initializer *)
         | DFunction of option cc & list flag & int & typ & lident & list binder & expr
             (* Function: calling convention, flags, type params, return type, name, params, body *)
         | DTypeAlias of lident & list flag & int & typ
             (* Type alias: name, flags, type params, definition *)
         | DTypeFlat of lident & list flag & int & fields_t
             (* Flat struct: name, flags, type params, fields *)
         | DUnusedRetainedForBackwardsCompat of option cc & list flag & lident & typ
         | DTypeVariant of lident & list flag & int & branches_t
             (* Tagged union: name, flags, type params, constructors *)
         | DTypeAbstractStruct of lident
             (* Abstract struct (forward declaration) *)
         | DExternal of option cc & list flag & lident & typ & list ident
             (* External declaration: cc, flags, name, type, argument names *)
         | DUntaggedUnion of lident & list flag & int & list (ident & typ)
             (* C union type *)

       3.3 Expression Types

       The expression AST maps closely to C constructs. From FStarC.Extraction.Krml.fst:99-142:

       and expr =
         | EBound of var                         (* De Bruijn index *)
         | EQualified of lident                  (* Qualified name *)
         | EConstant of constant                 (* Literal constant *)
         | EUnit                                 (* Unit value -> void *)
         | EApp of expr & list expr              (* Function application *)
         | ETypApp of expr & list typ            (* Type application *)
         | ELet of binder & expr & expr          (* Let binding *)
         | EIfThenElse of expr & expr & expr     (* Conditional *)
         | ESequence of list expr                (* Statement sequence *)
         | EAssign of expr & expr                (* Assignment *)
         | EBufCreate of lifetime & expr & expr  (* Buffer allocation *)
         | EBufRead of expr & expr               (* Buffer indexing: b[i] *)
         | EBufWrite of expr & expr & expr       (* Buffer write: b[i] = v *)
         | EBufSub of expr & expr                (* Pointer arithmetic: b + i *)
         | EBufBlit of expr & expr & expr & expr & expr  (* memcpy *)
         | EMatch of expr & branches             (* Pattern matching *)
         | EOp of op & width                     (* Primitive operator *)
         | ECast of expr & typ                   (* Type cast *)
         | EPushFrame                            (* Stack frame push *)
         | EPopFrame                             (* Stack frame pop *)
         | EBool of bool                         (* Boolean literal *)
         | EAny                                  (* Wildcard *)
         | EAbort                                (* abort() *)
         | EReturn of expr                       (* Return statement *)
         | EFlat of typ & list (ident & expr)    (* Struct literal *)
         | EField of typ & expr & ident          (* Field access: e.f *)
         | EWhile of expr & expr                 (* While loop *)
         | EBufCreateL of lifetime & list expr   (* Array literal *)
         | EBufFill of expr & expr & expr        (* memset *)
         | EBufFree of expr                      (* free() *)
         | EAddrOf of expr                       (* Address-of: &e *)
         | EBufNull of typ                       (* NULL pointer *)
         | EBufDiff of expr & expr               (* Pointer difference *)

       3.4 Type System

       From FStarC.Extraction.Krml.fst:190-202:

       and typ =
         | TInt of width        (* Fixed-width integers: int8_t, uint32_t, etc. *)
         | TBuf of typ          (* Mutable pointer: t* *)
         | TUnit                (* void *)
         | TQualified of lident (* Named type *)
         | TBool                (* bool *)
         | TAny                 (* void* or erased type *)
         | TArrow of typ & typ  (* Function pointer *)
         | TBound of int        (* Type variable (De Bruijn) *)
         | TApp of lident & list typ  (* Parameterized type *)
         | TTuple of list typ   (* Tuple type *)
         | TConstBuf of typ     (* Const pointer: const t* *)
         | TArray of typ & constant  (* Fixed-size array: t[n] *)

       3.5 Lifetime Annotations

       From FStarC.Extraction.Krml.fst:94-97:

       and lifetime =
         | Eternal           (* Heap-allocated (GC or manual) *)
         | Stack             (* Stack-allocated *)
         | ManuallyManaged   (* malloc/free managed *)

       ---
       4. Buffer Types and Operations

       4.1 The LowStar.Buffer Module

       The core buffer type is defined in /home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:70:

       val mbuffer (a:Type0) (rrel rel:srel a) :Tot Type0

       This is parameterized by:
       - a - Element type
       - rrel - The "root" preorder (for the original allocation)
       - rel - The current preorder (for sub-buffers)

       The simplified LowStar.Buffer module provides buffers with trivial preorders (/home/grigory/Downloads/FStar/ulib/LowStar.Buffer.fst:29-31):

       let trivial_preorder (a:Type0) :srel a = fun _ _ -> True

       type buffer (a:Type0) = mbuffer a (trivial_preorder a) (trivial_preorder a)

       4.2 Buffer Operations

       Liveness Predicate (/home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:96-110):

       (* live h b holds if buffer b is currently allocated in heap h *)
       val live (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot Type0

       Reading and Writing (/home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:1783-1858):

       (* index b i - reads b[i], extracts to b[i] in C *)
       val index (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (i:U32.t)
         :HST.Stack a
           (requires (fun h -> live h b /\ U32.v i < length b))
           (ensures  (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))

       (* upd b i v - writes b[i] = v *)
       val upd (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (i:U32.t) (v:a)
         : HST.Stack unit
           (requires (fun h -> live h b /\ U32.v i < length b /\
                            rel (as_seq h b) (Seq.upd (as_seq h b) (U32.v i) v)))
           (ensures (fun h _ h' ->
             modifies (loc_buffer b) h h' /\
             live h' b /\
             as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v))

       Sub-buffers (/home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:1754-1776):

       (* msub b i len - creates sub-buffer starting at offset i with length len *)
       (* Extracts to: b + i (pointer arithmetic) *)
       val msub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a) (b:mbuffer a rrel rel)
         (i:U32.t) (len:Ghost.erased U32.t)
         :HST.Stack (mbuffer a rrel sub_rel)
           (requires (fun h -> U32.v i + U32.v (Ghost.reveal len) <= length b /\
                            compatible_sub b i (Ghost.reveal len) sub_rel /\ live h b))
           (ensures  (fun h y h' -> h == h' /\ y == mgsub sub_rel b i (Ghost.reveal len)))

       4.3 Pointer Operators

       From /home/grigory/Downloads/FStar/ulib/LowStar.BufferOps.fst:38-54:

       (* Pointer dereference: *p - specially handled by Karamel *)
       let ( !* ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel):
         HST.Stack a
         (requires (fun h -> B.live h p))
         (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) =
         B.index p 0ul

       (* Pointer assignment: *p = v *)
       let ( *= ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel) (v:a) : HST.Stack unit
         (requires (fun h -> B.live h p /\ rel (B.as_seq h p) (Seq.upd (B.as_seq h p) 0 v)))
         (ensures (fun h0 _ h1 ->
           B.live h1 p /\
           B.as_seq h1 p `Seq.equal` Seq.create 1 v /\
           B.modifies (B.loc_buffer p) h0 h1
         ))
       = B.upd p 0ul v

       ---
       5. Stack vs Heap Allocation

       5.1 Stack Allocation

       Stack allocation uses malloca and related functions. From the extraction code in /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:867-888:

       (* Stack allocation patterns recognized by Karamel *)
       | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ e1; e2 ])
         when (string_of_mlpath p = "FStar.Buffer.create" ||
               string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca" ||
               string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca") ->
           EBufCreate (Stack, translate_expr env e1, translate_expr env e2)

       | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ])
         when (string_of_mlpath p = "FStar.Buffer.createL" ||
               string_of_mlpath p = "LowStar.Monotonic.Buffer.malloca_of_list" ||
               string_of_mlpath p = "LowStar.ImmutableBuffer.ialloca_of_list") ->
           EBufCreateL (Stack, List.map (translate_expr env) (list_elements e2))

       Stack Frame Management (/home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:985-991):

       | MLE_App ({ expr = MLE_Name p }, [ _ ]) 
         when (string_of_mlpath p = "FStar.HyperStack.ST.push_frame") ->
           EPushFrame

       | MLE_App ({ expr = MLE_Name p }, [ _ ]) 
         when (string_of_mlpath p = "FStar.HyperStack.ST.pop_frame") ->
           EPopFrame

       These translate to C code patterns like:

       void my_function() {
         // EPushFrame - marks beginning of stack frame
         uint32_t buf[16];  // Stack-allocated buffer
         // ... use buf ...
         // EPopFrame - marks end of stack frame (implicit in C)
       }

       5.2 Heap Allocation

       GC-managed Heap (/home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:904-907):

       | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
         when (string_of_mlpath p = "FStar.Buffer.rcreate" || 
               string_of_mlpath p = "LowStar.Monotonic.Buffer.mgcmalloc") ->
           EBufCreate (Eternal, translate_expr env e1, translate_expr env e2)

       Manually Managed Heap (/home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:931-936):

       | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _e0; e1; e2 ])
         when (string_of_mlpath p = "FStar.Buffer.rcreate_mm" ||
               string_of_mlpath p = "LowStar.Monotonic.Buffer.mmalloc") ->
           EBufCreate (ManuallyManaged, translate_expr env e1, translate_expr env e2)

       Freeing Memory (/home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:943-951):

       | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ])
         when (string_of_mlpath p = "FStar.HyperStack.ST.rfree" ||
               string_of_mlpath p = "LowStar.Monotonic.Buffer.free") ->
           EBufFree (translate_expr env e2)

       ---
       6. Modifies Clauses and Framing

       The modifies clause tracks which memory locations are modified by an operation.

       6.1 Location Types

       From /home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:405-459:

       (* The type of sets of memory locations *)
       [@@erasable]
       val loc : Type0

       (* Empty set of locations *)
       val loc_none: loc

       (* Union of location sets *)
       val loc_union (s1 s2: loc) : GTot loc

       (* Location of a buffer *)
       val loc_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot loc

       (* Location of a region *)
       val loc_regions (preserve_liveness: bool) (r: Set.set HS.rid) : GTot loc

       (* Location of specific addresses in a region *)
       val loc_addresses (preserve_liveness: bool) (r: HS.rid) (n: Set.set nat) : GTot loc

       6.2 The Modifies Predicate

       From /home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:992-1006:

       (* modifies s h1 h2 - only locations in s may have changed between h1 and h2 *)
       val modifies (s: loc) (h1 h2: HS.mem) : GTot Type0

       (* Key lemma: disjoint locations are preserved *)
       val modifies_buffer_elim (#a:Type0) (#rrel #rel:srel a)
         (b:mbuffer a rrel rel) (p:loc) (h h':HS.mem)
         :Lemma (requires (loc_disjoint (loc_buffer b) p /\ live h b /\ modifies p h h'))
                (ensures  (live h' b /\ (as_seq h b == as_seq h' b)))

       6.3 Framing Pattern

       The standard pattern for specifying buffer-modifying functions:

       val my_buffer_op:
           b: buffer uint32
         -> Stack unit
           (requires fun h0 -> live h0 b)
           (ensures  fun h0 _ h1 ->
             modifies (loc_buffer b) h0 h1 /\  (* Only b is modified *)
             live h1 b /\                       (* b remains live *)
             as_seq h1 b == ... )               (* Functional spec *)

       6.4 Transitivity and Fresh Regions

       From /home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:1255-1262:

       (* Modifies clauses compose transitively *)
       val modifies_trans (s12: loc) (h1 h2: HS.mem) (s23: loc) (h3: HS.mem)
       : Lemma
         (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
         (ensures (modifies (loc_union s12 s23) h1 h3))

       From /home/grigory/Downloads/FStar/ulib/LowStar.Monotonic.Buffer.fsti:1287-1290:

       (* Fresh regions can be removed from modifies clauses *)
       val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
         (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
         (ensures  (modifies l h0 h1))

       ---
       7. inline_for_extraction Usage

       The inline_for_extraction attribute tells F* to inline a definition during extraction.

       7.1 Purpose and Semantics

       From the F* documentation, inline_for_extraction serves several purposes:

       1. Eliminating higher-order code: Functions passed as arguments can be inlined at call sites
       2. Specializing generic code: Type-parameterized code can be instantiated
       3. Removing abstraction overhead: Helper functions can be inlined for efficiency

       7.2 Examples from HACL*

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:26-31:

       inline_for_extraction
       let buffer_t (t:buftype) (a:Type0) =
         match t with
         | IMMUT -> IB.ibuffer a
         | MUT -> B.buffer a
         | CONST -> CB.const_buffer a

       This type function is inlined at extraction time, so each usage becomes the concrete buffer type.

       7.3 Extraction Flag Translation

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:515-532:

       let translate_flags flags =
         List.choose (function
           | Syntax.Private -> Some Private
           | Syntax.NoExtract -> Some WipeBody      (* Erase body *)
           | Syntax.CInline -> Some CInline         (* __inline hint *)
           | Syntax.CNoInline -> Some CNoInline     (* __noinline hint *)
           | Syntax.Substitute -> Some Substitute   (* Full inlining *)
           | Syntax.GCType -> Some GCType
           | Syntax.Comment s -> Some (Comment s)
           | Syntax.StackInline -> Some MustDisappear  (* Must be inlined *)
           | Syntax.CConst s -> Some (Const s)
           | Syntax.CPrologue s -> Some (Prologue s)
           | Syntax.CEpilogue s -> Some (Epilogue s)
           | Syntax.CAbstract -> Some Abstract
           | Syntax.CIfDef -> Some IfDef
           | Syntax.CMacro -> Some Macro
           | Syntax.Deprecated s -> Some (Deprecated s)
           | _ -> None
         ) flags

       ---
       8. noextract for Proof-Only Code

       The noextract attribute marks definitions that should not be extracted to C.

       8.1 Ghost Code Patterns

       From the ML syntax metadata (/home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.ML.Syntax.fsti:89):

       type meta =
         | ...
         | NoExtract     (* Do not extract this binding *)
         | ...

       8.2 Usage Patterns

       (* This function exists only for proofs *)
       noextract
       let spec_function (x: nat) : nat = x * x

       (* This is extracted to C *)
       inline_for_extraction
       let impl_function (x: uint32) : Stack uint32
         (requires fun h -> True)
         (ensures fun h0 r h1 -> v r == spec_function (v x))
       = FStar.UInt32.mul x x

       8.3 Extraction Behavior

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:1368-1369:

       if List.mem Syntax.NoExtract meta then
         None  (* Skip extraction entirely *)

       When NoExtract is present, the definition is not translated to Karamel IR at all.

       ---
       9. HACL* as an Example

       HACL* (High-Assurance Cryptographic Library) demonstrates Low* patterns at scale.

       9.1 Library Organization

       From the HACL* Lib.Buffer module (/home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:19-44):

       #set-options "--z3rlimit 20 --fuel 0 --max_ifuel 1"

       type buftype =
         | MUT    (* Mutable buffer - extracted as a* *)
         | IMMUT  (* Immutable buffer - extracted as a*, with read-only semantics *)
         | CONST  (* Const buffer - extracted as const a* *)

       inline_for_extraction
       let buffer_t (t:buftype) (a:Type0) =
         match t with
         | IMMUT -> IB.ibuffer a
         | MUT -> B.buffer a
         | CONST -> CB.const_buffer a

       (* Type aliases for common cases *)
       unfold let buffer (a:Type0) = buffer_t MUT a
       unfold let ibuffer (a:Type0) = buffer_t IMMUT a
       unfold let cbuffer (a:Type0) = buffer_t CONST a

       9.2 Modifies Helpers

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:168-195:

       (* Modifies nothing *)
       let modifies0 (h1 h2:HS.mem) =
         modifies (B.loc_none) h1 h2

       (* Modifies one buffer *)
       let modifies1 (#a:Type0) (b:buffer_t MUT a) (h1 h2:HS.mem) =
         modifies (loc b) h1 h2

       (* Modifies two buffers *)
       let modifies2 (#a0:Type0) (#a1:Type0)
         (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (h1 h2: HS.mem) =
         modifies (loc b0 |+| loc b1) h1 h2

       (* And so on for modifies3, modifies4, modifies5, modifies6 *)

       9.3 Typical Function Pattern

       (* From HACL* cryptographic implementations *)
       inline_for_extraction noextract
       val sha256_update:
           hash: lbuffer uint32 8ul
         -> block: lbuffer uint8 64ul
         -> Stack unit
           (requires fun h0 -> 
             live h0 hash /\ live h0 block /\
             disjoint hash block)
           (ensures fun h0 _ h1 ->
             modifies1 hash h0 h1 /\
             as_seq h1 hash == Spec.SHA2.update (as_seq h0 hash) (as_seq h0 block))

       ---
       10. Common Extraction Patterns

       10.1 Type Translation

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:653-754:

       let rec translate_type_without_decay' env t: typ =
         match t with
         | MLTY_Tuple [] | MLTY_Top -> TAny
         | MLTY_Var name -> TBound (find_t env name)
         | MLTY_Fun (t1, _, t2) -> TArrow (translate_type_without_decay env t1,
                                            translate_type_without_decay env t2)
         | MLTY_Erased -> TUnit

         (* Primitive types *)
         | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.unit") -> TUnit
         | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.bool") -> TBool
         | MLTY_Named ([], ([ "FStar"; m ], "t")) when is_machine_int m ->
             TInt (Option.must (mk_width m))

         (* Buffer types *)
         | MLTY_Named ([arg; _; _], p)
           when Syntax.string_of_mlpath p = "LowStar.Monotonic.Buffer.mbuffer" ->
             TBuf (translate_type_without_decay env arg)

         | MLTY_Named ([arg], p)
           when Syntax.string_of_mlpath p = "LowStar.ConstBuffer.const_buffer" ->
             TConstBuf (translate_type_without_decay env arg)

         (* ... other patterns ... *)

       10.2 Integer Operations

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:430-454:

       let mk_op = function
         | "add" | "add_underspec"  -> Some Add
         | "add_mod"                -> Some AddW      (* Wrapping add *)
         | "sub" | "sub_underspec"  -> Some Sub
         | "sub_mod"                -> Some SubW      (* Wrapping sub *)
         | "mul" | "mul_underspec"  -> Some Mult
         | "mul_mod"                -> Some MultW     (* Wrapping mul *)
         | "div"                    -> Some Div
         | "div_mod"                -> Some DivW
         | "rem"                    -> Some Mod
         | "logor"                  -> Some BOr       (* Bitwise OR *)
         | "logxor"                 -> Some BXor      (* Bitwise XOR *)
         | "logand"                 -> Some BAnd      (* Bitwise AND *)
         | "lognot"                 -> Some BNot      (* Bitwise NOT *)
         | "shift_right"            -> Some BShiftR
         | "shift_left"             -> Some BShiftL
         | "eq"                     -> Some Eq
         | "gt"                     -> Some Gt
         | "gte"                    -> Some Gte
         | "lt"                     -> Some Lt
         | "lte"                    -> Some Lte
         | _                        -> None

       10.3 Cast Operations

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:1104-1128:

       | MLE_App ({ expr = MLE_Name ([ "FStar"; "Int"; "Cast" ], c) }, [ arg ]) ->
           let is_known_type =
             starts_with c "uint8" || starts_with c "uint16" ||
             starts_with c "uint32" || starts_with c "uint64" ||
             starts_with c "int8" || starts_with c "int16" ||
             starts_with c "int32" || starts_with c "int64"
           in
           if ends_with c "uint64" && is_known_type then
             ECast (translate_expr env arg, TInt UInt64)
           else if ends_with c "uint32" && is_known_type then
             ECast (translate_expr env arg, TInt UInt32)
           (* ... similar for other widths ... *)

       ---
       11. Debugging C Extraction Issues

       11.1 Common Errors

       1. Polymorphic Assumptions Not Supported

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:1354-1360:

       if List.length tvars = 0 then
         Some (DExternal (...))
       else begin
         Format.print1_warning 
           "Not extracting %s to KaRaMeL (polymorphic assumes are not supported)\n"
           (Syntax.string_of_mlpath name);
         None
       end

       Solution: Instantiate polymorphic types before assuming.

       2. Type Annotation Mismatch

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:1382-1387:

       if i > 0 && not (Options.silent ()) then begin
         let msg = "function type annotation has less arrows than the \
           number of arguments; please mark the return type abbreviation as \
           inline_for_extraction" in
         Format.print2_warning "Not extracting %s to KaRaMeL (%s)\n"
           (Syntax.string_of_mlpath name) msg
       end

       Solution: Add inline_for_extraction to type abbreviations used as return types.

       3. List Literal Required

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:509-513:

       let list_elements e =
         let lopt = FStarC.Extraction.ML.Util.list_elements e in
         match lopt with
         | None -> failwith "Argument of FStar.Buffer.createL is not a list literal!"
         | Some l -> l

       Solution: Use explicit list literals [e1; e2; e3] instead of computed lists.

       11.2 Extraction Extension Points

       Karamel supports extension hooks for custom translation. From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:550-573:

       exception NotSupportedByKrmlExtension

       let translate_type_without_decay_t = env -> mlty -> ML typ
       let ref_translate_type_without_decay : ref translate_type_without_decay_t =
         mk_ref (fun _ _ -> raise NotSupportedByKrmlExtension)

       let register_pre_translate_type_without_decay (f: translate_type_without_decay_t) : ML unit =
         let before = !ref_translate_type_without_decay in
         let after = fun e t ->
           try f e t
           with NotSupportedByKrmlExtension -> before e t
         in
         ref_translate_type_without_decay := after

       This allows plugins to extend the extraction with custom type and expression handlers.

       11.3 Debugging Tips

       1. Enable verbose extraction: Use --silent false to see warnings
       2. Check type annotations: Ensure all function types have proper annotations
       3. Verify effects: Make sure effects are compatible with Low* (Stack, ST, StackInline)
       4. Inspect ML IR: Use --dump_module to see the intermediate ML representation
       5. Check monomorphization: Ensure polymorphism is resolved before extraction

       ---
       12. Karamel-Specific Constructs

       12.1 Comments

       From /home/grigory/Downloads/FStar/ulib/LowStar.Comment.fsti:1-29:

       (* Wrapping expression with comments *)
       val comment_gen: #t: Type -> before: string -> body: t -> after: string -> Pure t
         (requires (True))
         (ensures (fun res -> res == body))

       (* Standalone comment *)
       val comment (s: string) : Stack unit
         (requires (fun _ -> True))
         (ensures (fun h _ h' -> h == h'))

       Extracts to C as:

       /* before */
       body_code;
       /* after */

       12.2 Calling Conventions

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:64-68:

       and cc =
         | StdCall    (* __stdcall *)
         | CDecl      (* __cdecl *)
         | FastCall   (* __fastcall *)

       12.3 Flags for C Generation

       From /home/grigory/Downloads/FStar/src/extraction/FStarC.Extraction.Krml.fst:75-90:

       and flag =
         | Private           (* static in C *)
         | WipeBody          (* Erase function body *)
         | CInline           (* inline hint *)
         | Substitute        (* Full inlining *)
         | GCType            (* GC-managed type *)
         | Comment of string (* Attach comment *)
         | MustDisappear     (* Must be eliminated *)
         | Const of string   (* const qualifier *)
         | Prologue of string(* Code before definition *)
         | Epilogue of string(* Code after definition *)
         | Abstract          (* Abstract type *)
         | IfDef             (* Wrap in #ifdef *)
         | Macro             (* Extract as macro *)
         | Deprecated of string (* Mark as deprecated *)
         | CNoInline         (* __noinline hint *)

       ---
       Summary

       The Low*/Karamel extraction pipeline provides a verified path from F* to C:

       1. Low Library* (LowStar.*): Provides buffer types and memory management primitives with precise specifications
       2. Effect System: Stack, ST, and StackInline effects track memory discipline
       3. Modifies Clauses: Location-based framing for reasoning about memory modifications
       4. Karamel IR: A C-like intermediate representation capturing Low* programs
       5. Extraction: Pattern matching on F*/ML constructs to generate Karamel IR
       6. Annotations: inline_for_extraction, noextract, and various C-specific attributes control extraction behavior

       The resulting C code is readable, efficient, and inherits the correctness guarantees proven in F*. HACL* demonstrates that this approach scales to real cryptographic implementations with thousands of lines of verified code.
  ⎿  Done (19 tool uses · 156.1k tokens · 3m 30s)

● elite-bug-hunter(F* Ch14: Standard Library)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering THE STANDARD LIBRARY (ulib).

       Explore /home/grigory/Downloads/FStar/ulib/ extensively.

       Focus on:
       1. Read FStar.List.Tot.fst - document list operations with specs
       2. Read FStar.Seq.fst - document sequence operations
       3. Read FStar.Set.fst and FStar.Map.fst - document collections
       4. Read FStar.Classical.fst - document classical logic axioms
       5. Read FStar.Calc.fst - document calculational proofs
       6. Read FStar.Math.Lemmas.fst - document math lemmas
       7. Read FStar.Ghost.fst - document ghost/erased types
       8. Read FStar.Pervasives.fst - document built-in types

       Your chapter should include:
       - Library organization (Tot vs effectful versions)
       - List operations and lemmas
       - Sequence operations and lemmas
       - Set and Map APIs
       - Classical logic usage
       - Calculational proofs
       - Mathematical lemmas available
       - Ghost and erased types
       - Type classes (Class.Eq, etc.)
       - Module organization guide

       Read at least 15 files in ulib/. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have enough material to write the comprehensive documentation chapter. Let me compile this into a detailed technical document.

       ---
       THE F* STANDARD LIBRARY (ulib): A COMPREHENSIVE REFERENCE

       Table of Contents

       1. Library Organization and Overview
       2. Core Modules (Prims and FStar.Pervasives)
       3. List Operations and Lemmas (FStar.List.Tot)
       4. Sequence Operations (FStar.Seq)
       5. Set and Map Collections
       6. Classical Logic (FStar.Classical)
       7. Calculational Proofs (FStar.Calc)
       8. Mathematical Lemmas (FStar.Math.Lemmas)
       9. Ghost and Erased Types
       10. Squash Types and Proof Irrelevance
       11. Functional Extensionality
       12. Type Classes
       13. Module Organization Guide

       ---
       1. Library Organization and Overview

       The F* standard library is located in the ulib/ directory and follows a consistent organizational pattern. Understanding this structure is essential for effective F* programming.

       1.1 Tot vs Effectful Versions

       F* distinguishes between pure total functions and effectful computations. The library reflects this separation:

       Pure Total Modules (.Tot. suffix):
       - FStar.List.Tot.Base - Pure list operations with Tot effect
       - FStar.List.Tot.Properties - Lemmas about list operations

       Effectful Modules:
       - FStar.List.fst - List operations that may involve effects (ML, exceptions)
       - FStar.HyperStack.ST - Stateful computations

       Pattern:
       FStar.List.Tot.Base.fst    -- Pure total functions
       FStar.List.Tot.Properties.fst  -- Lemmas with SMT patterns
       FStar.List.fst             -- Effectful wrappers

       1.2 Interface (.fsti) vs Implementation (.fst)

       The library uses F*'s interface/implementation separation:
       - .fsti files declare signatures with pre/post conditions
       - .fst files provide implementations
       - This enables modular verification and information hiding

       1.3 Library Hierarchy

       Prims                    -- Primitive types and effects (built-in)
       FStar.Pervasives         -- Utility types, effects, control flow
       FStar.Pervasives.Native  -- Native tuples (tuple2, tuple3, ...)
         |
         +-- FStar.Squash       -- Proof irrelevance
         +-- FStar.Classical    -- Classical logic combinators
         +-- FStar.Ghost        -- Erased types
         |
         +-- Data Structures
         |   +-- FStar.List.Tot.*  -- Pure total lists
         |   +-- FStar.Seq.*       -- Sequences (arrays)
         |   +-- FStar.Set         -- Computational sets
         |   +-- FStar.Map         -- Partial maps
         |
         +-- Mathematics
         |   +-- FStar.Math.Lemmas  -- Integer lemmas
         |   +-- FStar.Math.Lib     -- Math functions
         |   +-- FStar.Math.Euclid  -- GCD, Bezout
         |
         +-- Effects
             +-- FStar.ST           -- State
             +-- FStar.HyperStack   -- Regions and frames

       ---
       2. Core Modules (Prims and FStar.Pervasives)

       2.1 Prims: The Foundation

       Prims is the primordial module automatically opened in all F* programs. Key definitions:

       // Basic types (from Prims)
       type bool = True | False
       type int : eqtype           // Mathematical integers
       type nat = i:int{i >= 0}    // Natural numbers
       type pos = i:int{i > 0}     // Positive integers

       // Squash type for proof irrelevance
       type squash (p:Type) = x:unit{p}

       // Logical connectives (squashed)
       let l_and (p q:Type) = squash (p /\ q)
       let l_or (p q:Type) = squash (p \/ q)
       let l_imp (p q:Type) = squash (p ==> q)

       // Effects
       total effect Tot (a:Type) = ...  // Total, terminating
       effect GTot (a:Type) = ...       // Ghost total (erased at extraction)
       effect Pure (a:Type) (pre:Type) (post:a -> Type) = ...

       2.2 FStar.Pervasives: Utility Definitions

       File: /home/grigory/Downloads/FStar/ulib/FStar.Pervasives.fsti

       Lemma Effect (lines 88-113):
       (** Lemma is desugared specially. Valid forms:
            Lemma (ensures post)
            Lemma (requires pre) (ensures post)
            Lemma (requires pre) (ensures post) [SMTPat ...] *)
       effect Lemma (a: eqtype_u) (pre: Type) (post: (squash pre -> Type)) (pats: list pattern) =
         Pure a pre (fun r -> post ())

       SMT Patterns (lines 57-74):
       (** Values of type [pattern] are used to tag Lemmas with SMT triggers *)
       type pattern : Type0 = unit

       val smt_pat (#a: Type) (x: a) : Tot pattern
       val smt_pat_or (x: list (list pattern)) : Tot pattern

       Either Type (lines 584-586):
       type either a b =
         | Inl : v: a -> either a b
         | Inr : v: b -> either a b

       Dependent Tuples (lines 597-615):
       (** Dependent triples: [x:a & y:b x & c x y] *)
       unopteq type dtuple3 (a: Type) (b: (a -> GTot Type)) (c: (x: a -> b x -> GTot Type)) =
         | Mkdtuple3 : _1: a -> _2: b _1 -> _3: c _1 _2 -> dtuple3 a b c

       (** Projections *)
       let dfst (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot a = Mkdtuple2?._1 t
       let dsnd (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot (b (Mkdtuple2?._1 t)) = Mkdtuple2?._2 t

       Normalization Control (lines 152-184):
       (** Reduce [e] completely during normalization *)
       val normalize_term (#a: Type) (x: a) : Tot a

       (** [norm s e] requests normalization of [e] with steps [s] *)
       val norm (s: list norm_step) (#a: Type) (x: a) : Tot a

       (** [assert_norm p] reduces [p] and proves the reduct *)
       val assert_norm (p: Type) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))

       (** Reveal opaque definitions to SMT *)
       let reveal_opaque (s: string) = norm_spec [delta_once [s]]

       Inversion Control (lines 554-576):
       (** [inversion t] allows SMT to invert type [t] regardless of ifuel *)
       val inversion (a: Type) : Type0

       (** Introduce inversion into SMT context *)
       val allow_inversion (a: Type) : Pure unit (requires True) (ensures (fun x -> inversion a))

       ---
       3. List Operations and Lemmas (FStar.List.Tot)

       3.1 Base Operations

       File: /home/grigory/Downloads/FStar/ulib/FStar.List.Tot.Base.fst

       Basic Destructors (lines 30-77):
       (** [isEmpty l] returns true iff [l] is empty *)
       val isEmpty: list 'a -> Tot bool
       let isEmpty l = match l with
         | [] -> true
         | _ -> false

       (** [hd l] returns the first element. Requires [Cons? l] *)
       val hd: l:list 'a{Cons? l} -> Tot 'a
       let hd = function | hd::_ -> hd

       (** [tl l] returns list without first element. Requires [Cons? l] *)
       val tl: l:list 'a {Cons? l} -> Tot (list 'a)
       let tl = function | _::tl -> tl

       (** [length l] returns total number of elements *)
       val length: list 'a -> Tot nat
       let rec length = function
         | [] -> 0
         | _::tl -> 1 + length tl

       (** [nth l n] returns [n]-th element or [None] if out of bounds *)
       val nth: list 'a -> nat -> Tot (option 'a)
       let rec nth l n = match l with
         | []     -> None
         | hd::tl -> if n = 0 then Some hd else nth tl (n - 1)

       (** [index l i] returns [i]-th element. Requires [i < length l] *)
       val index: #a:Type -> l:list a -> i:nat{i < length l} -> Tot a
       let rec index #a (l: list a) (i:nat{i < length l}): Tot a =
         if i = 0 then hd l else index (tl l) (i - 1)

       Core Transformations (lines 104-197):
       (** [rev l] reverses list [l] using tail-recursive accumulator *)
       val rev_acc: list 'a -> list 'a -> Tot (list 'a)
       let rec rev_acc l acc = match l with
           | [] -> acc
           | hd::tl -> rev_acc tl (hd::acc)

       val rev: list 'a -> Tot (list 'a)
       let rev l = rev_acc l []

       (** [append l1 l2] appends [l2] to end of [l1]. Notation: [@] *)
       val append: list 'a -> list 'a -> Tot (list 'a)
       let rec append x y = match x with
         | [] -> y
         | a::tl -> a::append tl y

       let op_At x y = append x y

       (** [map f l] applies [f] to each element *)
       val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
       let rec map f x = match x with
         | [] -> []
         | a::tl -> f a::map f tl

       (** [fold_left f x [y1;...;yn]] computes (f (... (f x y1) y2) ... yn) *)
       val fold_left: ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
       let rec fold_left f x l = match l with
         | [] -> x
         | hd::tl -> fold_left f (f x hd) tl

       (** [fold_right f [x1;...;xn] y] computes (f x1 (f x2 (... (f xn y)))) *)
       val fold_right: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
       let rec fold_right f l x = match l with
         | [] -> x
         | hd::tl -> f hd (fold_right f tl x)

       Membership (lines 223-248):
       (** Propositional membership (does not require decidable equality) *)
       let rec memP (#a: Type) (x: a) (l: list a) : Tot Type0 =
         match l with
         | [] -> False
         | y :: q -> x == y \/ memP x q

       (** Boolean membership (requires eqtype) *)
       val mem: #a:eqtype -> a -> list a -> Tot bool
       let rec mem #a x = function
         | [] -> false
         | hd::tl -> if hd = x then true else mem x tl

       Filtering and Searching (lines 260-381):
       (** [filter f l] keeps elements where [f x] is true *)
       val filter : #a: Type -> f:(a -> Tot bool) -> l: list a -> Tot (list a)
       let rec filter #a f = function
         | [] -> []
         | hd::tl -> if f hd then hd::filter f tl else filter f tl

       (** [find f l] returns [Some x] where [f x] holds, with refinement *)
       val find: #a:Type -> f:(a -> Tot bool) -> list a -> Tot (option (x:a{f x}))
       let rec find #a f l = match l with
         | [] -> None #(x:a{f x})
         | hd::tl -> if f hd then Some #(x:a{f x}) hd else find f tl

       (** [for_all f l] returns true iff [f x] holds for all [x] in [l] *)
       val for_all: ('a -> Tot bool) -> list 'a -> Tot bool
       let rec for_all f l = match l with
           | [] -> true
           | hd::tl -> if f hd then for_all f tl else false

       (** [partition f l] splits [l] into elements satisfying [f] and not *)
       val partition: f:('a -> Tot bool) -> list 'a -> Tot (list 'a & list 'a)
       let rec partition f = function
         | [] -> [], []
         | hd::tl ->
            let l1, l2 = partition f tl in
            if f hd then hd::l1, l2 else l1, hd::l2

       Association Lists (lines 425-443):
       (** [assoc x l] returns [Some y] for first [(x, y)] in [l], or [None] *)
       val assoc: #a:eqtype -> #b:Type -> a -> list (a & b) -> Tot (option b)
       let rec assoc #a #b x = function
         | [] -> None
         | (x', y)::tl -> if x=x' then Some y else assoc x tl

       (** [split [(x1,y1);...]] returns ([x1;...], [y1;...]) *)
       val split: list ('a & 'b) -> Tot (list 'a & list 'b)
       let rec split l = match l with
           | [] -> ([],[])
           | (hd1,hd2)::tl ->
              let (tl1,tl2) = split tl in
              (hd1::tl1,hd2::tl2)

       Sorting (lines 498-549):
       (** [sortWith compare l] sorts [l] using comparison function *)
       val sortWith: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
       let rec sortWith f = function
         | [] -> []
         | pivot::tl ->
            let hi, lo = partition (bool_of_compare f pivot) tl in
            partition_length (bool_of_compare f pivot) tl;
            append (sortWith f lo) (pivot::sortWith f hi)

       3.2 List Properties and Lemmas

       File: /home/grigory/Downloads/FStar/ulib/FStar.List.Tot.Properties.fst

       Membership Lemmas (lines 31-104):
       (** Correctness of [mem] for eqtypes *)
       let rec mem_memP (#a: eqtype) (x: a) (l: list a)
       : Lemma (ensures (mem x l <==> memP x l))
               [SMTPat (mem x l); SMTPat (memP x l)]
       = match l with
         | [] -> ()
         | a :: q -> mem_memP x q

       (** Indexed element is a member of the list *)
       let rec lemma_index_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
         Lemma (ensures (index l i `memP` l))
               [SMTPat (index l i `memP` l)]
       = match i with
         | 0 -> ()
         | _ -> lemma_index_memP (tl l) (i - 1)

       Append Properties (lines 123-234):
       let append_nil_l l = ()

       let rec append_l_nil = function
         | [] -> ()
         | hd::tl -> append_l_nil tl

       (** Associativity of append *)
       let rec append_assoc l1 l2 l3 = match l1 with
           | [] -> ()
           | hd::tl -> append_assoc tl l2 l3

       (** Length of append *)
       let rec append_length l1 l2 = match l1 with
         | [] -> ()
         | hd::tl -> append_length tl l2

       (** Membership in append *)
       let rec append_mem #t l1 l2 a = match l1 with
         | [] -> ()
         | hd::tl -> append_mem tl l2 a

       (** Injectivity of append *)
       let append_injective #a (l0 l0':list a) (l1 l1':list a)
         : Lemma (ensures (length l0 == length l0' \/ length l1 == length l1') /\
                          append l0 l1 == append l0' l1' ==> l0 == l0' /\ l1 == l1')

       Sort Correctness (lines 412-453):
       (** sortWith is a permutation: preserves element counts *)
       let rec sortWith_permutation #a f l :
         Lemma (ensures forall x. count x l = count x (sortWith f l))
               (decreases length l)
       = match l with
           | [] -> ()
           | pivot::tl ->
              partition_count_forall (bool_of_compare f pivot) tl;
              sortWith_permutation f lo;
              sortWith_permutation f hi;
              append_count_forall (sortWith f lo) (pivot::sortWith f hi)

       (** sortWith produces sorted output *)
       let rec sortWith_sorted (#a:eqtype) (f:(a -> a -> Tot int)) (l:list a) :
         Lemma (requires (total_order #a (bool_of_compare f)))
               (ensures ((sorted (bool_of_compare f) (sortWith f l)) /\ 
                         (forall x. mem x l = mem x (sortWith f l))))
               (decreases length l)

       Fold Properties (lines 691-772):
       (** Fold invariant: if [p] is preserved by [f], fold preserves [p] *)
       let rec fold_left_invar (#a #b: Type) (f: (a -> b -> Tot a)) (l: list b) (p: (a -> Tot Type0))
         : Lemma (requires forall (x: a) (y: b) . p x ==> memP y l ==> p (f x y))
                 (ensures forall (x: a) . p x ==> p (fold_left f x l))
       = match l with
         | [] -> ()
         | y :: q -> fold_left_invar f q p

       (** Fold distributes over append *)
       let rec fold_left_append (#a #b: Type) (f: a -> b -> Tot a) (l1 l2: list b)
         : Lemma (ensures forall x . fold_left f x (l1 @ l2) == fold_left f (fold_left f x l1) l2)
       = match l1 with
         | [] -> ()
         | x :: q -> fold_left_append f q l2

       ---
       4. Sequence Operations (FStar.Seq)

       4.1 Base Operations

       File: /home/grigory/Downloads/FStar/ulib/FStar.Seq.Base.fsti

       Sequences are the primary indexed collection type in F*, providing efficient array-like semantics with verification support.

       Core Type and Constructors (lines 23-64):
       (** Abstract sequence type *)
       new val seq ([@@@strictly_positive] a : Type u#a) : Type u#a

       (** Get length of sequence *)
       val length: #a:Type -> seq a -> Tot nat

       (** Index into sequence (requires bounds check) *)
       val index: #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a

       (** Create sequence of [n] copies of [v] *)
       val create: #a:Type -> nat -> a -> Tot (seq a)

       (** Initialize sequence with function *)
       val init: #a:Type -> len:nat -> contents:(i:nat{i < len} -> Tot a) -> Tot (seq a)

       (** Empty sequence *)
       val empty (#a:Type) : Tot (s:(seq a){length s=0})

       (** Update element at index *)
       val upd: #a:Type -> s:seq a -> n:nat{n < length s} -> a -> Tot (seq a)

       (** Append two sequences *)
       val append: #a:Type -> seq a -> seq a -> Tot (seq a)

       (** Cons element to front *)
       let cons (#a:Type) (x:a) (s:seq a) : Tot (seq a) = append (create 1 x) s

       (** Infix append notation *)
       let op_At_Bar (#a:Type) (s1:seq a) (s2:seq a) = append s1 s2

       (** Extract subsequence [i, j) *)
       val slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)

       List Conversion (lines 66-89):
       (** Convert sequence to list *)
       val seq_to_list (#a:Type) (s:seq a) : Tot (l:list a{List.length l == length s})

       (** Convert list to sequence *)
       val seq_of_list (#a:Type) (l:list a) : Tot (s:seq a{List.length l == length s})

       (** Round-trip lemmas *)
       val lemma_seq_of_seq_to_list : #a:Type -> s:seq a ->
         Lemma (ensures seq_of_list (seq_to_list s) == s)
               [SMTPat (seq_of_list (seq_to_list s))]

       val lemma_seq_to_seq_of_list : #a:Type -> l:list a ->
         Lemma (ensures seq_to_list (seq_of_list l) == l)
               [SMTPat (seq_to_list (seq_of_list l))]

       Length Lemmas with SMT Patterns (lines 91-130):
       val lemma_create_len: #a:Type -> n:nat -> v:a -> Lemma
         (ensures (length (create n v) = n))
         [SMTPat (length (create n v))]

       val lemma_len_upd: #a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
         (ensures (length (upd s n v) = length s))
         [SMTPat (length (upd s n v))]

       val lemma_len_append: #a:Type -> s1:seq a -> s2:seq a -> Lemma
         (ensures (length (append s1 s2) = length s1 + length s2))
         [SMTPat (length (append s1 s2))]

       val lemma_len_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
         (ensures (length (slice s i j) = j - i))
         [SMTPat (length (slice s i j))]

       Index Lemmas (lines 132-161):
       val lemma_index_create: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
         (ensures (index (create n v) i == v))
         [SMTPat (index (create n v) i)]

       val lemma_index_upd1: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
         (ensures (index (upd s n v) n == v))
         [SMTPat (index (upd s n v) n)]

       val lemma_index_upd2: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a ->
                             i:nat{i<>n /\ i < length s} -> Lemma
         (ensures (index (upd s n v) i == index s i))
         [SMTPat (index (upd s n v) i)]

       val lemma_index_app1: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
         (ensures (index (append s1 s2) i == index s1 i))
         [SMTPat (index (append s1 s2) i)]

       val lemma_index_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} ->
                              k:nat{k < j - i} -> Lemma
         (ensures (index (slice s i j) k == index s (k + i)))
         [SMTPat (index (slice s i j) k)]

       Equality (lines 163-190):
       (** Extensional equality of sequences *)
       val equal (#a:Type) (s1:seq a) (s2:seq a) : Tot prop

       (** Decidable equality for eqtypes *)
       val eq: #a:eqtype -> s1:seq a -> s2:seq a -> Tot (r:bool{r <==> equal s1 s2})

       (** Introduction: pointwise equality implies [equal] *)
       val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
            (requires (length s1 = length s2 /\
                      (forall (i:nat{i < length s1}). index s1 i == index s2 i)))
            (ensures (equal s1 s2))
            [SMTPat (equal s1 s2)]

       (** Elimination: [equal] implies propositional equality *)
       val lemma_eq_elim: #a:Type -> s1:seq a -> s2:seq a -> Lemma
            (requires (equal s1 s2))
            (ensures (s1==s2))
            [SMTPat (equal s1 s2)]

       4.2 Sequence Properties

       File: /home/grigory/Downloads/FStar/ulib/FStar.Seq.Properties.fsti

       Length-Bounded Sequences (lines 22-25):
       (** Sequence with statically known length *)
       let lseq (a: Type) (l: nat) : Tot Type = s: Seq.seq a { Seq.length s == l }

       let indexable (#a:Type) (s:Seq.seq a) (j:int) = 0 <= j /\ j < Seq.length s

       Head/Tail Operations (lines 40-50):
       let head (#a:Type) (s:seq a{length s > 0}) : Tot a = index s 0
       let tail (#a:Type) (s:seq a{length s > 0}) : Tot (seq a) = slice s 1 (length s)
       let last (#a:Type) (s:seq a{length s > 0}) : Tot a = index s (length s - 1)

       Membership and Count (lines 71-92):
       (** Count occurrences of [x] in [s] *)
       let rec count (#a:eqtype) (x:a) (s:seq a) : Tot nat (decreases (length s))
       = if length s = 0 then 0
         else if head s = x then 1 + count x (tail s)
         else count x (tail s)

       (** Boolean membership *)
       let mem (#a:eqtype) (x:a) (l:seq a) : Tot bool = count x l > 0

       (** Find index of first occurrence *)
       let rec index_mem (#a:eqtype) (x:a) (s:seq a)
           : Pure nat (requires (mem x s))
                      (ensures (fun i -> i < length s /\ index s i == x))
                      (decreases (length s))
           = if head s = x then 0 else 1 + index_mem x (tail s)

       Permutations (lines 195-212):
       (** Permutation: same count of every element *)
       type permutation (a:eqtype) (s1:seq a) (s2:seq a) =
              (forall i. count i s1 = count i s2)

       (** Swap creates permutation *)
       val lemma_swap_permutes (#a:eqtype) (s:seq a) (i:nat{i<length s}) (j:nat{i <= j && j<length s})
         : Lemma (permutation a s (swap s i j))

       (** Permutation preserves length *)
       val perm_len (#a:eqtype) (s1 s2: seq a)
         : Lemma (requires (permutation a s1 s2))
                 (ensures  (length s1 == length s2))

       Snoc Operations (lines 316-331):
       (** Append single element to end *)
       let snoc (#a:Type) (s:seq a) (x:a) : Tot (seq a) = Seq.append s (Seq.create 1 x)

       (** Inverse of snoc *)
       let un_snoc (#a:Type) (s:seq a{length s <> 0}) : Tot (r:(seq a & a){s == snoc (fst r) (snd r)})

       val un_snoc_snoc (#a:Type) (s:seq a) (x:a) : Lemma (un_snoc (snoc s x) == (s, x))

       Contains (Undecidable Membership) (lines 460-495):
       (** [contains] doesn't require eqtype, unlike [mem] *)
       val contains (#a:Type) (s:seq a) (x:a) : Tot Type0

       val contains_intro (#a:Type) (s:seq a) (k:nat) (x:a)
         : Lemma (k < Seq.length s /\ Seq.index s k == x ==> s `contains` x)

       val append_contains_equiv (#a:Type) (s1:seq a) (s2:seq a) (x:a)
         : Lemma ((append s1 s2) `contains` x <==> (s1 `contains` x \/ s2 `contains` x))

       Sorting (lines 710-737):
       (** Sort sequence using comparison function *)
       let sortWith (#a:eqtype) (f:a -> a -> Tot int) (s:seq a) :Tot (seq a)
         = seq_of_list (List.Tot.Base.sortWith f (seq_to_list s))

       (** Correctness of sortWith *)
       val lemma_seq_sortwith_correctness (#a:eqtype) (f:a -> a -> Tot int) (s:seq a)
         :Lemma (requires (total_order a (List.Tot.Base.bool_of_compare f)))
                (ensures  (let s' = sortWith f s in 
                           sorted (List.Tot.Base.bool_of_compare f) s' /\ permutation a s s'))

       Folding and Mapping (lines 739-762):
       let rec foldr (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
         : Tot a (decreases (length s))
         = if length s = 0 then init
           else f (head s) (foldr f (tail s) init)

       val map_seq (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) : Tot (Seq.seq b)

       val map_seq_len (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a)
         : Lemma (ensures Seq.length (map_seq f s) == Seq.length s)

       val map_seq_index (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) (i:nat{i < Seq.length s})
         : Lemma (ensures (map_seq_len f s; Seq.index (map_seq f s) i == f (Seq.index s i)))

       ---
       5. Set and Map Collections

       5.1 Computational Sets (FStar.Set)

       File: /home/grigory/Downloads/FStar/ulib/FStar.Set.fsti

       (** Computational sets on eqtypes: membership is boolean *)
       val set (a:eqtype) : Type0

       (** Membership test *)
       val mem (#a:eqtype) (x:a) (s:set a) : Tot bool

       (** Constructors *)
       val empty (#a:eqtype) : Tot (set a)
       val singleton (#a:eqtype) (x:a) : Tot (set a)
       val union (#a:eqtype) : set a -> set a -> Tot (set a)
       val intersect (#a:eqtype) : set a -> set a -> Tot (set a)
       val complement (#a:eqtype) : set a -> Tot (set a)
       val intension (#a:eqtype) : (a -> Tot bool) -> GTot (set a)

       (** Derived operations *)
       let disjoint (#a:eqtype) (s1: set a) (s2: set a) = equal (intersect s1 s2) empty
       let subset (#a:eqtype) (s1:set a) (s2:set a) = forall x. mem x s1 ==> mem x s2
       let add (#a:eqtype) (x:a) (s:set a) : set a = union s (singleton x)
       let remove (#a:eqtype) (x:a) (s:set a) : set a = intersect s (complement (singleton x))

       Key Lemmas (lines 58-118):
       val mem_empty: #a:eqtype -> x:a -> Lemma
          (ensures (not (mem x empty)))
          [SMTPat (mem x empty)]

       val mem_singleton: #a:eqtype -> x:a -> y:a -> Lemma
          (ensures (mem y (singleton x) = (x=y)))
          [SMTPat (mem y (singleton x))]

       val mem_union: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
          (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
          [SMTPat (mem x (union s1 s2))]

       val mem_intersect: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
          (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
          [SMTPat (mem x (intersect s1 s2))]

       (** Extensionality: sets with same membership are equal *)
       val lemma_equal_intro: #a:eqtype -> s1:set a -> s2:set a -> Lemma
           (requires  (forall x. mem x s1 = mem x s2))
           (ensures (equal s1 s2))
           [SMTPat (equal s1 s2)]

       val lemma_equal_elim: #a:eqtype -> s1:set a -> s2:set a -> Lemma
           (requires (equal s1 s2))
           (ensures  (s1 == s2))
           [SMTPat (equal s1 s2)]

       List Conversion (lines 121-128):
       (** Convert list to set, normalizing at compile time *)
       let rec as_set' (#a:eqtype) (l:list a) : set a =
         match l with
         | [] -> empty
         | hd::tl -> union (singleton hd) (as_set' tl)

       unfold let as_set (#a:eqtype) (l:list a) = normalize_term (as_set' l)

       5.2 Partial Maps (FStar.Map)

       File: /home/grigory/Downloads/FStar/ulib/FStar.Map.fsti

       (** Partial map from keys to values. A map is:
           1. A total function [key -> value]
           2. A set of keys (the domain) *)
       val t (key:eqtype) ([@@@strictly_positive] value:Type u#a) : Type u#a

       (** Lookup key in map *)
       val sel: #key:eqtype -> #value:Type -> t key value -> key -> Tot value

       (** Update/insert key-value pair *)
       val upd: #key:eqtype -> #value:Type -> t key value -> key -> value -> Tot (t key value)

       (** Constant map: all keys map to [v] *)
       val const: #key:eqtype -> #value:Type -> value -> Tot (t key value)

       (** Domain of the map as a set *)
       val domain: #key:eqtype -> #value:Type -> t key value -> Tot (S.set key)

       (** Check if key is in domain *)
       val contains: #key:eqtype -> #value:Type -> t key value -> key -> Tot bool

       (** Merge maps: [m1] takes precedence *)
       val concat: #key:eqtype -> #value:Type -> t key value -> t key value -> Tot (t key value)

       (** Apply function to all values *)
       val map_val: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> 
                    t key val1 -> Tot (t key val2)

       (** Restrict domain to intersection with set *)
       val restrict: #key:eqtype -> #value:Type -> S.set key -> t key value -> Tot (t key value)

       (** Partial constant map on given domain *)
       let const_on (#key:eqtype) (#value:Type) (dom:S.set key) (v:value) : t key value
         = restrict dom (const v)

       Selection Lemmas (lines 95-121):
       val lemma_SelUpd1: #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
                          Lemma (ensures (sel (upd m k v) k == v))
                          [SMTPat (sel (upd m k v) k)]

       val lemma_SelUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                          Lemma (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1))
                          [SMTPat (sel (upd m k2 v) k1)]

       val lemma_SelConst: #key:eqtype -> #value:Type -> v:value -> k:key ->
                           Lemma (ensures (sel (const v) k == v))
                           [SMTPat (sel (const v) k)]

       val lemma_SelRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:S.set key -> k:key ->
                              Lemma (ensures (sel (restrict ks m) k == sel m k))
                              [SMTPat (sel (restrict ks m) k)]

       Domain Lemmas (lines 123-158):
       val lemma_InDomUpd1: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                            Lemma (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                            [SMTPat (contains (upd m k1 v) k2)]

       val lemma_ContainsDom: #key:eqtype -> #value:Type -> m:t key value -> k:key ->
         Lemma (ensures (contains m k = S.mem k (domain m)))
               [SMTPatOr[[SMTPat (contains m k)]; [SMTPat (S.mem k (domain m))]]]

       val lemma_UpdDomain : #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
         Lemma (ensures (S.equal (domain (upd m k v)) (S.union (domain m) (S.singleton k))))
               [SMTPat (domain (upd m k v))]

       Extensional Equality (lines 161-189):
       (** Maps are equal iff same domain and pointwise equal *)
       val equal (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) : prop

       val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                              Lemma (requires (forall k. sel m1 k == sel m2 k /\
                                                    contains m1 k = contains m2 k))
                                    (ensures (equal m1 m2))
                                    [SMTPat (equal m1 m2)]

       val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                             Lemma (ensures (equal m1 m2 <==> m1 == m2))
                                   [SMTPat (equal m1 m2)]

       ---
       6. Classical Logic (FStar.Classical)

       File: /home/grigory/Downloads/FStar/ulib/FStar.Classical.fsti

       This module provides utilities for manipulating squashed logical connectives (==>, /\, \/, forall, exists, ==).

       6.1 Witness Introduction

       (** Transform constructive proof into proof-irrelevant postcondition *)
       val give_witness (#a: Type) (_: a) : Lemma (ensures a)

       (** Move from unit refinement to postcondition *)
       val give_witness_from_squash (#a: Type) (_: squash a) : Lemma (ensures a)

       6.2 Implication Handling (lines 56-125)

       (** Convert [a ==> b] to [squash a -> squash b] *)
       val impl_to_arrow (#a #b: Type0) (_: (a ==> b)) (_: squash a) : Tot (squash b)

       (** Converse of impl_to_arrow *)
       val arrow_to_impl (#a #b: Type0) (_: (squash a -> GTot (squash b))) : GTot (a ==> b)

       (** Introduce implication from function *)
       val impl_intro (#p #q: Type0) ($_: (p -> Lemma q)) : Lemma (p ==> q)

       (** Move lemma precondition to implication postcondition *)
       val move_requires (#a: Type) (#p #q: (a -> Type))
             ($_: (x: a -> Lemma (requires (p x)) (ensures (q x)))) (x: a)
           : Lemma (p x ==> q x)

       (** Arity-2 version *)
       val move_requires_2 (#a: Type) (#b: (a -> Type)) (#p #q: (x: a -> b x -> Type))
             ($_: (x: a -> y: b x -> Lemma (requires (p x y)) (ensures (q x y)))) (x: a) (y: b x)
           : Lemma (p x y ==> q x y)

       6.3 Universal Quantification (lines 127-337)

       The section provides guidance on when to use forall_intro vs SMT patterns:

       (** Key insight from the documentation (lines 140-195):
           
           Local lemmas with SMT patterns are often more robust than forall_intro:
           
           let proof2 =
             let lem (x:nat) : Lemma (ensures p x) [SMTPat (p x)] = admit() in
             assert (forall x. p x)    // SMT proves this using lem
           
           Advantages of SMT pattern approach:
           1. Works with lemmas that have preconditions
           2. Produces quantifiers WITH patterns (better SMT performance)
           3. Works at arbitrary arity
       *)

       (** Main quantifier introduction *)
       val forall_intro (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> Lemma (p x)))
           : Lemma (forall (x: a). p x)

       (** With explicit SMT pattern *)
       val forall_intro_with_pat (#a: Type) (#c: (x: a -> Type)) (#p: (x: a -> GTot Type0))
             ($pat: (x: a -> Tot (c x))) ($_: (x: a -> Lemma (p x)))
           : Lemma (forall (x: a). {:pattern (pat x)} p x)

       (** Higher arities *)
       val forall_intro_2 (#a: Type) (#b: (a -> Type)) (#p: (x: a -> b x -> GTot Type0))
             ($_: (x: a -> y: b x -> Lemma (p x y)))
           : Lemma (forall (x: a) (y: b x). p x y)

       val forall_intro_3 (...) : Lemma (forall (x: a) (y: b x) (z: c x y). p x y z)
       val forall_intro_4 (...) : Lemma (forall ... w: d x y z). p x y z w)

       (** For lemmas with preconditions *)
       val ghost_lemma (#a: Type) (#p: (a -> GTot Type0)) (#q: (a -> unit -> GTot Type0))
             ($_: (x: a -> Lemma (requires p x) (ensures (q x ()))))
           : Lemma (forall (x: a). p x ==> q x ())

       6.4 Existential Quantification (lines 340-390)

       (** Introduce existential with witness *)
       val exists_intro (#a: Type) (p: (a -> Type)) (witness: a)
           : Lemma (requires (p witness)) (ensures (exists (x: a). p x))

       (** Introduce via classical correspondence with negated universal *)
       val exists_intro_not_all_not (#a: Type) (#p: (a -> Type))
             ($f: ((x: a -> Lemma (~(p x))) -> Lemma False))
           : Lemma (exists x. p x)

       (** Elimination: if all witnesses prove [goal], then [goal] holds *)
       val exists_elim (goal #a: Type) (#p: (a -> Type))
             (_: squash (exists (x: a). p x))
             (_: (x: a{p x} -> GTot (squash goal)))
           : Lemma goal

       6.5 Disjunction and Excluded Middle (lines 393-406)

       (** Disjunction elimination with dependent goal *)
       val or_elim (#l #r: Type0) (#goal: (squash (l \/ r) -> Tot Type0))
             (hl: (squash l -> Lemma (goal ())))
             (hr: (squash r -> Lemma (goal ())))
           : Lemma ((l \/ r) ==> goal ())

       (** Law of excluded middle: squashed types are classical *)
       val excluded_middle (p: Type) : Lemma (requires True) (ensures (p \/ ~p))

       ---
       7. Calculational Proofs (FStar.Calc)

       File: /home/grigory/Downloads/FStar/ulib/FStar.Calc.fsti

       Calculational proofs allow chaining equational reasoning steps. F* provides special syntax that desugars to this module.

       7.1 Core Types

       (** Main type for calc proof chains *)
       val calc_chain (#a:Type u#a) (rs:list (relation a)) (x y:a) : Type u#(max 1 a)

       (** When a calc chain is sound *)
       let rec calc_chain_related (#a:Type) (rs:list (relation a)) (x y:a) : Tot Type0
         = match rs with
           | [] -> x == y
           | r1::rs -> exists (w:a). calc_chain_related rs x w /\ r1 w y

       (** Compatibility with final relation *)
       let calc_chain_compatible (#t:Type) (rs:list (relation t)) (p:relation t) : Tot Type0
         = forall (x y:t). calc_chain_related rs x y ==> p x y

       7.2 Calc Operations

       (** Initialize a calc chain *)
       val calc_init (#a:Type) (x:a) : Tot (calc_pack [] x x)

       (** Add a step to the calc chain *)
       val calc_step (#a:Type) (#x #y:a)
         (p:relation a)           (* Relation for this step *)
         (z:a)                    (* Next expression *)
         (#rs:list (relation a))
         (pf:unit -> Tot (calc_pack rs x y))   (* Rest of proof *)
         (j:unit -> Tot (squash (p y z)))      (* Justification for this step *)
         : Tot (calc_pack (p::rs) x z)

       (** Finish calc proof, establishing top-level relation *)
       val calc_finish (#a:Type) (p:relation a) (#x #y:a) (#rs:list (relation a))
         (pf:unit -> Tot (calc_pack rs x y))
         : Lemma (requires (calc_chain_compatible rs p))
                 (ensures (p x y))

       7.3 Usage Example

       (* F* syntax for calculational proofs: *)
       calc (==) {
           (a * b % m) * c % m;
           == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c m }
           (a * b) * c % m;
           == { Math.Lemmas.paren_mul_right a b c }
           a * (b * c) % m;
           == { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) m }
           a * (b * c % m) % m;
       }

       (* Desugars to calc_init/calc_step/calc_finish calls *)

       ---
       8. Mathematical Lemmas (FStar.Math.Lemmas)

       File: /home/grigory/Downloads/FStar/ulib/FStar.Math.Lemmas.fsti

       8.1 Basic Arithmetic (lines 20-131)

       (** Euclidean division definition *)
       val euclidean_div_axiom: a:int -> b:pos -> Lemma
         (a - b * (a / b) >= 0 /\ a - b * (a / b) < b)

       (** Multiplication preserves order *)
       val lemma_mult_le_left: a:nat -> b:int -> c:int -> Lemma
         (requires (b <= c)) (ensures (a * b <= a * c))

       val lemma_mult_lt_right: a:pos -> b:int -> c:int -> Lemma
         (requires (b < c)) (ensures (b * a < c * a))

       (** Commutativity and associativity *)
       val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)
       val paren_mul_right: a:int -> b:int -> c:int -> Lemma (a * b * c = a * (b * c))
       val addition_is_associative: a:int -> b:int -> c:int -> Lemma
         (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))

       (** Distributivity *)
       val distributivity_add_left: a:int -> b:int -> c:int -> Lemma ((a + b) * c = a * c + b * c)
       val distributivity_add_right: a:int -> b:int -> c:int -> Lemma (a * (b + c) = a * b + a * c)
       val distributivity_sub_left: a:int -> b:int -> c:int -> Lemma ((a - b) * c = a * c - b * c)
       val distributivity_sub_right: a:int -> b:int -> c:int -> Lemma ((a * (b - c) = a * b - a * c))

       (** Negation *)
       val neg_mul_left: a:int -> b:int -> Lemma (-(a * b) = (-a) * b)
       val neg_mul_right: a:int -> b:int -> Lemma (-(a * b) = a * (-b))

       8.2 Powers of Two (lines 142-161)

       val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))
       val pow2_double_mult: n:nat -> Lemma (2 * pow2 n = pow2 (n + 1))

       val pow2_lt_compat: n:nat -> m:nat -> Lemma
         (requires (m < n)) (ensures (pow2 m < pow2 n))

       val pow2_le_compat: n:nat -> m:nat -> Lemma
         (requires (m <= n)) (ensures (pow2 m <= pow2 n))

       val pow2_plus: n:nat -> m:nat -> Lemma (pow2 n * pow2 m = pow2 (n + m))
       val pow2_minus: n:nat -> m:nat{n >= m} -> Lemma ((pow2 n) / (pow2 m) = pow2 (n - m))

       8.3 Modular Arithmetic (lines 163-260)

       (** Basic modulo lemmas *)
       val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
       val lemma_div_mod: a:int -> p:nonzero -> Lemma (a = p * (a / p) + a % p)
       val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p /\ (a >= 0 ==> a % p <= a))

       (** Modulo with addition/multiplication *)
       val lemma_mod_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) % n = a % n)
       val lemma_div_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) / n = a / n + k)
       val cancel_mul_div (a:int) (n:nonzero) : Lemma ((a * n) / n == a)
       val cancel_mul_mod (a:int) (n:pos) : Lemma ((a * n) % n == 0)

       (** Distributivity of modulo *)
       val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
       val lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = ((a % n) * b) % n)
       val lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = (a * (b % n)) % n)

       (** Modulo of modulo *)
       val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

       8.4 Division Properties (lines 265-350)

       (** Euclidean division characterization *)
       val euclidean_division_definition: a:int -> b:nonzero -> Lemma (a = (a / b) * b + a % b)
       val division_definition: a:int -> b:pos -> m:int{a - b < m * b && m * b <= a} -> Lemma (m = a / b)

       (** Small values *)
       val small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0)
       val small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a)

       (** Division ordering *)
       val lemma_div_le: a:int -> b:int -> d:pos -> Lemma (requires (a <= b)) (ensures (a / d <= b / d))

       (** Division distributivity *)
       val division_multiplication_lemma (a:int) (b:pos) (c:pos) : Lemma (a / (b * c) = (a / b) / c)
       val modulo_division_lemma: a:nat -> b:pos -> c:pos -> Lemma ((a % (b * c)) / b = (a / b) % c)
       val modulo_modulo_lemma (a:int) (b:pos) (c:pos) : Lemma ((a % (b * c)) % b = a % b)

       8.5 Powers of Two Division/Modulo (lines 361-407)

       val pow2_multiplication_division_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
         Lemma ((a * pow2 c) / pow2 b = a * pow2 (c - b))

       val pow2_multiplication_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
         Lemma ((a * pow2 c) % pow2 b = 0)

       val pow2_modulo_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
         Lemma ((a % pow2 c) / pow2 b = (a / pow2 b) % (pow2 (c - b)))

       val pow2_modulo_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
         Lemma ((a % pow2 c) % pow2 b = a % pow2 b)

       ---
       9. Ghost and Erased Types

       File: /home/grigory/Downloads/FStar/ulib/FStar.Ghost.fsti

       9.1 The Erased Type

       (** [erased t] is computationally irrelevant counterpart of [t].
           Key properties:
           1. Non-informative: [Ghost (erased a)] subsumes to [Pure (erased a)]
           2. Extracted to [unit] during compilation
           3. In bijection with [a] via [hide] and [reveal]
           4. [reveal] and [hide] are inserted automatically by typechecker *)

       [@@ erasable]
       new val erased ([@@@strictly_positive] a: Type u#a) : Type u#a

       (** Reveal erased value (only in Ghost) *)
       val reveal: #a: Type u#a -> erased a -> GTot a

       (** Hide value into erased type (in Tot) *)
       val hide: #a: Type u#a -> a -> Tot (erased a)

       (** Round-trip lemmas with SMT patterns *)
       val hide_reveal (#a: Type) (x: erased a)
           : Lemma (ensures (hide (reveal x) == x)) [SMTPat (reveal x)]

       val reveal_hide (#a: Type) (x: a) 
           : Lemma (ensures (reveal (hide x) == x)) [SMTPat (hide x)]

       9.2 Erased Monadic Operations

       (** Return: inject value into erased *)
       let return (#a: Type) (x: a) : erased a = hide x

       (** Bind: sequential composition *)
       let bind (#a #b: Type) (x: erased a) (f: (a -> Tot (erased b))) : Tot (erased b) =
         let y = reveal x in f y

       (** Notation for erased bind *)
       let (let@) (x:erased 'a) (f:('a -> Tot (erased 'b))) : Tot (erased 'b) = bind x f

       (** Unary map over erased *)
       let elift1 (#a #b: Type) (f: (a -> GTot b)) (x: erased a)
           : Tot (y: erased b {reveal y == f (reveal x)}) =
         let@ xx = x in return (f xx)

       (** Binary map *)
       let elift2 (#a #b #c: Type) (f: (a -> b -> GTot c)) (x: erased a) (y: erased b)
           : Tot (z: erased c {reveal z == f (reveal x) (reveal y)}) =
         let@ xx = x in let@ yy = y in return (f xx yy)

       (** Push refinement under erased *)
       let push_refinement #a (#p: (a -> Type0)) (r: erased a {p (reveal r)})
           : erased (x: a{p x /\ x == reveal r}) =
         let x:(x: a{p x}) = reveal r in return x

       ---
       10. Squash Types and Proof Irrelevance

       File: /home/grigory/Downloads/FStar/ulib/FStar.Squash.fsti

       10.1 Core Squash Operations

       (** Squash is defined in Prims as: type squash (p:Type) = x:unit{p}
           This captures classical, proof-irrelevant propositions *)

       (** Inject proof into squash (return) *)
       val return_squash (#a: Type) (x: a) : Tot (squash a)

       (** Sequential composition (bind) *)
       val bind_squash (#a #b: Type) (x: squash a) (f: (a -> GTot (squash b))) : Tot (squash b)

       (** Push squash through arrow *)
       val push_squash (#a: Type) (#b: (a -> Type)) (f: (x: a -> Tot (squash (b x))))
           : Tot (squash (x: a -> GTot (b x)))

       (** Get proof from precondition *)
       val get_proof (p: Type) : Pure (squash p) (requires p) (ensures (fun _ -> True))

       (** Give proof as postcondition *)
       val give_proof (#p: Type) (x: squash p) : Pure unit (requires True) (ensures (fun _ -> p))

       (** All squash proofs are equal *)
       val proof_irrelevance (p: Type) (x y: squash p) : Tot (squash (x == y))

       10.2 Advanced Squash Combinators

       (** Remove nested squash in codomain of universal *)
       val squash_double_arrow (#a: Type) (#p: (a -> Type)) 
           ($f: (squash (x: a -> GTot (squash (p x)))))
           : GTot (squash (x: a -> GTot (p x)))

       (** Push squash through existential (sum) *)
       val push_sum (#a: Type) (#b: (a -> Type)) ($p: (dtuple2 a (fun (x: a) -> squash (b x))))
           : Tot (squash (dtuple2 a b))

       (** Map function over squash *)
       val map_squash (#a #b: Type) (x: squash a) (f: (a -> GTot b)) : Tot (squash b)

       (** Join nested squash *)
       val join_squash (#a: Type) (x: squash (squash a)) : Tot (squash a)

       ---
       11. Functional Extensionality

       File: /home/grigory/Downloads/FStar/ulib/FStar.FunctionalExtensionality.fsti

       11.1 The Extensionality Axiom

       (** Dependent arrow type *)
       let arrow (a: Type) (b: (a -> Type)) = x: a -> Tot (b x)

       (** Pointwise equality on domain [a] *)
       let feq (#a: Type) (#b: (a -> Type)) (f g: arrow a b) = 
         forall x. {:pattern (f x)\/(g x)} f x == g x

       (** Restrict function to domain [a].
           Key properties:
           1. [on_domain a f] has maximal domain [a]
           2. Pointwise equal to [f] but not provably equal
           3. Idempotent: [on_domain a (on_domain a f) == on_domain a f]
           4. Normalizer reduces [on_domain a f x] to [f x] *)
       val on_domain (a: Type) (#b: (a -> Type)) (f: arrow a b) : Tot (arrow a b)

       (** [on_domain a f] is pointwise equal to [f] *)
       val feq_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
           : Lemma (feq (on_domain a f) f) [SMTPat (on_domain a f)]

       (** MAIN AXIOM: Pointwise equal functions are equal when restricted *)
       val extensionality (a: Type) (b: (a -> Type)) (f g: arrow a b)
           : Lemma (feq #a #b f g <==> on_domain a f == on_domain a g) 
                   [SMTPat (feq #a #b f g)]

       11.2 Restricted Function Types

       (** Is function restricted to domain [a]? *)
       let is_restricted (a: Type) (#b: (a -> Type)) (f: arrow a b) = on_domain a f == f

       (** Type of functions with maximal domain [a] *)
       let restricted_t (a: Type) (b: (a -> Type)) = f: arrow a b {is_restricted a f}

       (** Notation for non-dependent restricted functions: [a ^-> b] *)
       let op_Hat_Subtraction_Greater (a b: Type) = restricted_t a (fun _ -> b)

       (** Smart constructors *)
       let on_dom (a: Type) (#b: (a -> Type)) (f: arrow a b) : restricted_t a b = on_domain a f
       let on (a #b: Type) (f: (a -> Tot b)) : (a ^-> b) = on_dom a f

       11.3 Ghost Function Extensionality

       (** Ghost arrow type *)
       let arrow_g (a: Type) (b: (a -> Type)) = x: a -> GTot (b x)

       (** Counterpart for ghost functions *)
       val on_domain_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) : Tot (arrow_g a b)

       val extensionality_g (a: Type) (b: (a -> Type)) (f g: arrow_g a b)
           : Lemma (feq_g #a #b f g <==> on_domain_g a f == on_domain_g a g)
                   [SMTPat (feq_g #a #b f g)]

       ---
       12. Type Classes

       File: /home/grigory/Downloads/FStar/ulib/FStar.Class.Eq.fst

       12.1 Decidable Equality Class

       open FStar.Tactics.Typeclasses

       (** Specification: [f] decides equality *)
       let decides_eq (#a:Type) (f : a -> a -> bool) : prop =
         forall x y. f x y <==> x == y

       (** Type class for decidable equality *)
       class deq a = {
         raw : Raw.deq a;                       (* Raw equality function *)
         eq_dec : squash (decides_eq raw.eq);   (* Proof it decides equality *)
       }

       (** The equality function *)
       let eq (#a:Type) {| d : deq a |} (x y : a) : bool = d.raw.eq x y

       (** Infix notation *)
       val (=) : #a:Type -> {| deq a |} -> a -> a -> bool
       let (=) = eq

       12.2 Instances

       (** Instance from eqtype *)
       let eq_instance_of_eqtype (#a:eqtype) {| Raw.deq a |} : deq a = {
         raw = Raw.eq_instance_of_eqtype #a;
         eq_dec = ();
       }

       (** Primitive type instances *)
       instance int_has_eq : deq int = eq_instance_of_eqtype
       instance unit_has_eq : deq unit = eq_instance_of_eqtype
       instance bool_has_eq : deq bool = eq_instance_of_eqtype
       instance string_has_eq : deq string = eq_instance_of_eqtype

       (** Derived instances for containers *)
       instance eq_list (d : deq 'a) : deq (list 'a) = {
         raw = Raw.eq_list d.raw;
         eq_dec = eqList_ok d;
       }

       instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a & 'b) = {
         raw = solve;
         eq_dec = ();
       }

       instance eq_option (_ : deq 'a) : deq (option 'a) = {
         raw = solve;
         eq_dec = ();
       }

       12.3 Other Type Classes

       F* provides additional type classes in FStar.Class.*:

       - FStar.Class.Add - Additive operations
       - FStar.Class.Ord.Raw - Ordering
       - FStar.Class.TotalOrder.Raw - Total orders
       - FStar.Class.Printable - String conversion
       - FStar.Class.Embeddable - Embedding between types

       ---
       13. Module Organization Guide

       13.1 Recommended Import Patterns

       (* Standard imports for most modules *)
       module L = FStar.List.Tot
       module S = FStar.Seq
       module M = FStar.Map
       module Set = FStar.Set

       (* For classical reasoning *)
       open FStar.Classical

       (* For memory/state *)
       module ST = FStar.HyperStack.ST
       module B = LowStar.Buffer

       13.2 Effect Hierarchy

       Tot                  -- Total, terminating computations
         |
         +-> GTot           -- Ghost total (erased at extraction)
         +-> Pure           -- Total with pre/post conditions
              |
              +-> Lemma     -- Unit-returning Ghost with ensures
              +-> DIV       -- Possibly divergent
                   |
                   +-> EXN  -- May raise exceptions
                   +-> ST   -- Stateful (instantiation of STATE_h)
                        |
                        +-> ALL  -- State + Exceptions + Divergence

       13.3 Key Files by Domain

       | Domain          | Key Files                                                    |
       |-----------------|--------------------------------------------------------------|
       | Data Structures | FStar.List.Tot.*, FStar.Seq.*, FStar.Set, FStar.Map          |
       | Logic/Proofs    | FStar.Classical, FStar.Squash, FStar.Calc                    |
       | Mathematics     | FStar.Math.Lemmas, FStar.Math.Lib, FStar.Math.Euclid         |
       | Ghost/Erased    | FStar.Ghost, FStar.IndefiniteDescription                     |
       | Memory Safety   | FStar.HyperStack.*, LowStar.Buffer, LowStar.Monotonic.Buffer |
       | Type Classes    | FStar.Class.*, FStar.Tactics.Typeclasses                     |
       | Bit Operations  | FStar.UInt*, FStar.Int*, FStar.BitVector                     |

       13.4 Naming Conventions

       - FStar.*.Base - Core operations
       - FStar.*.Properties - Lemmas about operations
       - FStar.*.Tot - Pure total versions
       - FStar.Class.* - Type class definitions

       ---
       Summary

       The F* standard library provides a comprehensive foundation for verified programming:

       1. Pure Data Structures: Lists (FStar.List.Tot) and sequences (FStar.Seq) with complete specifications and lemmas.
       2. Collections: Sets and maps with decidable equality, extensional equality proofs, and rich operation sets.
       3. Classical Logic: Full support for proof manipulation through FStar.Classical, enabling reasoning about quantifiers, implications, and disjunctions.
       4. Calculational Proofs: Native syntax for equational reasoning chains via FStar.Calc.
       5. Mathematical Foundation: Comprehensive lemmas for integer arithmetic, modular operations, and powers of two in FStar.Math.Lemmas.
       6. Proof Irrelevance: The squash type and erased types enable clean separation between computational and proof-only code.
       7. Extensionality: Careful axiomatization of functional extensionality that avoids unsoundness through domain restriction.
       8. Type Classes: Growing infrastructure for ad-hoc polymorphism via FStar.Class.*.

       The library emphasizes SMT-friendly lemmas with explicit patterns, enabling efficient automated verification while maintaining soundness through careful axiom management.
  ⎿  Done (20 tool uses · 167.1k tokens · 5m 12s)

● elite-bug-hunter(F* Ch15: IDE & Interactive)
  ⎿  Prompt:                                                                                                                                                                                                                                                                           
       Write a comprehensive documentation chapter for F* covering IDE SUPPORT AND INTERACTIVE MODE.

       Explore /home/grigory/Downloads/FStar/src/interactive/ and /home/grigory/Downloads/FStar/src/basic/ extensively.

       Focus on:
       1. Read FStarC.Interactive.Ide.fst completely (49KB) - document IDE engine
       2. Read FStarC.Interactive.Incremental.fst - document incremental checking
       3. Read FStarC.Interactive.CompletionTable.fst - document autocompletion
       4. Read FStarC.Interactive.PushHelper.fst - document push-based updates
       5. Read FStarC.Options.fst (105KB) - document ALL command-line options
       6. Read FStarC.Errors.fst - document error system
       7. Read FStarC.Errors.Codes.fst - document error codes

       Your chapter should include:
       - LSP protocol support
       - Interactive queries (lookup, completion, etc.)
       - Incremental type checking
       - Error reporting format
       - Command-line options reference (ALL options)
       - Environment variables
       - Configuration files
       - Editor integration (VS Code, Emacs, Vim)
       - Debugging F* programs
       - Profiling and performance tuning options

       Read at least 10 files. Provide code snippets with file:line references. Write the chapter as detailed documentation (5000+ words) directly in your response.
  ⎿  Response:
       Now I have gathered sufficient information. Let me compile the comprehensive documentation chapter.

       ---
       F* IDE Support and Interactive Mode

       Chapter Overview

       This chapter provides comprehensive documentation for F*'s interactive mode and IDE support, including the JSON-based protocol for editor integration, incremental type checking, code completion, error reporting, and the complete command-line options reference. The
       interactive mode is the backbone of F*'s integration with editors like VS Code, Emacs, and Neovim.

       ---
       1. Architecture Overview

       1.1 Interactive Mode Entry Point

       The interactive mode is activated by passing --ide to the F* compiler. The main entry point is defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.Ide.fst:

       // FStarC.Interactive.Ide.fst:1268-1287
       let interactive_mode (filename:string): unit =
         install_ide_mode_hooks write_json;
         // Ignore unexpected interrupts (some methods override this handler)
         Util.set_sigint_handler Util.sigint_ignore;

         if Some? (Options.codegen ()) then
           Errors.log_issue0 Errors.Warning_IDEIgnoreCodeGen "--ide: ignoring --codegen";

         let init = build_initial_repl_state filename in
         if Options.trace_error () then
           interactive_mode' init
         else
           try
             interactive_mode' init
           with
           | e -> (FStarC.Errors.set_handler FStarC.Errors.default_handler;
                  raise e)

       1.2 REPL State Management

       The core state of the interactive mode is maintained in the repl_state record type, defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.Ide.Types.fsti:

       // FStarC.Interactive.Ide.Types.fsti:135-146
       and repl_state = {
           repl_line: int;
           repl_column: int;
           repl_fname: string;
           repl_deps_stack: repl_stack_t;
           repl_curmod: optmod_t;
           repl_env: TcEnv.env;
           repl_stdin: stream_reader;
           repl_names: CTable.table;
           repl_buffered_input_queries: list query;
           repl_lang: FStarC.Universal.lang_decls_t;
       }

       The state includes:
       - repl_line/repl_column: Current cursor position in the file
       - repl_fname: The file being edited
       - repl_deps_stack: Stack of loaded dependencies with their states
       - repl_curmod: The current module being type-checked
       - repl_env: The type-checking environment
       - repl_names: Completion table for autocompletion
       - repl_buffered_input_queries: Queue of pending queries

       1.3 Push-Based State Updates

       State updates are managed through a push/pop mechanism defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.PushHelper.fst:

       // FStarC.Interactive.PushHelper.fst:99-113
       let snapshot_env env msg : repl_depth_t & env_t =
         let ctx_depth, env = TypeChecker.Tc.snapshot_context env msg in
         let opt_depth, () = Options.snapshot () in
         (ctx_depth, opt_depth), env

       let push_repl msg push_kind_opt task st =
         let depth, env = snapshot_env st.repl_env msg in
         repl_stack := (depth, (task, { st with repl_buffered_input_queries=[] })) :: !repl_stack;
         match push_kind_opt with
         | None -> st
         | Some push_kind ->
           { st with repl_env = set_check_kind env push_kind }

       The push_repl function creates a snapshot of the current state before executing a task, allowing rollback on errors. The companion pop_repl function (lines 172-187) restores the previous state.

       ---
       2. JSON-Based Protocol

       2.1 Protocol Version and Features

       The interactive protocol is versioned to ensure compatibility between F* and editor plugins:

       // FStarC.Interactive.Ide.Types.fst:180-189
       let interactive_protocol_vernum = 3

       let interactive_protocol_features =
         ["autocomplete"; "autocomplete/context";
          "compute"; "compute/reify"; "compute/pure-subterms";
          "describe-protocol"; "describe-repl"; "exit";
          "lookup"; "lookup/context"; "lookup/documentation"; "lookup/definition";
          "peek"; "pop"; "push"; "push-partial-checked-file"; "search"; "segment";
          "vfs-add"; "tactic-ranges"; "interrupt"; "progress";
          "full-buffer"; "format"; "restart-solver"; "cancel"; "fly-deps"]

       2.2 Query Structure

       All queries follow a JSON format with three required fields:

       {
         "query-id": "unique-identifier",
         "query": "query-name",
         "args": { ... }
       }

       The query types are defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.Ide.Types.fsti:

       // FStarC.Interactive.Ide.Types.fsti:104-133
       type query' =
       | Exit
       | DescribeProtocol
       | DescribeRepl
       | Segment of string (* File contents *)
       | Pop
       | Push of push_query
       | PushPartialCheckedFile of string
       | VfsAdd of option string & string
       | AutoComplete of string & completion_context
       | Lookup of string & lookup_context & option position & list string & option lookup_symbol_range
       | Compute of string & option (list FStarC.TypeChecker.Env.step)
       | Search of string
       | GenericError of string
       | ProtocolViolation of string
       | FullBuffer of string & full_buffer_request_kind & bool
       | Callback of callback_t
       | Format of string
       | RestartSolver
       | Cancel of option position

       2.3 Response Format

       Responses are sent as JSON objects:

       // FStarC.Interactive.Ide.fst:420-429
       let json_of_response qid status response =
         let qid = JsonStr qid in
         let status = match status with
                      | QueryOK -> JsonStr "success"
                      | QueryNOK -> JsonStr "failure"
                      | QueryViolatesProtocol -> JsonStr "protocol-violation" in
         JsonAssoc [("kind", JsonStr "response");
                    ("query-id", qid);
                    ("status", status);
                    ("response", response)]

       2.4 Protocol Handshake

       Upon startup, the IDE sends a protocol-info message:

       // FStarC.Interactive.Ide.fst:443-449
       let json_of_hello =
         let js_version = JsonInt interactive_protocol_vernum in
         let js_features = JsonList (List.map JsonStr interactive_protocol_features) in
         JsonAssoc (("kind", JsonStr "protocol-info") :: alist_of_protocol_info)

       let write_hello () =
         write_json json_of_hello

       ---
       3. Interactive Queries

       3.1 Push Query

       The push query is the fundamental operation for type-checking code fragments:

       // FStarC.Interactive.Ide.Types.fsti:56-65
       type push_query =
         { 
           push_kind: push_kind;
           push_line: int;
           push_column: int;
           push_peek_only: bool;
           push_code_or_decl: either string (FStarC.Parser.AST.decl & PI.code_fragment)
         }

       Where push_kind determines the verification level:

       // FStarC.Interactive.Ide.Types.fsti:38
       type push_kind = | SyntaxCheck | LaxCheck | FullCheck

       - SyntaxCheck: Only parse the code, no type checking
       - LaxCheck: Type check with all proofs admitted
       - FullCheck: Complete verification including SMT queries

       3.2 Lookup Query

       The lookup query retrieves information about symbols:

       // FStarC.Interactive.QueryHelper.fst:47-94
       let symlookup tcenv symbol pos_opt requested_info =
         let info_of_lid_str lid_str =
           let lid = Ident.lid_of_ids (List.map Ident.id_of_text (U.split lid_str ".")) in
           let lid = Option.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
           try_lookup_lid tcenv lid |> Option.map (fun ((_, typ), r) -> (Inr lid, typ, r)) in
         ...
         match info_opt with
         | None -> None
         | Some (name_or_lid, typ, rng) ->
           Some ({ slr_name = name; slr_def_range = def_range;
                  slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str })

       The requested_info list can include:
       - "type" - Type signature of the symbol
       - "documentation" - Associated documentation
       - "definition" - Full definition source
       - "defined-at" - Source location where defined

       3.3 AutoComplete Query

       Code completion is handled through a sophisticated trie-based completion table:

       // FStarC.Interactive.QueryHelper.fst:102-106
       let ck_completion (st: repl_state) (search_term: string) : list CTable.completion_result =
         let needle = U.split search_term "." in
         let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle mod_filter in
         let lids = CTable.autocomplete_lid st.repl_names needle in
         lids @ mods_and_nss

       The completion context determines what to complete:

       // FStarC.Interactive.Ide.Types.fsti:42-45
       type completion_context =
       | CKCode
       | CKOption of bool (* #set-options (false) or #reset-options (true) *)
       | CKModuleOrNamespace of bool (* modules *) & bool (* namespaces *)

       3.4 Compute Query

       The compute query evaluates terms with configurable reduction rules:

       // FStarC.Interactive.Ide.fst:950-968
       let run_compute st term rules =
         let rules =
           (match rules with
            | Some rules -> rules
            | None -> [FStarC.TypeChecker.Env.Beta;
                      FStarC.TypeChecker.Env.Iota;
                      FStarC.TypeChecker.Env.Zeta;
                      FStarC.TypeChecker.Env.UnfoldUntil SS.delta_constant])
           @ [FStarC.TypeChecker.Env.Inlining;
              FStarC.TypeChecker.Env.Eager_unfolding;
              FStarC.TypeChecker.Env.DontUnfoldAttr [Parser.Const.tac_opaque_attr];
              FStarC.TypeChecker.Env.Primops] in

         let normalize_term tcenv rules t =
           FStarC.TypeChecker.Normalize.normalize rules tcenv t in

         run_with_parsed_and_tc_term st term 0 0 (fun tcenv def ->
             let normalized = normalize_term tcenv rules def in
             (QueryOK, JsonStr (term_to_string tcenv normalized)))

       3.5 Search Query

       The search query finds definitions by type or name pattern:

       // FStarC.Interactive.Ide.fst:970-1067
       type search_term' =
       | NameContainsStr of string
       | TypeContainsLid of lid

       let run_search st search_str =
         let tcenv = st.repl_env in
         let parse search_str =
           let parse_one term =
             let negate = Util.starts_with term "-" in
             ...
             let parsed =
               if beg_quote then
                 NameContainsStr (strip_quotes term)
               else
                 let lid = Ident.lid_of_str term in
                 match DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid with
                 | None -> raise (InvalidSearch ...)
                 | Some lid -> TypeContainsLid lid in
             { st_negate = negate; st_term = parsed }

       Search terms can be:
       - Quoted strings for name matching: "lemma" finds all names containing "lemma"
       - Unquoted identifiers for type matching: list finds definitions using the list type
       - Negated with - prefix: -deprecated excludes deprecated items

       ---
       4. Incremental Type Checking

       4.1 Full Buffer Processing

       The incremental checker processes complete file buffers, defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.Incremental.fst:

       // FStarC.Interactive.Incremental.fst:272-350
       let run_full_buffer (st:repl_state)
                           (qid:string)
                           (code:string)
                           (request_type:full_buffer_request_kind)
                           (with_symbols:bool)
                           (write_full_buffer_fragment_progress: fragment_progress -> unit)
         : list query & list json
         = FStarC.Parser.ParseIt.add_vfs_entry st.repl_fname code;
           let parse_result = parse_code st None code in
           ...

       Request types control verification behavior:

       // FStarC.Interactive.Ide.Types.fsti:96-102
       type full_buffer_request_kind =
         | Full : full_buffer_request_kind
         | Lax : full_buffer_request_kind
         | Cache : full_buffer_request_kind
         | ReloadDeps : full_buffer_request_kind
         | VerifyToPosition of position
         | LaxToPosition of position

       4.2 Incremental Stack Inspection

       The incremental checker compares the REPL stack with parsed declarations to minimize re-checking:

       // FStarC.Interactive.Incremental.fst:170-229
       let inspect_repl_stack (s:repl_stack_t)
                              (ds:list (decl & code_fragment))
                              (push_kind : push_kind)
                              (with_symbols:bool)
                              (write_full_buffer_fragment_progress: fragment_progress -> unit)
         : qst (list query & list json)
         = let entries = List.rev s in
           ...
           let rec matching_prefix (accum:list json) (lookups:list query) entries (ds:list (decl & code_fragment))
               : qst (list query & list json)
               = match entries, ds with
                 | [], [] -> return (lookups, accum)
                 | e::entries, d::ds -> (
                   match repl_task_of_entry e with
                   | PushFragment (Inr d', pk, issues, _) -> (
                     if eq_decl (fst d) d' && pk `push_kind_geq` push_kind
                     then (
                       // Declaration matches - skip re-checking
                       write_full_buffer_fragment_progress (FragmentSuccess (d, s, pk));
                       matching_prefix (issues@accum) (lookups'@lookups) entries ds
                     )
                     else
                       // Mismatch - pop and push new declarations
                       let! pops = pop_entries (e::entries) in
                       let! pushes = push_decls (d::ds) in
                       return (pops @ lookups @ pushes, accum)
                   )

       This algorithm:
       1. Walks through both the REPL stack and parsed declarations in parallel
       2. If declarations match (using AST comparison), skips re-checking
       3. If a mismatch is found, pops divergent stack entries and pushes new declarations
       4. Emits progress notifications for each fragment

       4.3 Progress Notifications

       Progress is reported to the IDE during incremental checking:

       // FStarC.Interactive.Incremental.fst (referenced from types)
       type fragment_progress =
       | FullBufferStarted
       | FragmentStarted of decl
       | FragmentSuccess of decl & code_fragment & push_kind
       | FragmentFailed of decl
       | FragmentError of list issue
       | FullBufferFinished

       The IDE receives these as progress messages:

       // FStarC.Interactive.Ide.fst:607-641
       let write_full_buffer_fragment_progress (di:Incremental.fragment_progress) =
           match di with
           | FullBufferStarted ->
             write_progress (Some "full-buffer-started") []
           | FragmentStarted d ->
             write_progress (Some "full-buffer-fragment-started")
                            ["ranges", json_of_def_range d.FStarC.Parser.AST.drange]
           | FragmentSuccess (d, cf, FullCheck) ->
             write_progress (Some "full-buffer-fragment-ok")
                            ["ranges", json_of_def_range d.FStarC.Parser.AST.drange;
                             "code-fragment", json_of_code_fragment cf]
           ...

       ---
       5. Completion Table

       5.1 Data Structure

       The completion table uses a trie-based structure for efficient prefix lookup, defined in /home/grigory/Downloads/FStar/src/interactive/FStarC.Interactive.CompletionTable.fst:

       // FStarC.Interactive.CompletionTable.fst:216-219
       type trie (a:Type0) =
         { bindings: names a;
           namespaces: names (trie a) }

       Names can be direct or imported:

       // FStarC.Interactive.CompletionTable.fst:211-214
       type name_collection 'a =
       | Names of btree 'a
       | ImportedNames of string & names 'a

       5.2 Module and Namespace Registration

       Modules and namespaces are registered for completion:

       // FStarC.Interactive.CompletionTable.fst:400-423
       let register_module_path (tbl: table) (loaded: bool) (path: string) (mod_query: query) =
         let ins_ns id bindings full_name loaded =
           match names_find_exact bindings id, loaded with
           | None, _ -> names_insert bindings id (Namespace ({ ns_name = full_name; ns_loaded = loaded }))
           | Some (Namespace { ns_loaded = false }), true ->
             names_insert bindings id (Namespace ({ ns_name = full_name; ns_loaded = loaded }))
           | Some _, _ -> bindings in
         let ins_mod id bindings full_name loaded =
           names_insert bindings id
             (Module ({ mod_name = full_name; mod_loaded = loaded; mod_path = path })) in
         ...

       5.3 Name Tracking

       The IDE tracks name changes during type checking for completion updates:

       // FStarC.Interactive.PushHelper.fst:269-291
       let fresh_name_tracking_hooks () =
         let events = mk_ref [] in
         let push_event evt = events := evt :: !events in
         events,
         DsEnv.mk_dsenv_hooks
             (fun dsenv op -> push_event (NTOpen (DsEnv.current_module dsenv, op)))
             (fun dsenv ns -> push_event (NTInclude (DsEnv.current_module dsenv, ns)))
             (fun dsenv x l -> push_event (NTAlias (DsEnv.current_module dsenv, x, l))),
         { TcEnv.tc_push_in_gamma_hook =
             (fun _ s -> push_event (NTBinding s)) }

       let track_name_changes (env: env_t)
           : env_t & (env_t -> env_t & list name_tracking_event) =
         let set_hooks dshooks tchooks env =
           let (), tcenv' = with_dsenv_of_tcenv env (fun dsenv -> (), DsEnv.set_ds_hooks dsenv dshooks) in
           TcEnv.set_tc_hooks tcenv' tchooks in
         ...

       Events tracked include:
       - NTOpen - Module opens
       - NTInclude - Module includes
       - NTAlias - Module aliases
       - NTBinding - New bindings

       ---
       6. Error Reporting

       6.1 Issue Structure

       Errors are represented as issues, defined in /home/grigory/Downloads/FStar/src/basic/FStarC.Errors.fst:

       // From FStarC.Errors.Codes.fsti (interface)
       type issue = {
         issue_level: issue_level;
         issue_range: option range;
         issue_msg: error_message;
         issue_number: option int;
         issue_ctx: list string;
       }

       type issue_level =
       | ENotImplemented
       | EInfo
       | EWarning
       | EError

       6.2 JSON Error Format

       For IDE mode, errors are serialized to JSON:

       // FStarC.Errors.fst:125-132
       let json_of_issue issue =
           JsonAssoc [
               "msg",    json_of_error_message issue.issue_msg;
               "level",  json_of_issue_level issue.issue_level;
               "range",  Option.dflt JsonNull (json_of_range <$> Option.map Range.refind_range issue.issue_range);
               "number", Option.dflt JsonNull (JsonInt <$> issue.issue_number);
               "ctx",    JsonList (JsonStr <$> issue.issue_ctx);
           ]

       6.3 Error Handler for IDE Mode

       A special error handler collects errors for the IDE:

       // FStarC.Errors.fst:339-356
       let mk_catch_handler () =
         let issues : ref (list issue) = mk_ref [] in
         let err_count : ref int = mk_ref 0 in

         let add_one (e: issue) =
             (if e.issue_level = EError then
                err_count := 1 + !err_count);
             issues := e :: !issues;
             ()
         in
         let count_errors () = !err_count in
         let report () = !issues in
         let clear () = issues := []; err_count := 0 in
         { eh_name = "catch handler";
           eh_add_one = add_one;
           eh_count_errors = count_errors;
           eh_report = report;
           eh_clear = clear }

       6.4 Error Context

       Error context helps identify the source of issues:

       // FStarC.Errors.fst:402-418
       let error_context : error_context_t =
           let ctxs = mk_ref [] in
           let push s = ctxs := s :: !ctxs in
           let pop s =
               match !ctxs with
               | h::t -> (ctxs := t; h)
               | _ -> failwith "cannot pop error prefix..."
           in
           let clear () = ctxs := [] in
           let get () = !ctxs in
           let set c = ctxs := c in
           { push = push; pop = pop; clear = clear; get = get; set = set }

       Use with_ctx to add context:

       // FStarC.Errors.fst:610-632
       let with_ctx (s:string) (f : unit -> 'a) : 'a =
         error_context.push s;
         let r = try Inr (f ()) with ... in
         ignore (error_context.pop ());
         match r with
         | Inr r -> r
         | Inl e -> raise e

       ---
       7. Error Codes Reference

       F* defines over 360 error codes in /home/grigory/Downloads/FStar/src/basic/FStarC.Errors.Codes.fst. Key categories include:

       7.1 Fatal Errors (CFatal)

       Fatal errors terminate compilation:

       | Code                   | Name              | Number |
       |------------------------|-------------------|--------|
       | Fatal_AssertionFailure | Assertion failure | 24     |
       | Fatal_TypeError        | Type error        | 12     |
       | Fatal_ModuleNotFound   | Module not found  | 128    |
       | Fatal_ParseErrors      | Parse errors      | 157    |
       | Fatal_SyntaxError      | Syntax error      | 168    |
       | Fatal_TacticGotStuck   | Tactic stuck      | 170    |

       7.2 Recoverable Errors (CError/CAlwaysError)

       These can be suppressed with --warn_error:

       | Code                             | Name                | Number |
       |----------------------------------|---------------------|--------|
       | Error_ProofObligationFailed      | Proof failed        | 9      |
       | Error_Z3SolverError              | Z3 error            | 19     |
       | Error_TypeCheckerFailToProve     | TC failed           | 11     |
       | Error_UncontrainedUnificationVar | Uninstantiated uvar | 13     |

       7.3 Warnings (CWarning)

       | Code                             | Name                | Number |
       |----------------------------------|---------------------|--------|
       | Warning_CachedFile               | Cached file issue   | 241    |
       | Warning_Defensive                | Defensive check     | 290    |
       | Warning_HintFailedToReplayProof  | Hint replay failed  | 251    |
       | Warning_QuantifierWithoutPattern | Missing SMT pattern | 305    |
       | Warning_UnusedLetRec             | Unused let rec      | 328    |

       7.4 Controlling Error Levels

       The --warn_error flag controls error levels:

       // FStarC.Errors.fst:81-112
       let update_flags (l:list (error_flag & (int & int)))
         : list error_setting
         = let set_one_flag i flag default_flag =
             match flag, default_flag with
             | (CWarning, CAlwaysError)
             | (CError, CAlwaysError) ->
               raise (Invalid_warn_error_setting ...)
             | (CSilent, CAlwaysError) ->
               raise (Invalid_warn_error_setting ...)
             | (CSilent, CFatal)
             | (CWarning, CFatal)
             | (CError, CFatal) ->
               raise (Invalid_warn_error_setting ...)
             | _ -> flag
          in
          ...

       Example usage:
       - --warn_error -290 - Suppress warning 290
       - --warn_error +9 - Turn error 9 into hard error
       - --warn_error @305 - Turn warning 305 into error

       ---
       8. Command-Line Options Reference

       8.1 Core Verification Options

       | Option              | Type   | Default | Description                    |
       |---------------------|--------|---------|--------------------------------|
       | --admit_smt_queries | bool   | false   | Admit all SMT queries (unsafe) |
       | --admit_except      | string | unset   | Admit except specific queries  |
       | --lax               | flag   | false   | Run lax type checker only      |
       | --no_smt            | flag   | false   | Fail on SMT queries            |

       8.2 Fuel and Resource Limits

       | Option            | Type   | Default  | Description                                 |
       |-------------------|--------|----------|---------------------------------------------|
       | --initial_fuel    | int    | 2        | Initial unrolling of recursive functions    |
       | --max_fuel        | int    | 8        | Maximum fuel                                |
       | --initial_ifuel   | int    | 1        | Initial inductive type unrolling            |
       | --max_ifuel       | int    | 2        | Maximum inductive fuel                      |
       | --fuel            | string | -        | Set both initial and max fuel (e.g., "2,8") |
       | --z3rlimit        | int    | 5        | Z3 resource limit per query                 |
       | --z3rlimit_factor | int    | 1        | Multiplier for z3rlimit                     |
       | --z3seed          | int    | 0        | Z3 random seed                              |
       | --z3version       | string | "4.13.3" | Expected Z3 version                         |

       8.3 Hint and Cache Options

       | Option                  | Type | Default | Description                                |
       |-------------------------|------|---------|--------------------------------------------|
       | --use_hints             | flag | false   | Use hints database                         |
       | --record_hints          | flag | false   | Record hints                               |
       | --use_hint_hashes       | flag | false   | Admit on hash match                        |
       | --hint_dir              | path | -       | Directory for hints                        |
       | --hint_file             | path | -       | Specific hint file                         |
       | --cache_checked_modules | flag | false   | Write .checked files                       |
       | --cache_dir             | path | -       | Directory for cache                        |
       | --cache_off             | flag | false   | Disable caching                            |
       | --query_cache           | flag | false   | Cache SMT queries (IDE only, experimental) |

       8.4 IDE and Interactive Options

       | Option            | Type | Default | Description                |
       |-------------------|------|---------|----------------------------|
       | --ide             | flag | false   | Enable JSON-based IDE mode |
       | --ide_id_info_off | flag | false   | Disable identifier tables  |

       8.5 Output and Formatting

       | Option                | Type | Default | Description                              |
       |-----------------------|------|---------|------------------------------------------|
       | --message_format      | enum | "auto"  | Output format: human, json, github, auto |
       | --error_contexts      | bool | false   | Print error contexts                     |
       | --print_full_names    | flag | false   | Print fully qualified names              |
       | --print_universes     | flag | false   | Print universe levels                    |
       | --print_implicits     | flag | false   | Print implicit arguments                 |
       | --print_effect_args   | flag | false   | Print effect arguments                   |
       | --print_z3_statistics | flag | false   | Print Z3 stats                           |
       | --ugly                | flag | false   | Debug output formatting                  |

       8.6 SMT Encoding Options

       | Option                      | Type | Default   | Description                                     |
       |-----------------------------|------|-----------|-------------------------------------------------|
       | --smtencoding.elim_box      | bool | false     | Eliminate boxing                                |
       | --smtencoding.nl_arith_repr | enum | "boxwrap" | Non-linear arithmetic: native, wrapped, boxwrap |
       | --smtencoding.l_arith_repr  | enum | "boxwrap" | Linear arithmetic: native, boxwrap              |
       | --smtencoding.valid_intro   | bool | true      | Include valid intro axiom                       |
       | --smtencoding.valid_elim    | bool | false     | Include valid elim axiom                        |
       | --z3cliopt                  | list | []        | Z3 command line options                         |
       | --z3smtopt                  | list | []        | Z3 SMT2 options                                 |
       | --z3refresh                 | flag | false     | Restart Z3 after each query                     |

       8.7 Code Generation Options

       | Option        | Type   | Default | Description                                    |
       |---------------|--------|---------|------------------------------------------------|
       | --codegen     | enum   | unset   | Target: OCaml, FSharp, krml, Plugin, Extension |
       | --codegen-lib | list   | []      | External runtime libraries                     |
       | --extract     | string | -       | Module extraction selectors                    |
       | --odir        | path   | -       | Output directory                               |
       | --cmi         | flag   | false   | Cross-module inlining                          |

       8.8 Debugging Options

       | Option              | Type   | Default | Description                     |
       |---------------------|--------|---------|---------------------------------|
       | -d                  | flag   | false   | Enable general debugging        |
       | --debug             | list   | []      | Debug toggles (comma-separated) |
       | --debug_all         | flag   | false   | Enable all debug toggles        |
       | --trace_error       | flag   | false   | Attach stack traces             |
       | --timing            | flag   | false   | Print timing per definition     |
       | --stats             | bool   | false   | Print statistics                |
       | --profile           | string | -       | Profile specific modules        |
       | --profile_component | string | -       | Profile components              |

       8.9 Quake/Retry Options

       | Option           | Type   | Default | Description                      |
       |------------------|--------|---------|----------------------------------|
       | --quake          | string | -       | Quake testing: N, N/M, or N/M/k  |
       | --retry          | int    | -       | Retry failing queries N times    |
       | --proof_recovery | flag   | false   | Auto-retry with increased limits |

       8.10 Tactic Options

       | Option               | Type | Default | Description                         |
       |----------------------|------|---------|-------------------------------------|
       | --no_tactics         | flag | false   | Disable tactic engine               |
       | --no_plugins         | flag | false   | Interpret plugins instead of native |
       | --tactics_info       | flag | false   | Print tactic timing                 |
       | --tactics_failhard   | flag | false   | Abort on tactic errors              |
       | --tactic_trace       | flag | false   | Trace tactic execution              |
       | --tactic_trace_d     | int  | 0       | Trace depth limit                   |
       | --unsafe_tactic_exec | flag | false   | Allow external processes            |

       ---
       9. Environment Variables

       F* respects several environment variables:

       | Variable       | Purpose                           |
       |----------------|-----------------------------------|
       | FSTAR_HOME     | F* installation directory         |
       | FSTAR_LIB      | Library path (overrides default)  |
       | Z3_EXE         | Path to Z3 executable             |
       | GITHUB_ACTIONS | Auto-select github message format |

       ---
       10. Editor Integration

       10.1 VS Code Extension

       The official VS Code extension uses the --ide mode. Key features:
       - Real-time type checking with full-buffer queries
       - Hover information via lookup queries
       - Go-to-definition using defined-at in lookup results
       - Code completion with autocomplete queries
       - Inline error display from issue JSON

       10.2 Emacs (fstar-mode.el)

       The Emacs mode supports:
       - Interactive verification with push/pop queries
       - Buffer navigation with progress tracking
       - Completion via autocomplete
       - Symbol lookup with lookup

       10.3 Vim/Neovim

       Integration typically uses:
       - Language Server Protocol (LSP) wrapper around --ide
       - Or direct JSON communication via terminal

       ---
       11. Debugging F* Programs

       11.1 Tracing Execution

       # Trace all errors with stack traces
       fstar.exe --trace_error MyModule.fst

       # Enable specific debug toggles
       fstar.exe --debug "Rel,Tc" MyModule.fst

       # Enable all debugging (very verbose)
       fstar.exe --debug_all MyModule.fst

       11.2 Available Debug Toggles

       Common debug toggles include:
       - IDE - Interactive mode debugging
       - Rel - Unification/relation checking
       - Tc - Type checking
       - SMTEncoding - SMT encoding
       - Tac - Tactic execution
       - Normalize - Term normalization
       - BU - Basic utilities

       List all toggles with --help or check Debug.list_all_toggles().

       11.3 SMT Query Logging

       # Log all SMT queries
       fstar.exe --log_queries MyModule.fst

       # Log only failing queries
       fstar.exe --log_failing_queries MyModule.fst

       # Include helpful captions
       fstar.exe --log_queries --keep_query_captions true MyModule.fst

       ---
       12. Performance Tuning

       12.1 Fuel Management

       // In-file pragmas
       #set-options "--initial_fuel 1 --max_fuel 4"
       #set-options "--initial_ifuel 0 --max_ifuel 2"

       // Per-definition
       #push-options "--fuel 0 --ifuel 0"
       let fast_definition = ...
       #pop-options

       12.2 SMT Resource Management

       // Increase resource limit for complex proofs
       #push-options "--z3rlimit 50"
       let complex_lemma = ...
       #pop-options

       // Use quake testing for robustness
       #push-options "--quake 3"
       let robust_lemma = ...
       #pop-options

       12.3 Profiling

       # Profile specific modules
       fstar.exe --profile "MyModule" --profile_group_by_decl MyModule.fst

       # Timing per top-level definition
       fstar.exe --timing MyModule.fst

       # Full statistics
       fstar.exe --stats true MyModule.fst

       ---
       13. Virtual File System

       The VFS allows editors to provide file contents without disk writes:

       // FStarC.Interactive.Ide.fst:561-564
       let run_vfs_add st opt_fname contents =
         let fname = Option.dflt st.repl_fname opt_fname in
         Parser.ParseIt.add_vfs_entry fname contents;
         ((QueryOK, JsonNull), Inl st)

       JSON query format:
       {
         "query-id": "1",
         "query": "vfs-add",
         "args": {
           "filename": "MyModule.fst",
           "contents": "module MyModule\n..."
         }
       }

       ---
       14. Cancel and Interrupt Handling

       14.1 Cancel Query

       Cancel pending queries beyond a position:

       // FStarC.Interactive.Ide.fst:1086-1114
       let maybe_cancel_queries st l =
         match st.repl_buffered_input_queries with
         | { qq = Cancel p } :: rest -> (
           match p with
           | None -> [], st  // Cancel all
           | Some p ->       // Cancel from position
             let query_ahead_of p q =
               let _, l, c = p in
               match q.qq with
               | Push pq -> pq.push_line >= l
               | _ -> false
             in
             ...
         )

       14.2 Signal Handling

       // FStarC.Interactive.Ide.fst:56-78
       let with_captured_errors' (env : env_t) sigint_handler f =
         try
           Util.with_sigint_handler sigint_handler (fun _ -> f env)
         with
         | Failure (msg) ->
           Errors.log_issue env Errors.Error_IDEAssertionFailure msg;
           None
         | Util.SigInt ->
           Format.print_string "Interrupted"; None
         | Error e ->
           Errors.add_errors [e];
           None

       ---
       15. Summary

       F*'s interactive mode provides a powerful foundation for IDE integration through:

       1. JSON-based protocol with versioning and feature negotiation
       2. Incremental type checking that minimizes re-verification
       3. Sophisticated completion using trie-based tables
       4. Comprehensive error reporting with source locations and context
       5. Fine-grained control through extensive command-line options
       6. Push/pop state management for exploratory verification

       The architecture enables responsive editing experiences while maintaining F*'s strong verification guarantees.
  ⎿  Done (14 tool uses · 160.7k tokens · 3m 28s)
