#!/usr/bin/env python3
"""
reorder_fsti.py - Reorder F* interface (.fsti) files to match implementation order

This script addresses F* Error 233: "Expected the definition of X to precede Y"
by automatically reordering .fsti declarations to match the definition order
in corresponding .fst implementation files.

SAFETY: Runs in DRY-RUN mode by default. Use --apply to actually write changes.

USAGE:
    # Dry run on all .fsti/.fst pairs (default)
    python scripts/reorder_fsti.py

    # Dry run on a specific file
    python scripts/reorder_fsti.py --file src/core/BrrrAsync.fsti

    # Actually apply changes (creates backups)
    python scripts/reorder_fsti.py --apply

    # Verbose output showing block detection
    python scripts/reorder_fsti.py --verbose

    # Check dependencies without reordering
    python scripts/reorder_fsti.py --check-only

CRITICAL FEATURES:
    1. Forward Reference Detection: Refuses to reorder if it would create
       forward references (type A uses type B, but B would come after A)
    2. Mutual Recursion: Types connected by 'and' are treated as atomic groups
    3. Dependency Analysis: Builds dependency graph from type/val signatures
    4. Module Header Preservation: module, open, friend statements stay at top
    5. Robust Validation: Content-level validation before applying changes

Author: Claude Code Bug Hunter
Date: 2026-02-01
"""

from __future__ import annotations

import argparse
import re
import sys
import shutil
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Set, FrozenSet
from datetime import datetime
from enum import Enum, auto
from collections import defaultdict


class BlockType(Enum):
    """Types of top-level blocks in F* files."""
    MODULE = auto()       # module declaration
    OPEN = auto()         # open statements
    FRIEND = auto()       # friend declarations
    SET_OPTIONS = auto()  # #set-options (standalone at top)
    VAL = auto()          # val declarations
    TYPE = auto()         # type/noeq type definitions
    LET = auto()          # let/let rec bindings
    ASSUME = auto()       # assume val/assume type
    EFFECT = auto()       # effect/layered_effect definitions
    CLASS = auto()        # typeclass definitions
    INSTANCE = auto()     # typeclass instances
    EXCEPTION = auto()    # exception definitions
    UNFOLD_LET = auto()   # unfold let bindings (type aliases)
    INLINE_LET = auto()   # inline_for_extraction let
    DIRECTIVE = auto()    # #push-options, #pop-options (standalone)
    COMMENT = auto()      # standalone comments (section headers)
    UNKNOWN = auto()      # unrecognized content


@dataclass
class DeclarationBlock:
    """
    A logical block in an F* file representing a single declaration
    with its associated comments, options, and continuations.
    """
    block_type: BlockType
    names: List[str]              # All names in this block (for mutual recursion)
    lines: List[str]              # All lines including leading comments, options
    start_line: int               # 1-indexed line number
    has_push_options: bool = False
    has_pop_options: bool = False
    references: Set[str] = field(default_factory=set)  # Names this block references

    @property
    def name(self) -> Optional[str]:
        """Primary name (first in list) for compatibility."""
        return self.names[0] if self.names else None

    def __repr__(self) -> str:
        end_line = self.start_line + len(self.lines) - 1
        names_str = ', '.join(self.names) if self.names else 'unnamed'
        return f"Block({self.block_type.name}, [{names_str}], lines {self.start_line}-{end_line})"

    def text(self) -> str:
        """Return the full text of this block."""
        return ''.join(self.lines)


class FStarParser:
    """
    Parser for F* source files (.fst/.fsti).

    Parses files into logical blocks for reordering while preserving
    all formatting, comments, and options directives.
    """

    # F* identifier pattern - identifiers can contain apostrophes (primes)
    # Examples: expr', pattern', expr'_size, type_name
    # Pattern: starts with letter or underscore, then letters/digits/underscores/apostrophes
    FSTAR_IDENT = r"[a-zA-Z_][\w']*"

    # Pattern for declarations that START a new block
    # Order matters: more specific patterns first
    # CRITICAL: Use FSTAR_IDENT instead of \w+ to handle identifiers with apostrophes
    #
    # Visibility modifiers: private, abstract can precede declarations
    # Example: private val helper : int -> int
    #          private noeq type internal = ...
    DECL_PATTERNS: List[Tuple[re.Pattern, BlockType]] = [
        # val declarations - handle operators like (<=>) and regular names
        # Optional 'private' prefix for visibility control
        (re.compile(rf'^(?:private\s+)?val\s+(?:\(([^)]+)\)|({FSTAR_IDENT}))'), BlockType.VAL),

        # assume declarations
        (re.compile(rf'^assume\s+val\s+(?:\(([^)]+)\)|({FSTAR_IDENT}))'), BlockType.ASSUME),
        (re.compile(rf'^assume\s+type\s+({FSTAR_IDENT})'), BlockType.ASSUME),

        # type declarations (noeq, abstract, private, etc.)
        # Modifiers can be: private, noeq, abstract in ANY combination/order
        # FIX: Use (?:modifier\s+)* to allow any order instead of fixed sequence
        (re.compile(rf'^(?:(?:private|noeq|abstract)\s+)*type\s+({FSTAR_IDENT})'), BlockType.TYPE),

        # let declarations with various modifiers
        # private can appear before other modifiers
        (re.compile(rf'^(?:\[@[^\]]*\]\s*)*(?:private\s+)?unfold\s+(?:inline_for_extraction\s+)?let\s+({FSTAR_IDENT})'), BlockType.UNFOLD_LET),
        (re.compile(rf'^(?:\[@[^\]]*\]\s*)*(?:private\s+)?inline_for_extraction\s+(?:noextract\s+)?(?:unfold\s+)?let\s+({FSTAR_IDENT})'), BlockType.INLINE_LET),
        (re.compile(rf'^(?:\[@[^\]]*\]\s*)*(?:private\s+)?let\s+rec\s+({FSTAR_IDENT})'), BlockType.LET),
        (re.compile(rf'^(?:\[@[^\]]*\]\s*)*(?:private\s+)?let\s+({FSTAR_IDENT})'), BlockType.LET),

        # effect declarations
        (re.compile(rf'^(?:layered_)?effect\s+({FSTAR_IDENT})'), BlockType.EFFECT),
        # new_effect and sub_effect forms
        (re.compile(rf'^new_effect\s+\{{?\s*({FSTAR_IDENT})'), BlockType.EFFECT),
        (re.compile(rf'^sub_effect\s+'), BlockType.EFFECT),

        # class/instance
        (re.compile(rf'^class\s+({FSTAR_IDENT})'), BlockType.CLASS),
        (re.compile(rf'^instance\s+({FSTAR_IDENT})'), BlockType.INSTANCE),

        # exception
        (re.compile(rf'^exception\s+({FSTAR_IDENT})'), BlockType.EXCEPTION),
    ]

    # Pattern for 'and' continuation in mutual recursion
    # This matches 'and' at the START of a line
    AND_PATTERN = re.compile(rf'^and\s+(?:\(([^)]+)\)|({FSTAR_IDENT}))')

    # Pattern for inline 'and' within a single line (e.g., "type A = ... and B = ...")
    # This is used to extract additional names from mutual recursion on a single line
    INLINE_AND_PATTERN = re.compile(rf'\band\s+(?:\(([^)]+)\)|({FSTAR_IDENT}))\s*=')

    # Header patterns (kept at top, not reordered)
    HEADER_PATTERNS: List[Tuple[re.Pattern, BlockType]] = [
        (re.compile(r'^module\s+'), BlockType.MODULE),
        (re.compile(r'^open\s+'), BlockType.OPEN),
        (re.compile(r'^friend\s+'), BlockType.FRIEND),
    ]

    # Option directive patterns
    PUSH_OPTIONS = re.compile(r'^#push-options\s')
    POP_OPTIONS = re.compile(r'^#pop-options')
    SET_OPTIONS = re.compile(r'^#set-options\s')
    RESET_OPTIONS = re.compile(r'^#reset-options')
    RESTART_SOLVER = re.compile(r'^#restart-solver')

    # Type reference patterns - used to extract dependencies
    # Matches type names that look like references to other declarations
    # CRITICAL: F* identifiers can contain apostrophes (e.g., expr', pattern')
    # We use a pattern that captures identifiers with apostrophes
    # Note: Cannot use \b boundaries because ' is not a word character
    #
    # BUG-005 FIX: Skip identifiers that are part of qualified names
    # In "FStar.List.Tot.map", we don't want to extract "List" or "Tot" as
    # local dependencies. We skip identifiers that are:
    # - Preceded by '.' (they're qualified references like Module.Type)
    # - Followed by '.' (they're module prefixes like FStar.)
    TYPE_REF_PATTERN = re.compile(r"(?<![a-zA-Z0-9_'.])([A-Z][\w']*|[a-z_][\w']*)(?![a-zA-Z0-9_'.])")

    # F* keywords to exclude from dependency analysis
    # CRITICAL: This list must be comprehensive to avoid false positive dependencies
    # Missing keywords like 'in' cause bugs where 'let x = y in z' incorrectly adds
    # 'in' as a dependency.
    #
    # IMPORTANT: Do NOT add user-definable type names like 'result', 'error', etc.
    # Those are often local type definitions that create real dependencies!
    FSTAR_KEYWORDS = frozenset([
        # Declaration keywords
        'val', 'let', 'rec', 'type', 'noeq', 'and', 'with', 'match',
        'module', 'open', 'friend', 'include',
        'effect', 'layered_effect', 'new_effect', 'sub_effect', 'total_effect',
        'class', 'instance', 'exception',
        'assume', 'private', 'abstract', 'unfold', 'irreducible',
        'inline_for_extraction', 'noextract', 'opaque_to_smt',

        # Control flow keywords
        'if', 'then', 'else', 'begin', 'end',
        'fun', 'function', 'return', 'yield',
        'in',  # CRITICAL: 'let x = y in z' - 'in' is a keyword!
        'of',  # Pattern matching: 'Some of x'
        'when', 'as',  # Pattern guards and aliases
        'try',  # Exception handling (with is above)

        # Logic/quantifier keywords
        'forall', 'exists', 'True', 'False', 'true', 'false',
        'not', 'mod', 'div', 'land', 'lor', 'lxor',

        # Type-related keywords
        'prop', 'Type', 'Type0', 'Type1', 'eqtype', 'squash',
        'Tot', 'GTot', 'Lemma', 'Pure', 'Ghost', 'ST', 'Dv', 'Div', 'Exn',
        'requires', 'ensures', 'returns', 'decreases', 'modifies',
        'assert', 'admit', 'calc',

        # F* built-in primitive types (these are truly built-in, not user-definable)
        'unit', 'bool', 'int', 'nat', 'pos', 'string', 'char',

        # Standard library types from Prims/FStar that never need local definitions
        'option', 'list', 'either', 'ref', 'seq', 'set', 'map',

        # Standard library module prefixes (qualified names start with these)
        'FStar', 'Prims',

        # Common constructors from Prims (these are special)
        'Some', 'None', 'Cons', 'Nil', 'Inl', 'Inr',
    ])

    @classmethod
    def is_header_line(cls, line: str) -> Optional[BlockType]:
        """Check if line is a header (module/open/friend). Returns BlockType or None.

        Header lines must start at column 0 (no leading whitespace).
        """
        # Header lines must not have leading whitespace
        if line and line[0] in (' ', '\t'):
            return None
        stripped = line.strip()
        for pattern, block_type in cls.HEADER_PATTERNS:
            if pattern.match(stripped):
                return block_type
        return None

    @classmethod
    def is_standalone_options(cls, line: str) -> bool:
        """Check if line is a standalone #set-options at file level."""
        stripped = line.strip()
        return bool(cls.SET_OPTIONS.match(stripped) or
                    cls.RESET_OPTIONS.match(stripped) or
                    cls.RESTART_SOLVER.match(stripped))

    @classmethod
    def is_push_options(cls, line: str) -> bool:
        """Check if line is #push-options."""
        return bool(cls.PUSH_OPTIONS.match(line.strip()))

    @classmethod
    def is_pop_options(cls, line: str) -> bool:
        """Check if line is #pop-options."""
        return bool(cls.POP_OPTIONS.match(line.strip()))

    @classmethod
    def extract_name_from_match(cls, m: re.Match) -> Optional[str]:
        """Extract declaration name from regex match groups."""
        for i in range(1, len(m.groups()) + 1):
            g = m.group(i)
            if g:
                name = g.strip()
                # Clean up name - remove type annotations
                name = name.split(':')[0].split('(')[0].strip()
                # Handle special cases like 'unfold' appearing as name
                if name in ('unfold', 'inline_for_extraction', 'noextract', 'rec'):
                    continue
                return name
        return None

    @classmethod
    def get_declaration_info(cls, line: str) -> Optional[Tuple[str, BlockType]]:
        """
        Extract declaration info from a line.

        CRITICAL: Top-level F* declarations ALWAYS start at column 0.
        Lines with leading whitespace are CONTINUATION lines, not new declarations.
        This prevents incorrectly parsing indented 'let' expressions inside
        multi-line val/Lemma declarations as new top-level declarations.

        Returns:
            (name, block_type) or None if not a declaration
        """
        # CRITICAL FIX: Top-level declarations never have leading whitespace.
        # If the line is indented, it's a continuation of the previous declaration,
        # NOT a new top-level declaration. This fixes the bug where indented
        # 'let' expressions in multi-line Lemma bodies were incorrectly parsed
        # as new declarations.
        if line and line[0] in (' ', '\t'):
            return None

        stripped = line.strip()

        # Skip if line is a comment or directive
        if stripped.startswith('(*') or stripped.startswith('#'):
            return None

        for pattern, block_type in cls.DECL_PATTERNS:
            m = pattern.match(stripped)
            if m:
                name = cls.extract_name_from_match(m)
                if name:
                    return (name, block_type)

        return None

    @classmethod
    def get_and_name(cls, line: str) -> Optional[str]:
        """Extract name from 'and' continuation line.

        'and' in mutual recursion must start at column 0.
        """
        # 'and' continuations must not have leading whitespace
        if line and line[0] in (' ', '\t'):
            return None
        stripped = line.strip()
        m = cls.AND_PATTERN.match(stripped)
        if m:
            return cls.extract_name_from_match(m)
        return None

    @classmethod
    def extract_inline_and_names(cls, line: str) -> List[str]:
        """Extract additional names from inline 'and' in mutual recursion.

        F* allows mutual recursion on a single line:
            type expr = ELit of int and stmt = SExpr of expr

        This method finds all 'and NAME =' patterns in a line.

        Args:
            line: A declaration line that may contain inline 'and'

        Returns:
            List of names found after 'and' keywords (may be empty)
        """
        names = []
        for match in cls.INLINE_AND_PATTERN.finditer(line):
            name = cls.extract_name_from_match(match)
            if name:
                names.append(name)
        return names

    @classmethod
    def is_blank_line(cls, line: str) -> bool:
        """Check if line is blank."""
        return not line.strip()

    @classmethod
    def count_comment_opens_closes(cls, line: str) -> Tuple[int, int]:
        """Count (* and *) occurrences in a line (naive, ignores strings)."""
        opens = line.count('(*')
        closes = line.count('*)')
        return opens, closes

    @classmethod
    def strip_comments_and_strings(cls, text: str) -> str:
        """
        Remove F* comments and string literals from text to avoid false dependencies.

        This is a simplified implementation that handles:
        - Multi-line comments (* ... *)
        - String literals "..."

        Does not handle nested comments perfectly but good enough for dependency extraction.
        """
        result = []
        i = 0
        n = len(text)
        comment_depth = 0

        while i < n:
            # Check for comment start
            if i + 1 < n and text[i:i+2] == '(*':
                comment_depth += 1
                i += 2
                continue

            # Check for comment end
            if i + 1 < n and text[i:i+2] == '*)' and comment_depth > 0:
                comment_depth -= 1
                i += 2
                continue

            # Inside comment - skip
            if comment_depth > 0:
                i += 1
                continue

            # Check for string literal
            if text[i] == '"':
                i += 1
                # Skip to end of string
                while i < n and text[i] != '"':
                    if text[i] == '\\' and i + 1 < n:
                        i += 2  # Skip escaped char
                    else:
                        i += 1
                if i < n:
                    i += 1  # Skip closing quote
                continue

            result.append(text[i])
            i += 1

        return ''.join(result)

    # F* operator-to-function-name mapping
    # In F*, operator `@%.` resolves to function `op_At_Percent_Dot`
    FSTAR_OP_CHARS: Dict[str, str] = {
        '@': 'At', '%': 'Percent', '.': 'Dot', '+': 'Plus', '-': 'Minus',
        '*': 'Star', '/': 'Slash', '<': 'Less', '>': 'Greater', '=': 'Equals',
        '!': 'Bang', '|': 'Bar', '&': 'Amp', '^': 'Hat', '~': 'Tilde',
        '?': 'Qmark', ':': 'Colon', '$': 'Dollar',
    }

    # Pattern to match F* custom operators (sequences of operator chars)
    # These appear in expressions like `(a + b) @%. it` or `x |> f`
    FSTAR_OP_PATTERN = re.compile(r'(?<![a-zA-Z0-9_])\s([!@#$%^&*+\-/|<>=~?:.]+)\s')

    @classmethod
    def operator_to_function_name(cls, op: str) -> Optional[str]:
        """Convert F* operator syntax to its op_* function name.

        F* maps operator characters to names:
            @%. -> op_At_Percent_Dot
            |> -> op_Bar_Greater

        Args:
            op: The operator string (e.g., "@%.")

        Returns:
            The function name (e.g., "op_At_Percent_Dot") or None if not all
            characters are valid F* operator chars
        """
        parts = []
        for ch in op:
            name = cls.FSTAR_OP_CHARS.get(ch)
            if name is None:
                return None
            parts.append(name)
        if parts:
            return 'op_' + '_'.join(parts)
        return None

    @classmethod
    def extract_references(cls, text: str, exclude_names: Set[str]) -> Set[str]:
        """
        Extract type/val references from declaration text.

        Filters out comments and string literals to avoid false dependencies.
        Also recognizes F* operator syntax and maps to op_* function names.

        Args:
            text: The full text of the declaration
            exclude_names: Names to exclude (the declaration's own names)

        Returns:
            Set of referenced names (potential dependencies)
        """
        # Strip comments and strings first
        clean_text = cls.strip_comments_and_strings(text)

        refs = set()
        for match in cls.TYPE_REF_PATTERN.finditer(clean_text):
            name = match.group(1)
            if name not in cls.FSTAR_KEYWORDS and name not in exclude_names:
                refs.add(name)

        # Extract operator references: @%. -> op_At_Percent_Dot
        for match in cls.FSTAR_OP_PATTERN.finditer(clean_text):
            op_str = match.group(1)
            func_name = cls.operator_to_function_name(op_str)
            if func_name and func_name not in exclude_names:
                refs.add(func_name)

        return refs


def parse_fstar_file(filepath: Path, verbose: bool = False) -> Tuple[List[str], List[DeclarationBlock]]:
    """
    Parse an F* file into header lines and declaration blocks.

    Args:
        filepath: Path to .fst or .fsti file
        verbose: Print detailed parsing info

    Returns:
        (header_lines, declaration_blocks)
        - header_lines: Lines for module, opens, friends (kept at top)
        - declaration_blocks: List of DeclarationBlock objects
    """
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    header_lines: List[str] = []
    blocks: List[DeclarationBlock] = []

    n = len(lines)
    i = 0

    # Phase 1: Collect header (module, opens, friends, initial comments, initial #set-options)
    in_header = True
    comment_depth = 0
    header_comment_buffer: List[str] = []

    while i < n and in_header:
        line = lines[i]
        stripped = line.strip()

        # Track comment depth
        opens, closes = FStarParser.count_comment_opens_closes(line)
        prev_depth = comment_depth
        comment_depth += opens - closes

        # Empty line in header
        if not stripped:
            header_lines.append(line)
            i += 1
            continue

        # Inside multi-line comment
        if prev_depth > 0 or (opens > 0 and comment_depth > 0):
            header_lines.append(line)
            i += 1
            continue

        # Check for module/open/friend
        header_type = FStarParser.is_header_line(line)
        if header_type is not None:
            header_lines.append(line)
            i += 1
            continue

        # Check for standalone #set-options at file level
        if FStarParser.is_standalone_options(line):
            header_lines.append(line)
            i += 1
            continue

        # Check if this is a file-level comment (doc comment before declarations)
        if stripped.startswith('(*'):
            # Collect entire comment
            comment_lines_temp = [line]
            temp_depth = comment_depth
            j = i + 1

            while j < n and temp_depth > 0:
                c_opens, c_closes = FStarParser.count_comment_opens_closes(lines[j])
                temp_depth += c_opens - c_closes
                comment_lines_temp.append(lines[j])
                j += 1

            # Skip blank lines after comment
            peek = j
            while peek < n and not lines[peek].strip():
                peek += 1

            # Check what follows
            if peek < n:
                next_header = FStarParser.is_header_line(lines[peek])
                next_opts = FStarParser.is_standalone_options(lines[peek])
                if next_header is not None or next_opts:
                    # Comment is part of header
                    header_lines.extend(comment_lines_temp)
                    i = j
                    comment_depth = 0
                    continue

            # This comment is before declarations - ends header
            in_header = False
            break

        # Any other content ends header
        in_header = False
        break

    # Reset comment depth for declaration parsing
    comment_depth = 0

    # Phase 2: Parse declarations
    pending_lines: List[str] = []
    pending_start: int = i + 1
    pending_push_options: bool = False

    def create_block_from_pending(names: List[str], block_type: BlockType,
                                   extra_lines: Optional[List[str]] = None) -> DeclarationBlock:
        """Create a DeclarationBlock from pending lines plus optional extra lines."""
        block_lines = pending_lines.copy()
        if extra_lines:
            block_lines.extend(extra_lines)

        # Extract references from the block text
        block_text = ''.join(block_lines)
        refs = FStarParser.extract_references(block_text, set(names))

        return DeclarationBlock(
            block_type=block_type,
            names=names,
            lines=block_lines,
            start_line=pending_start if pending_lines else (i + 1),
            has_push_options=pending_push_options,
            references=refs
        )

    def flush_pending_as_comment() -> None:
        """Create a comment block from pending lines if any exist."""
        nonlocal pending_lines, pending_start, pending_push_options
        if pending_lines:
            # Strip trailing blank lines
            while pending_lines and not pending_lines[-1].strip():
                pending_lines.pop()
            if pending_lines:
                blocks.append(DeclarationBlock(
                    block_type=BlockType.COMMENT,
                    names=[],
                    lines=pending_lines,
                    start_line=pending_start,
                    has_push_options=pending_push_options
                ))
        pending_lines = []
        pending_push_options = False

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # Track comment depth for multi-line comments
        opens, closes = FStarParser.count_comment_opens_closes(line)
        prev_depth = comment_depth
        comment_depth += opens - closes

        # Inside multi-line comment - accumulate
        if prev_depth > 0:
            pending_lines.append(line)
            i += 1
            continue

        # Blank line - accumulate sparingly
        if not stripped:
            # Only keep if we have content before, and not too many blanks
            if pending_lines and pending_lines[-1].strip():
                pending_lines.append(line)
            i += 1
            continue

        # #push-options - starts potential block
        if FStarParser.is_push_options(line):
            if not pending_lines:
                pending_start = i + 1
            pending_lines.append(line)
            pending_push_options = True
            i += 1
            continue

        # #pop-options - attach to the block with the matching #push-options
        # BUG-002 FIX: Search backwards through blocks to find one with unmatched push,
        # not just the immediately preceding block
        if FStarParser.is_pop_options(line):
            # Search backwards for a block with push but no pop
            matched = False
            for j in range(len(blocks) - 1, -1, -1):
                if blocks[j].has_push_options and not blocks[j].has_pop_options:
                    blocks[j].lines.append(line)
                    blocks[j].has_pop_options = True
                    matched = True
                    break
            if not matched:
                # No matching push found - add to pending (will become standalone)
                pending_lines.append(line)
            i += 1
            continue

        # Standalone #set-options in body - attach to pending
        if FStarParser.is_standalone_options(line):
            if not pending_lines:
                pending_start = i + 1
            pending_lines.append(line)
            i += 1
            continue

        # Comment start
        if stripped.startswith('(*'):
            comment_lines_here = [line]
            temp_depth = comment_depth
            j = i + 1

            while j < n and temp_depth > 0:
                c_opens, c_closes = FStarParser.count_comment_opens_closes(lines[j])
                temp_depth += c_opens - c_closes
                comment_lines_here.append(lines[j])
                j += 1

            if not pending_lines:
                pending_start = i + 1
            pending_lines.extend(comment_lines_here)
            i = j
            comment_depth = 0
            continue

        # Check for declaration start
        decl_info = FStarParser.get_declaration_info(line)
        if decl_info:
            decl_name, decl_type = decl_info
            all_names = [decl_name]

            # BUG-001 FIX: Check for inline 'and' on the same line
            # e.g., "type expr = ELit of int and stmt = SExpr of expr"
            inline_and_names = FStarParser.extract_inline_and_names(line)
            all_names.extend(inline_and_names)

            # Collect the declaration lines
            decl_lines = pending_lines.copy() + [line]
            decl_start = pending_start if pending_lines else (i + 1)
            has_push = pending_push_options
            pending_lines = []
            pending_push_options = False

            i += 1

            # Continue reading declaration body and 'and' continuations
            while i < n:
                next_line = lines[i]
                next_stripped = next_line.strip()

                # Track comments within declaration
                c_opens, c_closes = FStarParser.count_comment_opens_closes(next_line)
                comment_depth += c_opens - c_closes

                if comment_depth > 0:
                    decl_lines.append(next_line)
                    i += 1
                    continue

                # Check for 'and' continuation (mutual recursion)
                and_name = FStarParser.get_and_name(next_line)
                if and_name:
                    all_names.append(and_name)
                    decl_lines.append(next_line)
                    i += 1
                    continue

                # Check for new declaration (ends current)
                next_decl = FStarParser.get_declaration_info(next_line)
                if next_decl:
                    break

                # Check for #pop-options
                if FStarParser.is_pop_options(next_line):
                    if has_push:
                        decl_lines.append(next_line)
                        i += 1
                    break

                # Check for #push-options (starts new context)
                if FStarParser.is_push_options(next_line):
                    break

                # Header-like items shouldn't appear in body
                if FStarParser.is_header_line(next_line):
                    break

                # Blank lines - check if declaration continues
                if not next_stripped:
                    # Look ahead for continuation
                    peek = i + 1
                    blank_count = 1
                    while peek < n and not lines[peek].strip():
                        blank_count += 1
                        peek += 1

                    if blank_count >= 2 and peek < n:
                        # Two+ blank lines often indicate section break
                        peek_decl = FStarParser.get_declaration_info(lines[peek])
                        peek_and = FStarParser.get_and_name(lines[peek])
                        if peek_decl or peek_and:
                            break

                    decl_lines.append(next_line)
                    i += 1
                    continue

                # Regular content line
                decl_lines.append(next_line)
                i += 1

            # Extract references from declaration
            decl_text = ''.join(decl_lines)
            refs = FStarParser.extract_references(decl_text, set(all_names))

            block = DeclarationBlock(
                block_type=decl_type,
                names=all_names,
                lines=decl_lines,
                start_line=decl_start,
                has_push_options=has_push,
                references=refs
            )
            blocks.append(block)
            comment_depth = 0
            continue

        # Unrecognized content - accumulate
        if not pending_lines:
            pending_start = i + 1
        pending_lines.append(line)
        i += 1

    # Flush any remaining pending content
    flush_pending_as_comment()

    if verbose:
        print(f"  Parsed {len(header_lines)} header lines, {len(blocks)} blocks")
        for block in blocks:
            refs_str = f" (refs: {', '.join(sorted(block.references))})" if block.references else ""
            print(f"    {block}{refs_str}")

    return header_lines, blocks


def get_definition_order(filepath: Path, verbose: bool = False) -> List[str]:
    """
    Extract ordered list of definition names from .fst implementation file.

    Args:
        filepath: Path to .fst file
        verbose: Print parsing info

    Returns:
        List of definition names in order of appearance
    """
    _, blocks = parse_fstar_file(filepath, verbose)
    names = []
    for block in blocks:
        for name in block.names:
            if name and name not in names:
                names.append(name)
    return names


def build_dependency_graph(blocks: List[DeclarationBlock]) -> Dict[str, Set[str]]:
    """
    Build a dependency graph from declaration blocks.

    A declaration depends on another if it references that declaration's name.

    Args:
        blocks: List of declaration blocks

    Returns:
        Dict mapping declaration name to set of names it depends on
    """
    # Collect all declared names
    declared_names = set()
    for block in blocks:
        declared_names.update(block.names)

    # Build dependency graph
    deps: Dict[str, Set[str]] = {}
    for block in blocks:
        for name in block.names:
            # Filter references to only include names declared in this file
            valid_refs = block.references.intersection(declared_names)
            # Remove self-references (same block)
            valid_refs -= set(block.names)
            deps[name] = valid_refs

    return deps


def check_order_valid(
    order: List[str],
    deps: Dict[str, Set[str]],
    all_declared_names: Optional[Set[str]] = None
) -> Tuple[bool, List[str]]:
    """
    Check if a given order satisfies all dependencies (no forward references).

    CRITICAL FIX: This function now also checks for dependencies that are NOT
    in the order list at all. This catches the bug where FSTI-only declarations
    (types defined only in .fsti, not in .fst) would be placed at the END,
    after declarations that depend on them.

    Args:
        order: List of names in proposed order
        deps: Dependency graph (name -> set of names it depends on)
        all_declared_names: Set of all valid declaration names (optional).
            If provided, also checks for dependencies missing from order.

    Returns:
        (is_valid, list of violations)
        Each violation is a string like "A references B, but B comes after A"
    """
    violations = []
    name_to_position = {name: i for i, name in enumerate(order)}
    order_set = set(order)

    for name in order:
        if name not in deps:
            continue
        name_pos = name_to_position[name]
        for dep in deps[name]:
            # Check if dependency is a valid declared name
            is_valid_dep = (all_declared_names is None or dep in all_declared_names)

            if not is_valid_dep:
                # Dependency is not a name declared in this file - skip it
                continue

            if dep not in order_set:
                # CRITICAL: Dependency is NOT in the order list at all!
                # This means it will be added at the END, creating a forward reference.
                violations.append(
                    f"'{name}' references '{dep}', but '{dep}' is not in order "
                    f"(FSTI-only declaration that would be placed at END)"
                )
            else:
                dep_pos = name_to_position[dep]
                if dep_pos > name_pos:
                    violations.append(
                        f"'{name}' references '{dep}', but '{dep}' comes after '{name}'"
                    )

    return len(violations) == 0, violations


def topological_sort_with_preference(
    names: List[str],
    deps: Dict[str, Set[str]],
    preferred_order: List[str]
) -> Tuple[Optional[List[str]], List[str]]:
    """
    Attempt to sort names respecting dependencies while following preferred order.

    Args:
        names: Set of names to sort
        deps: Dependency graph
        preferred_order: Preferred order (from .fst file)

    Returns:
        (sorted_order, cycle_errors)
        - sorted_order: List in valid order, or None if impossible
        - cycle_errors: List of error messages if cycles detected
    """
    # Build name set for quick lookup
    name_set = set(names)

    # Filter dependencies to only include names we're sorting
    filtered_deps: Dict[str, Set[str]] = {}
    for name in names:
        if name in deps:
            filtered_deps[name] = deps[name].intersection(name_set)
        else:
            filtered_deps[name] = set()

    # Kahn's algorithm with preference-based selection
    in_degree: Dict[str, int] = {name: 0 for name in names}
    for name in names:
        for dep in filtered_deps.get(name, set()):
            if dep in in_degree:
                in_degree[name] += 1  # name depends on dep, so name has higher in-degree

    # Queue: names with no dependencies (in-degree 0)
    # Use preferred order as tie-breaker
    preferred_position = {name: i for i, name in enumerate(preferred_order)}

    def get_priority(name: str) -> Tuple[int, str]:
        """Return (preferred_position, name) for deterministic sorting.

        Names not in preferred_order get max position, then alphabetical tie-break.
        This ensures the topological sort is fully deterministic and idempotent.
        """
        return (preferred_position.get(name, len(preferred_order)), name)

    available = sorted([n for n in names if in_degree[n] == 0], key=get_priority)
    result = []

    while available:
        # Pick the one with best preferred position
        current = available.pop(0)
        result.append(current)

        # "Remove" current: decrease in-degree of dependents
        for name in names:
            if current in filtered_deps.get(name, set()):
                in_degree[name] -= 1
                if in_degree[name] == 0:
                    # Insert in sorted position
                    available.append(name)
                    available.sort(key=get_priority)

    if len(result) != len(names):
        # Cycle detected
        remaining = [n for n in names if n not in result]
        return None, [f"Cycle detected involving: {', '.join(remaining)}"]

    return result, []


def reorder_fsti(
    fsti_path: Path,
    fst_path: Path,
    verbose: bool = False,
    check_only: bool = False
) -> Tuple[List[str], List[str], List[Tuple[str, int, int]], bool, List[str]]:
    """
    Reorder .fsti file declarations to match .fst definition order.

    Args:
        fsti_path: Path to .fsti interface file
        fst_path: Path to .fst implementation file
        verbose: Print detailed info
        check_only: Only check, don't compute reordering

    Returns:
        (original_lines, reordered_lines, movements, changed, errors)
        - original_lines: Original file content
        - reordered_lines: Reordered file content (empty if errors)
        - movements: List of (name, old_pos, new_pos) describing changes
        - changed: True if order changed
        - errors: List of error messages (forward refs, cycles, etc.)
    """
    # Parse both files
    fsti_header, fsti_blocks = parse_fstar_file(fsti_path, verbose)
    fst_order = get_definition_order(fst_path, verbose)

    if verbose:
        print(f"  FST definition order ({len(fst_order)}): {fst_order[:10]}{'...' if len(fst_order) > 10 else ''}")
        fsti_names = []
        for b in fsti_blocks:
            fsti_names.extend(b.names)
        print(f"  FSTI declarations ({len(fsti_names)}): {fsti_names[:10]}{'...' if len(fsti_names) > 10 else ''}")

    # Read original content
    with open(fsti_path, 'r', encoding='utf-8') as f:
        original_lines = f.readlines()

    # Validate parsing results before proceeding
    # This catches parsing errors that could lead to file corruption
    parsing_errors = validate_parsing(fsti_blocks)
    if parsing_errors:
        return original_lines, [], [], False, [
            "PARSING VALIDATION FAILED - file may have complex structure that cannot be safely reordered:"
        ] + parsing_errors

    # Build dependency graph for .fsti
    deps = build_dependency_graph(fsti_blocks)

    if verbose:
        print("  Dependencies:")
        for name, name_deps in sorted(deps.items()):
            if name_deps:
                print(f"    {name} -> {', '.join(sorted(name_deps))}")

    # Map blocks by their primary name
    block_by_name: Dict[str, DeclarationBlock] = {}
    for block in fsti_blocks:
        for name in block.names:
            if name not in block_by_name:
                block_by_name[name] = block

    # Get set of .fsti declaration names
    fsti_names_set = set()
    for block in fsti_blocks:
        fsti_names_set.update(block.names)

    # Identify FSTI-only declarations (types/vals defined only in .fsti, not in .fst)
    # These are common in F* where type definitions appear only in the interface
    fsti_only = fsti_names_set - set(fst_order)

    # Filter fst_order to only include names also in fsti
    fst_order_filtered = [n for n in fst_order if n in fsti_names_set]

    # CRITICAL FIX: When there are FSTI-only declarations, we MUST use topological
    # sort on ALL fsti declarations. Otherwise, FSTI-only types get placed at the
    # END (in "second pass"), after val declarations that depend on them.
    #
    # Example bug this fixes:
    #   - `type result` defined only in .fsti (FSTI-only)
    #   - `val result_map : ... result ...` in both files
    #   - Old behavior: result_map placed by .fst order, result placed at END
    #   - Result: forward reference error (result_map before result)

    if fsti_only:
        if verbose:
            print(f"  FSTI-only declarations ({len(fsti_only)}): {sorted(fsti_only)[:5]}...")

        # Always use topological sort when there are FSTI-only declarations
        # This ensures they come before any declarations that depend on them
        #
        # IDEMPOTENCY FIX: Build a deterministic name list preserving fsti block order.
        # Using list(set) gives non-deterministic order causing the sort to oscillate.
        fsti_all_names = []
        seen_names: Set[str] = set()
        for block in fsti_blocks:
            for name in block.names:
                if name not in seen_names:
                    fsti_all_names.append(name)
                    seen_names.add(name)

        # Build a COMPLETE preferred order that covers ALL names.
        #
        # CRITICAL: FSTI-only types must be inserted JUST BEFORE the earliest
        # .fst-order item that depends on them. If they're appended at the end,
        # they get high preference numbers, and unrelated items with lower
        # preference numbers sneak in before them, breaking .fst order.
        #
        # Example: FSTI-only `type range` is needed by `val dummy_range` (fst pos 2).
        # If `range` gets preference 150, then `reserved_prefix` (fst pos 83) gets
        # placed between `string_of_pos` (1) and `range` (150), before `dummy_range`,
        # violating the .fst order.
        #
        # Fix: Insert `range` at position 2 (just before `dummy_range`), giving it
        # preference 2 and pushing `dummy_range` to 3.
        fst_set = set(fst_order_filtered)

        # Build reverse dependency map: for each FSTI-only name, find the earliest
        # .fst-order item that TRANSITIVELY depends on it.
        #
        # This handles chains like: pos_eq (FSTI) -> range_eq (FSTI) -> range_eq_refl (fst:18)
        # Both pos_eq and range_eq should be inserted at position 18, not at the end.

        # Step 1: Build a reverse dependency map (who depends on me?)
        reverse_deps: Dict[str, Set[str]] = defaultdict(set)
        for name, name_deps in deps.items():
            for dep in name_deps:
                if dep in fsti_names_set:
                    reverse_deps[dep].add(name)

        # Step 2: For each FSTI-only name, BFS through reverse deps to find
        # the earliest .fst-order item reachable
        fsti_only_insert_pos: Dict[str, int] = {}
        for fsti_name in fsti_only:
            earliest_pos = len(fst_order_filtered)  # default: end
            visited: Set[str] = set()
            queue = [fsti_name]
            while queue:
                current = queue.pop(0)
                if current in visited:
                    continue
                visited.add(current)
                # Check if this item is in .fst order
                if current in fst_set:
                    pos = fst_order_filtered.index(current)
                    earliest_pos = min(earliest_pos, pos)
                # Follow reverse deps (who depends on current?)
                for dependent in reverse_deps.get(current, set()):
                    if dependent not in visited:
                        queue.append(dependent)
            fsti_only_insert_pos[fsti_name] = earliest_pos

        # Build complete preferred order by inserting FSTI-only names at their
        # computed positions (grouped, then sorted by fsti block order for stability)
        # Group FSTI-only names by their insertion position
        insert_groups: Dict[int, List[str]] = defaultdict(list)
        for name in fsti_all_names:
            if name not in fst_set:
                pos = fsti_only_insert_pos.get(name, len(fst_order_filtered))
                insert_groups[pos].append(name)

        complete_preferred: List[str] = []
        for i, fst_name in enumerate(fst_order_filtered):
            # Insert any FSTI-only names that should come before this position
            if i in insert_groups:
                complete_preferred.extend(insert_groups[i])
            complete_preferred.append(fst_name)
        # Append any remaining FSTI-only names (those at the end)
        end_pos = len(fst_order_filtered)
        if end_pos in insert_groups:
            complete_preferred.extend(insert_groups[end_pos])

        sorted_order, cycle_errors = topological_sort_with_preference(
            fsti_all_names, deps, complete_preferred
        )

        if cycle_errors:
            return original_lines, [], [], False, cycle_errors

        if not sorted_order:
            return original_lines, [], [], False, [
                "Could not find valid ordering for FSTI-only declarations"
            ]

        if verbose:
            print(f"  Using topological sort (respects FSTI-only deps): {sorted_order[:10]}...")

        relevant_fst_order = sorted_order

    else:
        # No FSTI-only declarations - use .fst order directly
        relevant_fst_order = fst_order_filtered

        # Still check for internal violations (forward refs within .fst order)
        is_valid, violations = check_order_valid(
            relevant_fst_order, deps, fsti_names_set
        )

        if not is_valid:
            if verbose:
                print("  FST order creates forward references in FSTI:")
                for v in violations[:5]:
                    print(f"    {v}")
                if len(violations) > 5:
                    print(f"    ... and {len(violations) - 5} more")

            # Try topological sort respecting dependencies
            # IDEMPOTENCY FIX: Use deterministic fsti block order, not set conversion
            fsti_all_names = []
            seen_fb: Set[str] = set()
            for block in fsti_blocks:
                for name in block.names:
                    if name not in seen_fb:
                        fsti_all_names.append(name)
                        seen_fb.add(name)
            sorted_order, cycle_errors = topological_sort_with_preference(
                fsti_all_names, deps, relevant_fst_order
            )

            if cycle_errors:
                return original_lines, [], [], False, cycle_errors

            if sorted_order:
                if verbose:
                    print(f"  Using dependency-aware order: {sorted_order[:10]}...")
                relevant_fst_order = sorted_order
            else:
                return original_lines, [], [], False, violations

    # Track original positions for reporting
    original_positions: Dict[str, int] = {}
    for idx, block in enumerate(fsti_blocks):
        for name in block.names:
            if name not in original_positions:
                original_positions[name] = idx

    if check_only:
        # Just checking - return success
        return original_lines, original_lines, [], False, []

    # Build reordered block list
    reordered_blocks: List[DeclarationBlock] = []
    used_blocks: Set[int] = set()  # Track blocks by their id
    movements: List[Tuple[str, int, int]] = []

    # First pass: add blocks in fst order
    new_position = 0
    for name in relevant_fst_order:
        if name in block_by_name:
            block = block_by_name[name]
            block_id = id(block)
            if block_id not in used_blocks:
                reordered_blocks.append(block)
                used_blocks.add(block_id)

                # Record movement for primary name
                primary = block.names[0] if block.names else name
                old_pos = original_positions.get(primary, -1)
                if old_pos != new_position:
                    movements.append((primary, old_pos, new_position))
                new_position += 1

    # Second pass: add remaining fsti blocks not in fst
    for block in fsti_blocks:
        block_id = id(block)
        if block_id not in used_blocks:
            reordered_blocks.append(block)
            used_blocks.add(block_id)

            if block.names:
                primary = block.names[0]
                old_pos = original_positions.get(primary, -1)
                if verbose:
                    print(f"  Warning: '{primary}' in .fsti but not found in .fst order")
                movements.append((primary, old_pos, new_position))
            new_position += 1

    # Construct reordered content
    reordered_lines: List[str] = list(fsti_header)

    # Ensure separation between header and first block
    if reordered_lines and reordered_blocks:
        if reordered_lines[-1].strip():
            reordered_lines.append('\n')

    for block in reordered_blocks:
        reordered_lines.extend(block.lines)

    # Ensure trailing newline consistency
    if original_lines and original_lines[-1].endswith('\n'):
        if reordered_lines and not reordered_lines[-1].endswith('\n'):
            reordered_lines[-1] += '\n'
    elif original_lines and not original_lines[-1].endswith('\n'):
        if reordered_lines and reordered_lines[-1].endswith('\n'):
            reordered_lines[-1] = reordered_lines[-1].rstrip('\n')

    # Check if order actually changed
    original_order = []
    for b in fsti_blocks:
        original_order.extend(b.names)
    new_order = []
    for b in reordered_blocks:
        new_order.extend(b.names)

    changed = original_order != new_order

    return original_lines, reordered_lines, movements, changed, []


def validate_parsing(blocks: List[DeclarationBlock]) -> List[str]:
    """
    Validate that parsing produced sensible results.

    Detects potential parsing errors that could lead to file corruption:
    - Orphaned code fragments (let...in expressions parsed as declarations)
    - Blocks with suspicious content patterns

    Args:
        blocks: Parsed declaration blocks

    Returns:
        List of error messages (empty if valid)
    """
    errors: List[str] = []

    # Pattern to detect the 'in' keyword (not as part of another word)
    # Matches: " in ", " in\n", " in)", " in}" etc.
    # Does NOT match: "int", "into", "in_range", etc.
    IN_KEYWORD_PATTERN = re.compile(r'\s+in(?:\s|$|[)\]}])')

    for block in blocks:
        text = block.text().strip()
        if not text:
            continue

        first_line = text.split('\n')[0] if text else ''
        stripped_first = first_line.strip()

        # Check for orphaned let...in expressions
        # These should never be top-level declarations
        # Valid: "let foo = expr" (top-level binding in .fsti)
        # Invalid: "let foo = expr in bar" (let expression, should be inside a val body)
        if stripped_first.startswith('let ') and block.block_type == BlockType.LET:
            # Look for the 'in' keyword (not substring like 'int')
            if IN_KEYWORD_PATTERN.search(first_line):
                # Check if 'in' is at a balanced paren/brace level
                # Find the position of the 'in' keyword
                match = IN_KEYWORD_PATTERN.search(first_line)
                if match:
                    before_in = first_line[:match.start()]
                    paren_depth = before_in.count('(') - before_in.count(')')
                    brace_depth = before_in.count('{') - before_in.count('}')
                    bracket_depth = before_in.count('[') - before_in.count(']')

                    # Only flag if 'in' appears at top level (balanced parens)
                    # and there's content after 'in' (not just whitespace/end of line)
                    if paren_depth == 0 and brace_depth == 0 and bracket_depth == 0:
                        after_in = first_line[match.end():]
                        if after_in.strip():  # There's actual content after 'in'
                            errors.append(
                                f"Line {block.start_line}: Orphaned 'let...in' expression detected - "
                                f"'{stripped_first[:60]}...' - this may indicate a parsing error"
                            )

        # Check for blocks that start with indented-looking content
        # (shouldn't happen after our fix, but check anyway)
        if block.lines and block.lines[0].startswith((' ', '\t')):
            if block.block_type not in (BlockType.COMMENT, BlockType.UNKNOWN):
                errors.append(
                    f"Line {block.start_line}: Block starts with whitespace - "
                    f"this may be a continuation that was incorrectly split"
                )

    return errors


def validate_reorder(
    original_lines: List[str],
    reordered_lines: List[str],
    fsti_path: Path
) -> List[str]:
    """
    Validate that reordering didn't lose or duplicate content.

    Args:
        original_lines: Original file content
        reordered_lines: Reordered file content
        fsti_path: Path for error messages

    Returns:
        List of warning/error messages (empty if valid)
    """
    warnings: List[str] = []

    # Check line count
    orig_count = len(original_lines)
    new_count = len(reordered_lines)

    if abs(orig_count - new_count) > 10:
        warnings.append(
            f"Line count changed significantly: {orig_count} -> {new_count} "
            f"(diff: {new_count - orig_count})"
        )

    # Content-level validation
    orig_text = ''.join(original_lines)
    new_text = ''.join(reordered_lines)

    # Check module declaration preserved
    orig_module = re.search(r'^module\s+\S+', orig_text, re.MULTILINE)
    new_module = re.search(r'^module\s+\S+', new_text, re.MULTILINE)
    if orig_module:
        if not new_module:
            warnings.append("CRITICAL: module declaration lost!")
        elif orig_module.group() != new_module.group():
            warnings.append(f"module declaration changed: {orig_module.group()} -> {new_module.group()}")

    # Count key tokens
    for pattern, name in [
        (r'\nval\s', 'val'),
        (r'\ntype\s', 'type'),
        (r'\nnoeq\s+type\s', 'noeq type'),
        (r'\nlet\s', 'let'),
        (r'\nunfold\s', 'unfold'),
        (r'\nassume\s+val\s', 'assume val'),
    ]:
        orig_count_p = len(re.findall(pattern, orig_text))
        new_count_p = len(re.findall(pattern, new_text))
        if orig_count_p != new_count_p:
            warnings.append(f"{name} count changed: {orig_count_p} -> {new_count_p}")

    return warnings


def create_backup(filepath: Path) -> Path:
    """
    Create a timestamped backup of a file.

    Args:
        filepath: File to backup

    Returns:
        Path to backup file
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_path = filepath.with_suffix(f".fsti.bak.{timestamp}")
    shutil.copy2(filepath, backup_path)
    return backup_path


def find_fsti_fst_pairs(project_root: Path) -> List[Tuple[Path, Path]]:
    """
    Find all .fsti/.fst pairs in the project.

    Args:
        project_root: Root directory to search

    Returns:
        List of (fsti_path, fst_path) tuples
    """
    pairs = []
    for fsti in project_root.rglob('*.fsti'):
        fst = fsti.with_suffix('.fst')
        if fst.exists():
            pairs.append((fsti, fst))
    return sorted(pairs)


def main() -> int:
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Reorder .fsti files to match .fst definition order',
        epilog='SAFETY: Runs in dry-run mode by default. Use --apply to write changes.',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        '--apply',
        action='store_true',
        help='Actually apply changes (default is dry-run mode)'
    )
    parser.add_argument(
        '--file',
        type=str,
        help='Process a single .fsti file (default: all pairs in project)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed block detection and dependency info'
    )
    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Do not create backup files when applying changes'
    )
    parser.add_argument(
        '--project-root',
        type=str,
        help='Project root directory (default: auto-detect from script location)'
    )
    parser.add_argument(
        '--check-only',
        action='store_true',
        help='Only check for issues, do not compute reordering'
    )
    parser.add_argument(
        '--force',
        action='store_true',
        help='Apply changes even if validation warnings occur'
    )

    args = parser.parse_args()

    # Determine project root
    if args.project_root:
        project_root = Path(args.project_root)
    else:
        # Script is in brrr-lang/scripts/
        script_dir = Path(__file__).resolve().parent
        project_root = script_dir.parent

    if not project_root.exists():
        print(f"Error: Project root not found: {project_root}")
        return 1

    # Find files to process
    if args.file:
        fsti_path = Path(args.file)
        if not fsti_path.is_absolute():
            fsti_path = project_root / args.file

        if not fsti_path.exists():
            print(f"Error: File not found: {fsti_path}")
            return 1

        if fsti_path.suffix != '.fsti':
            print(f"Error: Expected .fsti file: {fsti_path}")
            return 1

        fst_path = fsti_path.with_suffix('.fst')
        if not fst_path.exists():
            print(f"Error: Corresponding .fst file not found: {fst_path}")
            return 1

        pairs = [(fsti_path, fst_path)]
    else:
        pairs = find_fsti_fst_pairs(project_root)

    if not pairs:
        print("No .fsti/.fst pairs found")
        return 0

    # Print mode
    if args.check_only:
        mode_str = "CHECK ONLY"
    elif args.apply:
        mode_str = "APPLYING CHANGES"
    else:
        mode_str = "DRY RUN"
    print(f"[{mode_str}] Processing {len(pairs)} file pair(s)...")
    print()

    # Process files
    changes_needed = 0
    errors_count = 0
    total_movements = 0
    skipped_due_to_deps = 0

    for fsti_path, fst_path in pairs:
        try:
            rel_path = fsti_path.relative_to(project_root) if fsti_path.is_relative_to(project_root) else fsti_path
        except ValueError:
            rel_path = fsti_path

        try:
            original, reordered, movements, changed, errors = reorder_fsti(
                fsti_path, fst_path, args.verbose, args.check_only
            )

            if errors:
                print(f"[SKIP] {rel_path}")
                for err in errors:
                    print(f"  Error: {err}")
                skipped_due_to_deps += 1
                print()
                continue

            if not changed:
                if args.verbose:
                    print(f"[OK] {rel_path} - already in correct order")
                continue

            changes_needed += 1
            total_movements += len(movements)

            print(f"[REORDER] {rel_path}")
            print(f"  {len(movements)} declaration(s) need reordering")

            # Show movements
            for name, old_pos, new_pos in movements[:5]:
                direction = "down" if new_pos > old_pos else "up"
                print(f"    {name}: position {old_pos} -> {new_pos} ({direction})")
            if len(movements) > 5:
                print(f"    ... and {len(movements) - 5} more")

            # Validate
            warnings = validate_reorder(original, reordered, fsti_path)
            for warn in warnings:
                print(f"  WARNING: {warn}")

            if args.apply:
                if warnings and not args.force:
                    print(f"  Skipping due to validation warnings (use --force to override)")
                    errors_count += 1
                    continue

                # Create backup
                if not args.no_backup:
                    backup_path = create_backup(fsti_path)
                    print(f"  Backup: {backup_path.name}")

                # Write reordered content
                with open(fsti_path, 'w', encoding='utf-8') as f:
                    f.writelines(reordered)

                print(f"  Applied: {len(original)} -> {len(reordered)} lines")
            else:
                print(f"  Would change: {len(original)} -> {len(reordered)} lines")

            print()

        except Exception as e:
            print(f"[ERROR] {rel_path}: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
            errors_count += 1
            print()

    # Summary
    print("-" * 60)
    mode_str = "Applied to" if args.apply else "Would reorder"
    print(f"{mode_str} {changes_needed} file(s) ({total_movements} total movements)")

    if skipped_due_to_deps > 0:
        print(f"Skipped due to dependency issues: {skipped_due_to_deps}")

    if errors_count > 0:
        print(f"Errors: {errors_count}")

    if not args.apply and changes_needed > 0:
        print()
        print("To apply changes, run with --apply flag")
        print("Backups will be created automatically (use --no-backup to skip)")

    return 1 if errors_count > 0 else 0


if __name__ == '__main__':
    sys.exit(main())
