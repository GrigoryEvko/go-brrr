#!/usr/bin/env python3
"""
Remove duplicate type definitions from .fst files when they exist in .fsti.

When a type is fully defined (with = and body) in the .fsti interface file,
F* expects the .fst implementation file to NOT redefine it. This script:

1. Finds all type definitions in .fsti files (fully defined with =)
2. Removes matching type definitions from corresponding .fst files
3. Runs in DRY RUN mode by default - use --apply to make changes

Handles:
- Simple type aliases: type foo = nat
- noeq types: noeq type bar = { field : nat }
- unfold types: unfold type my_nat = nat
- inline_for_extraction types
- ADT types: type color = | Red | Green | Blue
- Record types: type person = { name: string; age: nat }
- Mutual recursion: type a = ... and b = ... and c = ...
- Attributes before types: [@...] type t = ...
- F* directives: #push-options, #pop-options, #set-options
- Type declarations (without =) in .fsti are NOT considered concrete
- Private types in .fst are NOT removed (implementation details)

Usage:
    python scripts/remove_fst_duplicate_types.py                    # Dry run all
    python scripts/remove_fst_duplicate_types.py --file BrrrAsync   # Dry run one
    python scripts/remove_fst_duplicate_types.py --apply            # Apply all
"""

import argparse
import re
import sys
import shutil
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Set, Tuple, Optional


# All valid type modifiers that can precede 'type' keyword
# Order matters for the regex - longer patterns first
TYPE_MODIFIERS = [
    'inline_for_extraction',
    'noextract',
    'private',
    'abstract',
    'unfold',
    'noeq',
]

# Build pattern for type modifiers
# Matches: (modifier1 modifier2 ... type name) where modifiers are optional
MODIFIER_PATTERN = '(?:(?:' + '|'.join(TYPE_MODIFIERS) + r')\s+)*'

# Patterns for detecting type definitions
# Handles all modifiers: noeq, unfold, inline_for_extraction, private, etc.
TYPE_START_PATTERN = re.compile(
    r'^' + MODIFIER_PATTERN + r'type\s+([a-zA-Z_][a-zA-Z0-9_\']*)'
)

# Pattern for 'and' continuation of mutual recursion
AND_TYPE_PATTERN = re.compile(
    r'^and\s+([a-zA-Z_][a-zA-Z0-9_\']*)'
)

# Pattern to check if a type line has 'private' modifier
PRIVATE_TYPE_PATTERN = re.compile(
    r'^(?:(?:' + '|'.join(TYPE_MODIFIERS) + r')\s+)*private\s+(?:(?:' + '|'.join(TYPE_MODIFIERS) + r')\s+)*type\s+'
)

# Pattern for F* directives that do NOT terminate type definitions
FST_DIRECTIVE_PATTERN = re.compile(
    r'^#(push-options|pop-options|set-options|restart-solver)\b'
)

# Terminators: constructs that definitely end a type definition block
TERMINATORS = [
    'val ',
    'let ',
    'let rec ',
    'unfold let ',
    'inline_for_extraction let ',
    'noextract let ',
    'assume val ',
    'friend ',
    'open ',
    'module ',
    'instance ',
    'class ',
    'effect ',
    'layered_effect ',
    'sub_effect ',
    'new_effect ',
    'total_effect ',
]


def is_comment_start(line: str) -> bool:
    """Check if line starts a comment block."""
    stripped = line.strip()
    return stripped.startswith('(*') or stripped.startswith('//')


def is_section_header(line: str) -> bool:
    """Check if line is a section header comment like (* ==== *)."""
    stripped = line.strip()
    return (
        (stripped.startswith('(** ==') or stripped.startswith('(* ==')) or
        (stripped.startswith('(*') and '====' in stripped)
    )


def is_block_in_comment(lines: List[str], start: int, end: int) -> bool:
    """
    Check if the type definition block appears to be inside a comment.
    This is a heuristic check - we look if the block starts with (* and no closing.
    """
    # This is a simple heuristic - a more robust solution would parse comments
    # For now, we check if the type line starts after (* on the same line
    first_line = lines[start].strip() if start < len(lines) else ""
    return first_line.startswith('(*') and 'type ' in first_line


def find_type_block_end(lines: List[str], start_index: int) -> int:
    """
    Find the end of a type definition block starting at start_index.

    Returns the index of the last line of the type block (inclusive).
    """
    j = start_index + 1
    while j < len(lines):
        curr_line = lines[j]
        curr_stripped = curr_line.strip()

        # Skip empty lines
        if not curr_stripped:
            j += 1
            continue

        # F* directives don't terminate type definitions
        if FST_DIRECTIVE_PATTERN.match(curr_stripped):
            j += 1
            continue

        # Attributes don't terminate type definitions
        if curr_stripped.startswith('[@'):
            j += 1
            continue

        # Must be at column 0 (not indented) to be a terminator
        if curr_line and not curr_line[0].isspace():
            # Check for 'and' continuation of mutual recursion
            if AND_TYPE_PATTERN.match(curr_stripped):
                j += 1
                continue

            # Check for terminators
            for term in TERMINATORS:
                if curr_stripped.startswith(term):
                    # Found terminator, go back to skip trailing blank lines
                    end_line = j - 1
                    while end_line > start_index and not lines[end_line].strip():
                        end_line -= 1
                    return end_line

            # New type definition (not 'and')
            if TYPE_START_PATTERN.match(curr_stripped):
                end_line = j - 1
                while end_line > start_index and not lines[end_line].strip():
                    end_line -= 1
                return end_line

            # Section headers terminate
            if is_section_header(curr_line):
                end_line = j - 1
                while end_line > start_index and not lines[end_line].strip():
                    end_line -= 1
                return end_line

        j += 1

    # Reached end of file
    end_line = j - 1
    while end_line > start_index and not lines[end_line].strip():
        end_line -= 1
    return end_line


def extract_and_types(block: str) -> List[str]:
    """
    Extract type names from 'and' continuations in a mutual recursion block.

    Returns list of type names (not including the main type).
    """
    and_types = []
    for line in block.split('\n'):
        stripped = line.strip()
        m = AND_TYPE_PATTERN.match(stripped)
        if m:
            and_types.append(m.group(1))
    return and_types


def is_private_type(block: str) -> bool:
    """
    Check if a type block contains a private type definition.

    Private types should not be removed from .fst files as they
    are implementation details not exposed in .fsti.
    """
    first_line = block.split('\n')[0].strip()
    return PRIVATE_TYPE_PATTERN.match(first_line) is not None


def find_attribute_prefix_lines(lines: List[str], type_start: int) -> int:
    """
    Find the start of attribute prefix lines before a type definition.

    Looks for lines like [@...] that precede the type keyword
    and should be removed along with the type.

    Returns the line index where the type block truly starts (including attributes).
    """
    actual_start = type_start

    # Look backwards from type_start
    j = type_start - 1
    while j >= 0:
        line = lines[j]
        stripped = line.strip()

        # Empty lines break the attribute chain
        if not stripped:
            break

        # Attribute annotations (can be multi-line like [@attr1]\n[@attr2])
        if stripped.startswith('[@') or stripped.startswith('[@@'):
            actual_start = j
            j -= 1
            continue

        # Otherwise, not part of the type definition
        break

    return actual_start


def find_type_definitions(content: str) -> Dict[str, Tuple[int, int, str, bool]]:
    """
    Find all type definitions with their line ranges.

    Returns dict of type_name -> (start_line, end_line, full_block, is_private)
    Lines are 0-indexed.

    Also tracks 'and' types from mutual recursion as separate entries.
    """
    lines = content.split('\n')
    types: Dict[str, Tuple[int, int, str, bool]] = {}

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        m = TYPE_START_PATTERN.match(stripped)
        if m:
            # Skip if this appears to be inside a comment
            if is_block_in_comment(lines, i, i):
                i += 1
                continue

            type_name = m.group(1)

            # Find attribute prefix (lines before type with [@...])
            actual_start = find_attribute_prefix_lines(lines, i)

            # Find the end of the type definition block
            end_line = find_type_block_end(lines, i)

            block = '\n'.join(lines[actual_start:end_line + 1])
            is_private = is_private_type(block)
            types[type_name] = (actual_start, end_line, block, is_private)

            # Also extract 'and' types as separate entries
            # They share the same block range and privacy as the parent
            for and_type in extract_and_types(block):
                types[and_type] = (actual_start, end_line, block, is_private)

            i = end_line + 1
        else:
            i += 1

    return types


def has_constructors_or_fields(type_block: str) -> bool:
    """
    Check if a type definition has constructors (|) or record fields ({}).

    Tries to ignore patterns that appear inside comments.
    """
    # Remove single-line comments
    lines = []
    for line in type_block.split('\n'):
        # Remove (* ... *) comments on single line
        cleaned = re.sub(r'\(\*[^*]*\*\)', '', line)
        # Remove // comments
        cleaned = re.sub(r'//.*$', '', cleaned)
        lines.append(cleaned)

    cleaned_block = '\n'.join(lines)

    # Check for constructor syntax: | at start of line (after whitespace)
    if re.search(r'^\s*\|', cleaned_block, re.MULTILINE):
        return True

    # Check for record syntax: { ... } with field definitions
    # Must have { and } with something between them
    if re.search(r'\{[^}]+\}', cleaned_block, re.DOTALL):
        return True

    return False


def is_concrete_definition(block: str) -> bool:
    """
    Check if a type block is a concrete definition (has = sign).

    Type declarations like 'type foo' or 'type foo : Type0' without =
    are not concrete - they must be implemented in .fst.
    """
    # Remove comments first to avoid matching = inside comments
    cleaned = re.sub(r'\(\*[^*]*\*\)', '', block)
    cleaned = re.sub(r'//.*$', '', cleaned, flags=re.MULTILINE)
    return '=' in cleaned


def remove_duplicate_types(
    fst_content: str,
    fsti_types: Set[str],
    verbose: bool = False
) -> Tuple[str, List[str], int]:
    """
    Remove type definitions from .fst that exist in .fsti.

    Returns (modified_content, list_of_removed, count)

    Does NOT remove:
    - Private types (implementation details)
    - Types that are abstract in .fsti (only their name, no definition)
    """
    lines = fst_content.split('\n')
    fst_types = find_type_definitions(fst_content)

    removed: List[str] = []
    lines_to_remove: Set[int] = set()

    # Track which blocks we've already marked for removal
    # (multiple types in a mutual recursion block share the same range)
    removed_ranges: Set[Tuple[int, int]] = set()

    for type_name, (start, end, block, is_private) in fst_types.items():
        # Skip private types - they are implementation details
        if is_private:
            if verbose:
                print(f"    Keeping private type '{type_name}' (lines {start+1}-{end+1})")
            continue

        if type_name in fsti_types:
            range_key = (start, end)
            if range_key not in removed_ranges:
                removed_ranges.add(range_key)
                # Add ALL types from this block to removed list
                removed.append(type_name)
                for line_num in range(start, end + 1):
                    lines_to_remove.add(line_num)
                if verbose:
                    print(f"    Removing type '{type_name}' (lines {start+1}-{end+1})")
            else:
                # Type is part of an already-marked mutual recursion block
                # Still add it to the removed list for accurate reporting
                removed.append(type_name)
                if verbose:
                    print(f"    Removing type '{type_name}' (part of mutual recursion, lines {start+1}-{end+1})")

    # Build new content excluding removed lines
    new_lines = []
    i = 0
    while i < len(lines):
        if i in lines_to_remove:
            # Skip all lines of this type block
            while i in lines_to_remove and i < len(lines):
                i += 1
        else:
            new_lines.append(lines[i])
            i += 1

    # Clean up multiple consecutive blank lines (keep at most one)
    cleaned_lines = []
    prev_blank = False
    for line in new_lines:
        is_blank = not line.strip()
        if is_blank and prev_blank:
            continue
        cleaned_lines.append(line)
        prev_blank = is_blank

    return '\n'.join(cleaned_lines), removed, len(removed)


def process_file_pair(
    fst_path: Path,
    fsti_path: Path,
    apply: bool,
    verbose: bool,
    no_backup: bool
) -> Tuple[int, List[str]]:
    """
    Process a .fst/.fsti file pair.

    Returns (count_removed, list_of_removed_types)
    """
    fst_content = fst_path.read_text()
    fsti_content = fsti_path.read_text()

    # Find all types defined in .fsti
    fsti_types_info = find_type_definitions(fsti_content)
    fsti_concrete_types: Set[str] = set()

    for type_name, (_, _, block, _) in fsti_types_info.items():
        # Only consider types with = (concrete definitions)
        if is_concrete_definition(block):
            fsti_concrete_types.add(type_name)

    if verbose:
        print(f"  Found {len(fsti_concrete_types)} concrete types in .fsti")

    # Remove duplicates from .fst
    new_content, removed, count = remove_duplicate_types(
        fst_content, fsti_concrete_types, verbose
    )

    if count == 0:
        return 0, []

    if apply:
        # Create backup
        if not no_backup:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            backup_path = fst_path.with_suffix(f'.fst.bak.{timestamp}')
            shutil.copy2(fst_path, backup_path)
            print(f"  Backup: {backup_path.name}")

        fst_path.write_text(new_content)
        print(f"  Applied: removed {count} duplicate type(s)")
    else:
        print(f"  Would remove {count} duplicate type(s): {', '.join(removed[:5])}" +
              (f"... and {len(removed)-5} more" if len(removed) > 5 else ""))

    return count, removed


def main():
    parser = argparse.ArgumentParser(
        description='Remove duplicate type definitions from .fst files'
    )
    parser.add_argument(
        '--file',
        help='Process specific module (e.g., BrrrAsync)'
    )
    parser.add_argument(
        '--apply',
        action='store_true',
        help='Actually apply changes (default is dry run)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed output'
    )
    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Skip creating backup files'
    )
    parser.add_argument(
        '--dir',
        help='Search in specific directory instead of src/core'
    )

    args = parser.parse_args()

    # Find project root
    script_dir = Path(__file__).parent
    project_root = script_dir.parent

    if args.dir:
        src_dir = project_root / args.dir
    else:
        src_dir = project_root / 'src' / 'core'

    if not src_dir.exists():
        print(f"Error: Cannot find {src_dir}", file=sys.stderr)
        sys.exit(1)

    # Find file pairs
    if args.file:
        module_name = args.file
        if not module_name.startswith('Brrr'):
            module_name = 'Brrr' + module_name
        fst_path = src_dir / f'{module_name}.fst'
        fsti_path = src_dir / f'{module_name}.fsti'

        if not fst_path.exists():
            print(f"Error: {fst_path} not found", file=sys.stderr)
            sys.exit(1)
        if not fsti_path.exists():
            print(f"Error: {fsti_path} not found", file=sys.stderr)
            sys.exit(1)

        pairs = [(fst_path, fsti_path)]
    else:
        # Find all .fst/.fsti pairs in the directory and subdirectories
        pairs = []
        for fst_path in sorted(src_dir.rglob('*.fst')):
            fsti_path = fst_path.with_suffix('.fsti')
            if fsti_path.exists():
                pairs.append((fst_path, fsti_path))

    mode = "[APPLYING CHANGES]" if args.apply else "[DRY RUN]"
    print(f"{mode} Processing {len(pairs)} file pair(s)...\n")

    total_removed = 0
    files_changed = 0

    for fst_path, fsti_path in pairs:
        try:
            rel_path = fst_path.relative_to(project_root)
        except ValueError:
            rel_path = fst_path
        print(f"[CHECK] {rel_path}")

        count, _ = process_file_pair(
            fst_path, fsti_path,
            args.apply, args.verbose, args.no_backup
        )

        if count > 0:
            total_removed += count
            files_changed += 1
        else:
            print("  No duplicates found")
        print()

    print("-" * 60)
    if args.apply:
        print(f"Removed {total_removed} duplicate types from {files_changed} file(s)")
    else:
        print(f"Would remove {total_removed} duplicate types from {files_changed} file(s)")
        print("\nTo apply changes, run with --apply flag")


if __name__ == '__main__':
    main()
