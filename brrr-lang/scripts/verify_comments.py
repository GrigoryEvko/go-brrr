#!/usr/bin/env python3
"""
F* Comment Syntax Verifier

Detects common comment syntax issues in F* (.fst/.fsti) files:
1. Unclosed (* comments that swallow code
2. Premature *) that close comments too early
3. Nested comment issues
4. Common gotchas:
   - (*) asterisk operator descriptions
   - (-*) magic wand operator (separation logic)
   - (char*), (void*) C-style pointer casts
   - Any identifier*) pattern inside comments

F* Comment Rules:
- (* text *) - regular block comment
- (** text *) - docstring
- Nested comments ARE allowed: (* outer (* inner *) outer *)
- DANGER: *) anywhere closes a comment level!

Safe alternatives:
- Use (star) instead of (*)
- Use (wand) or dash-star instead of (-*)
- Use "char pointer" instead of (char*)

Author: Claude Code Bug Hunter
"""

import os
import re
import sys
import subprocess
from dataclasses import dataclass
from typing import List, Tuple, Optional
from pathlib import Path


@dataclass
class CommentIssue:
    """Represents a comment-related issue in a file."""
    file_path: str
    line_number: int
    column: int
    issue_type: str
    message: str
    severity: str  # CRITICAL, HIGH, MEDIUM, LOW


@dataclass
class FileAnalysis:
    """Complete analysis of a single file."""
    file_path: str
    total_lines: int
    open_count: int  # Number of (*
    close_count: int  # Number of *)
    max_nesting: int
    unclosed_at_end: int  # Comment depth at EOF
    issues: List[CommentIssue]
    fstar_parse_ok: bool
    fstar_parse_error: Optional[str]


class FStarCommentVerifier:
    """Verifies F* comment syntax for correctness."""

    def __init__(self, fstar_exe: str = "fstar.exe"):
        self.fstar_exe = fstar_exe
        self.issues: List[CommentIssue] = []

    def analyze_file(self, file_path: str) -> FileAnalysis:
        """Analyze a single F* file for comment issues."""
        self.issues = []

        try:
            with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
                content = f.read()
        except Exception as e:
            return FileAnalysis(
                file_path=file_path,
                total_lines=0,
                open_count=0,
                close_count=0,
                max_nesting=0,
                unclosed_at_end=0,
                issues=[CommentIssue(
                    file_path=file_path,
                    line_number=0,
                    column=0,
                    issue_type="READ_ERROR",
                    message=f"Cannot read file: {e}",
                    severity="CRITICAL"
                )],
                fstar_parse_ok=False,
                fstar_parse_error=str(e)
            )

        lines = content.split('\n')
        total_lines = len(lines)

        # Analyze comment structure
        open_count, close_count, max_nesting, unclosed_at_end = self._count_comments(content, file_path)

        # Check for common problematic patterns
        self._check_problematic_patterns(content, lines, file_path)

        # Verify with F* parser
        fstar_ok, fstar_error = self._verify_with_fstar(file_path)

        return FileAnalysis(
            file_path=file_path,
            total_lines=total_lines,
            open_count=open_count,
            close_count=close_count,
            max_nesting=max_nesting,
            unclosed_at_end=unclosed_at_end,
            issues=self.issues.copy(),
            fstar_parse_ok=fstar_ok,
            fstar_parse_error=fstar_error
        )

    def _count_comments(self, content: str, file_path: str) -> Tuple[int, int, int, int]:
        """
        Count comment delimiters accounting for:
        - Strings (delimiters inside strings don't count)
        - Line comments (// makes rest of line not count)
        - Nested comments (F* supports them)
        - Operator definitions like (let*) where (* is NOT a comment

        Returns: (open_count, close_count, max_nesting, unclosed_at_end)
        """
        open_count = 0
        close_count = 0
        max_nesting = 0
        depth = 0

        i = 0
        line = 1
        col = 1
        in_string = False
        in_line_comment = False

        # Track where unclosed comments start
        unclosed_starts: List[Tuple[int, int]] = []  # (line, col)

        # Operator definition patterns like (let*), (and*) etc.
        # These contain (* but are NOT comment starts
        import re
        op_def_pattern = re.compile(r'\(let\*\)|\(and\*\)|\(\*\*\)')

        while i < len(content):
            char = content[i]

            # Track line/column for error reporting
            if char == '\n':
                line += 1
                col = 1
                in_line_comment = False
                i += 1
                continue

            # Inside line comment - skip
            if in_line_comment:
                i += 1
                col += 1
                continue

            # String handling - skip content inside strings
            if char == '"' and not in_string:
                # Start of string
                in_string = True
                i += 1
                col += 1
                continue
            elif char == '"' and in_string:
                # Check for escaped quote
                if i > 0 and content[i-1] == '\\':
                    i += 1
                    col += 1
                    continue
                in_string = False
                i += 1
                col += 1
                continue
            elif in_string:
                i += 1
                col += 1
                continue

            # Check for line comment start
            # IMPORTANT: Only treat // as line comment when OUTSIDE block comments!
            # In F* (like OCaml), // inside (* *) is just text, NOT a line comment.
            if depth == 0 and char == '/' and i + 1 < len(content) and content[i + 1] == '/':
                in_line_comment = True
                i += 2
                col += 2
                continue

            # Check for comment open (*
            # BUT skip operator definitions like (let*) where (* appears after identifier
            if char == '(' and i + 1 < len(content) and content[i + 1] == '*':
                # Check if this is an operator definition like (let*), (and*), etc.
                # Pattern: let (OPERATOR) = ... where OPERATOR ends with *
                # Look for pattern: (identifier*) - not a comment
                if i + 2 < len(content) and content[i + 2] == ')':
                    # This is (*) - just skip, might be inside comment describing *
                    i += 3
                    col += 3
                    continue
                # Check if preceding chars form operator def: let (xyz*) =
                # Look back for "let (" or "= ("
                lookback = content[max(0, i-10):i].strip()
                if lookback.endswith('let') or lookback.endswith('='):
                    # This might be operator def, look ahead for *) pattern
                    # like (let*) or (>>=) etc.
                    lookahead = content[i:i+10]
                    if re.match(r'\([a-zA-Z_][a-zA-Z0-9_]*\*\)', lookahead):
                        # Operator definition, skip whole thing
                        match_len = re.match(r'\([a-zA-Z_][a-zA-Z0-9_]*\*\)', lookahead).end()
                        i += match_len
                        col += match_len
                        continue
                open_count += 1
                depth += 1
                max_nesting = max(max_nesting, depth)
                unclosed_starts.append((line, col))
                i += 2
                col += 2
                continue

            # Check for comment close *)
            if char == '*' and i + 1 < len(content) and content[i + 1] == ')':
                # Skip if this is part of operator def like (let*)
                # Check if this *) is part of (identifier*) pattern
                lookback = content[max(0, i-10):i]
                if re.search(r'\([a-zA-Z_][a-zA-Z0-9_]*$', lookback):
                    # Part of operator definition, skip
                    i += 2
                    col += 2
                    continue
                close_count += 1
                if depth > 0:
                    depth -= 1
                    unclosed_starts.pop()
                else:
                    # Closing without opening!
                    self.issues.append(CommentIssue(
                        file_path=file_path,
                        line_number=line,
                        column=col,
                        issue_type="PREMATURE_CLOSE",
                        message=f"*) closes comment but no comment is open (depth was {depth})",
                        severity="CRITICAL"
                    ))
                i += 2
                col += 2
                continue

            i += 1
            col += 1

        # Check for unclosed comments at end
        if depth > 0:
            for (start_line, start_col) in unclosed_starts:
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=start_line,
                    column=start_col,
                    issue_type="UNCLOSED_COMMENT",
                    message=f"(* opened at line {start_line}:{start_col} is never closed - swallowing {line - start_line} lines!",
                    severity="CRITICAL"
                ))

        return open_count, close_count, max_nesting, depth

    def _check_problematic_patterns(self, content: str, lines: List[str], file_path: str):
        """Check for common problematic patterns."""

        # Pattern 1: (*) - asterisk operator description that closes comment
        # This matches (* ... (*) ... which is problematic
        for line_num, line in enumerate(lines, 1):
            # Look for (*) which would close then open
            if '(*)' in line:
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=line_num,
                    column=line.find('(*)') + 1,
                    issue_type="ASTERISK_OPERATOR_PATTERN",
                    message="'(*)' found - this closes and reopens comments! May be describing * operator. Use '(star)' instead.",
                    severity="HIGH"
                ))

        # Pattern 2: (-*) - magic wand operator in separation logic
        # The *) closes a comment prematurely!
        for line_num, line in enumerate(lines, 1):
            if '(-*)' in line:
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=line_num,
                    column=line.find('(-*)') + 1,
                    issue_type="MAGIC_WAND_PATTERN",
                    message="'(-*)' found - the '*)'closes comments! Use '(wand)' or '(dash-star)' instead.",
                    severity="HIGH"
                ))

        # Pattern 3: C-style pointer casts like (char*), (void*), (int*) etc.
        # The *) closes a comment prematurely!
        # EXCLUDE: F* operator definitions like (let*), (and*), (or*), (>>=), etc.
        fstar_operators = {'let*', 'and*', 'or*', 'fun*', 'match*', 'if*', 'then*', 'else*'}
        c_pointer_pattern = re.compile(r'\(([a-zA-Z_][a-zA-Z0-9_]*)\s*\*\)')
        for line_num, line in enumerate(lines, 1):
            for match in c_pointer_pattern.finditer(line):
                identifier = match.group(1)
                # Skip F* operator definitions
                if identifier + '*' in fstar_operators:
                    continue
                # Skip if it looks like a let binding: let (op*) =
                context_before = line[max(0, match.start()-10):match.start()].strip()
                if context_before.endswith('let') or context_before.endswith('='):
                    continue
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=line_num,
                    column=match.start() + 1,
                    issue_type="C_POINTER_CAST_PATTERN",
                    message=f"'{match.group()}' found - C pointer syntax with '*)'closes comments! Use 'type pointer' instead.",
                    severity="HIGH"
                ))

        # Pattern 4: Any *) preceded by non-whitespace that's not at comment depth 0
        # This catches patterns like: foo*), bar*), etc. inside comments
        # We check for word-char followed by *)
        # BUT: Skip if line has balanced (* and *) - likely C function pointer syntax
        #      creating valid nested comments (e.g., void* (*join)(void*, void*))
        suspicious_close = re.compile(r'[a-zA-Z0-9_]\*\)')
        for line_num, line in enumerate(lines, 1):
            # Count (* and *) on this line - if balanced, skip (nested comments balance out)
            line_opens = line.count('(*')
            line_closes = line.count('*)')
            if line_opens == line_closes and line_opens > 0:
                # Balanced nested comments on this line (like C function pointers)
                continue

            for match in suspicious_close.finditer(line):
                # Skip if this is a known operator definition like (let*)
                context_start = max(0, match.start() - 10)
                context = line[context_start:match.end()]
                if re.search(r'\([a-zA-Z_][a-zA-Z0-9_]*\*\)$', context):
                    # Already caught by C_POINTER_CAST_PATTERN
                    continue
                # Skip if there's a matching (* before this *) on the same line
                before = line[:match.start()]
                opens_before = before.count('(*')
                closes_before = before.count('*)')
                if opens_before > closes_before:
                    # There's an unmatched (* before this *), so this *) closes it - OK
                    continue
                # Check if it looks like it's inside a comment (heuristic: line has (* before this)
                if '(*' in before or before.strip().startswith('*') or before.strip() == '':
                    self.issues.append(CommentIssue(
                        file_path=file_path,
                        line_number=line_num,
                        column=match.start() + 1,
                        issue_type="SUSPICIOUS_CLOSE_PATTERN",
                        message=f"'...{match.group()}' may close comment prematurely. Check if inside comment block.",
                        severity="MEDIUM"
                    ))

        # Pattern 5: HACL*/ or similar - asterisk followed by / could be problematic
        # when inside a comment (not an issue for F* which uses *) not */)
        hacl_pattern = re.compile(r'\w+\*/|\w+\*/')
        for line_num, line in enumerate(lines, 1):
            for match in hacl_pattern.finditer(line):
                if '*/' in match.group():  # This would matter in C-style, but F* uses *)
                    pass  # Actually not an issue for F*

        # Pattern 6: Empty comment blocks that might indicate missing content
        empty_comment = re.compile(r'\(\*\s*\*\)')
        for line_num, line in enumerate(lines, 1):
            if empty_comment.search(line):
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=line_num,
                    column=line.find('(*') + 1,
                    issue_type="EMPTY_COMMENT",
                    message="Empty comment block (* *) - intentional?",
                    severity="LOW"
                ))

        # Pattern 7: Very long runs without any code (might be all commented)
        # Check if file is > 100 lines but has no 'let', 'val', 'type', 'module' outside comments
        if len(lines) > 100:
            code_keywords = ['let ', 'val ', 'type ', 'module ', 'open ', 'include ']
            has_code = False
            in_comment = False
            comment_depth = 0

            for line in lines:
                # Track comment state (simplified)
                for i in range(len(line)):
                    if line[i:i+2] == '(*':
                        comment_depth += 1
                    elif line[i:i+2] == '*)':
                        comment_depth = max(0, comment_depth - 1)

                # Only check for keywords outside comments
                if comment_depth == 0:
                    for kw in code_keywords:
                        if kw in line and not line.strip().startswith('//'):
                            has_code = True
                            break
                if has_code:
                    break

            if not has_code:
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=1,
                    column=1,
                    issue_type="ALL_COMMENTED",
                    message=f"File has {len(lines)} lines but no code keywords found outside comments - possibly all commented out!",
                    severity="CRITICAL"
                ))

        # Pattern 8: *) inside string literals that might close comments if string parsing is off
        # Look for patterns like "*)" inside what looks like strings
        string_with_close = re.compile(r'"[^"]*\*\)[^"]*"')
        for line_num, line in enumerate(lines, 1):
            if string_with_close.search(line):
                self.issues.append(CommentIssue(
                    file_path=file_path,
                    line_number=line_num,
                    column=1,
                    issue_type="CLOSE_IN_STRING",
                    message="String contains '*)', might cause issues if string parsing fails.",
                    severity="MEDIUM"
                ))

    def _verify_with_fstar(self, file_path: str) -> Tuple[bool, Optional[str]]:
        """Use fstar.exe to verify the file parses correctly."""
        try:
            # Use --print to just parse and print, not type check
            result = subprocess.run(
                [self.fstar_exe, '--print', file_path],
                capture_output=True,
                text=True,
                timeout=30
            )
            if result.returncode == 0:
                return True, None
            else:
                error = result.stderr.strip() if result.stderr else result.stdout.strip()
                # Truncate long errors
                if len(error) > 500:
                    error = error[:500] + "..."
                return False, error
        except subprocess.TimeoutExpired:
            return False, "fstar.exe timed out (30s)"
        except FileNotFoundError:
            return False, f"fstar.exe not found at {self.fstar_exe}"
        except Exception as e:
            return False, f"Error running fstar.exe: {e}"


def scan_directory(directory: str, verifier: FStarCommentVerifier) -> List[FileAnalysis]:
    """Scan a directory for F* files and analyze them."""
    results = []

    for root, dirs, files in os.walk(directory):
        # Skip common non-source directories
        dirs[:] = [d for d in dirs if d not in ['.git', '__pycache__', 'node_modules', '.cache']]

        for file in files:
            if file.endswith('.fst') or file.endswith('.fsti'):
                file_path = os.path.join(root, file)
                print(f"Analyzing: {file_path}")
                analysis = verifier.analyze_file(file_path)
                results.append(analysis)

    return results


def print_report(results: List[FileAnalysis]):
    """Print a comprehensive report of the analysis."""
    print("\n" + "=" * 80)
    print("F* COMMENT SYNTAX VERIFICATION REPORT")
    print("=" * 80)

    # Summary
    total_files = len(results)
    files_with_issues = sum(1 for r in results if r.issues or not r.fstar_parse_ok)
    critical_issues = sum(1 for r in results for i in r.issues if i.severity == "CRITICAL")
    high_issues = sum(1 for r in results for i in r.issues if i.severity == "HIGH")

    print(f"\nSUMMARY:")
    print(f"  Total files analyzed: {total_files}")
    print(f"  Files with issues: {files_with_issues}")
    print(f"  Critical issues: {critical_issues}")
    print(f"  High severity issues: {high_issues}")

    # Files with imbalanced comments
    print("\n" + "-" * 80)
    print("FILES WITH IMBALANCED COMMENTS:")
    print("-" * 80)

    imbalanced = [r for r in results if r.open_count != r.close_count or r.unclosed_at_end > 0]
    if imbalanced:
        for r in imbalanced:
            print(f"\n  {r.file_path}")
            print(f"    (* count: {r.open_count}, *) count: {r.close_count}")
            print(f"    Max nesting: {r.max_nesting}")
            print(f"    Unclosed at EOF: {r.unclosed_at_end}")
    else:
        print("  None found - all comments balanced!")

    # Files that fail F* parsing
    print("\n" + "-" * 80)
    print("FILES THAT FAIL F* PARSING:")
    print("-" * 80)

    parse_failures = [r for r in results if not r.fstar_parse_ok]
    if parse_failures:
        for r in parse_failures:
            print(f"\n  {r.file_path}")
            if r.fstar_parse_error:
                # Print first few lines of error
                error_lines = r.fstar_parse_error.split('\n')[:5]
                for line in error_lines:
                    print(f"    {line}")
    else:
        print("  All files parse successfully!")

    # All issues by severity
    print("\n" + "-" * 80)
    print("ALL ISSUES BY SEVERITY:")
    print("-" * 80)

    for severity in ["CRITICAL", "HIGH", "MEDIUM", "LOW"]:
        issues_at_level = [(r.file_path, i) for r in results for i in r.issues if i.severity == severity]
        if issues_at_level:
            print(f"\n  [{severity}]")
            for file_path, issue in issues_at_level:
                print(f"    {file_path}:{issue.line_number}:{issue.column}")
                print(f"      {issue.issue_type}: {issue.message}")

    # Files with possible "all commented" syndrome
    print("\n" + "-" * 80)
    print("FILES POSSIBLY ENTIRELY COMMENTED OUT:")
    print("-" * 80)

    all_commented = [r for r in results
                     for i in r.issues
                     if i.issue_type == "ALL_COMMENTED"]
    if all_commented:
        for r in all_commented:
            print(f"  {r.file_path} ({r.total_lines} lines)")
    else:
        print("  None detected!")

    print("\n" + "=" * 80)
    print("END OF REPORT")
    print("=" * 80)


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(description='Verify F* comment syntax')
    parser.add_argument('paths', nargs='*', default=['.'],
                       help='Paths to scan (files or directories)')
    parser.add_argument('--fstar', default='fstar.exe',
                       help='Path to fstar.exe')
    parser.add_argument('--no-fstar-check', action='store_true',
                       help='Skip fstar.exe verification')
    args = parser.parse_args()

    verifier = FStarCommentVerifier(fstar_exe=args.fstar)
    all_results = []

    for path in args.paths:
        if os.path.isfile(path):
            print(f"Analyzing: {path}")
            all_results.append(verifier.analyze_file(path))
        elif os.path.isdir(path):
            all_results.extend(scan_directory(path, verifier))
        else:
            print(f"Warning: {path} not found")

    print_report(all_results)

    # Return non-zero if critical issues found
    critical_count = sum(1 for r in all_results for i in r.issues if i.severity == "CRITICAL")
    return 1 if critical_count > 0 else 0


if __name__ == '__main__':
    sys.exit(main())
