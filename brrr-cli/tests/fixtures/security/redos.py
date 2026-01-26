# Test fixtures for ReDoS (Regular expression Denial of Service) detection
# Contains various ReDoS vulnerability patterns

import re


def vulnerable_nested_quantifiers(user_input):
    """Vulnerable: nested quantifiers."""
    # VULNERABLE: (a+)+ causes catastrophic backtracking
    pattern = re.compile(r'(a+)+$')
    return pattern.match(user_input)


def vulnerable_overlapping_groups(text):
    """Vulnerable: overlapping character classes."""
    # VULNERABLE: (.*a){n} causes exponential time
    pattern = re.compile(r'(.*a){10}')
    return pattern.search(text)


def vulnerable_email_regex(email):
    """Vulnerable: complex email validation."""
    # VULNERABLE: Multiple overlapping groups
    pattern = re.compile(r'^([a-zA-Z0-9_\.\-])+\@(([a-zA-Z0-9\-])+\.)+([a-zA-Z0-9]{2,4})+$')
    return pattern.match(email)


def vulnerable_html_regex(html):
    """Vulnerable: HTML parsing with regex."""
    # VULNERABLE: Nested optional groups with wildcards
    pattern = re.compile(r'<[^>]*(\s+\w+(\s*=\s*("[^"]*"|\'[^\']*\'|[^\s>]+))?)*>')
    return pattern.findall(html)


def vulnerable_polynomial_time(data):
    """Vulnerable: polynomial time complexity."""
    # VULNERABLE: (\w+\d+)+ on certain inputs
    pattern = re.compile(r'(\w+\d+)+')
    return pattern.match(data)


def safe_simple_pattern(text):
    """Safe: simple non-backtracking pattern."""
    # SAFE: No nested quantifiers
    pattern = re.compile(r'\w+')
    return pattern.findall(text)


def safe_atomic_group_alternative(text):
    """Safe: using possessive-like patterns."""
    # SAFE: Bounded repetition
    pattern = re.compile(r'[a-z]{1,100}')
    return pattern.match(text)


def safe_email_simple(email):
    """Safe: simple email validation."""
    # SAFE: No dangerous backtracking
    pattern = re.compile(r'^[^@]+@[^@]+\.[^@]+$')
    return pattern.match(email)


def safe_with_timeout(text, pattern_str, timeout=1.0):
    """Safe: regex with timeout."""
    import signal

    def handler(signum, frame):
        raise TimeoutError("Regex timeout")

    # SAFE: Using timeout to prevent DoS
    signal.signal(signal.SIGALRM, handler)
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        pattern = re.compile(pattern_str)
        result = pattern.match(text)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)

    return result
