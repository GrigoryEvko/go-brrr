# Test fixtures for low complexity functions
# Expected: cyclomatic complexity 1-5, cognitive complexity 0-5


def simple_return():
    """Complexity: 1 (single path)."""
    return 42


def simple_if(x):
    """Complexity: 2 (one branch)."""
    if x > 0:
        return "positive"
    return "non-positive"


def simple_math(a, b):
    """Complexity: 1 (no branches)."""
    result = a + b
    return result * 2


def simple_loop(items):
    """Complexity: 2 (one loop)."""
    total = 0
    for item in items:
        total += item
    return total


def simple_try_except(value):
    """Complexity: 2 (one exception handler)."""
    try:
        return int(value)
    except ValueError:
        return 0


def simple_ternary(x):
    """Complexity: 2 (ternary counts as branch)."""
    return "yes" if x else "no"


def linear_sequence(data):
    """Complexity: 1 (sequential statements)."""
    step1 = data.strip()
    step2 = step1.lower()
    step3 = step2.replace(" ", "_")
    return step3


def simple_early_return(x):
    """Complexity: 2 (guard clause)."""
    if x is None:
        return None
    return x * 2


def simple_match(value):
    """Complexity: 3 (two case branches)."""
    if value == "a":
        return 1
    elif value == "b":
        return 2
    return 0
