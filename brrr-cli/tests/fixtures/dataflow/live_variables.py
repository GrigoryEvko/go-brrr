# Test fixtures for live variables analysis
# Patterns for dead store detection and variable lifetime


def dead_store_simple():
    """Simple dead store: x is overwritten before use."""
    x = 10      # DEAD STORE: x overwritten at line 7
    y = 5
    x = 20      # x used here (assigned)
    return x + y


def dead_store_conditional(flag):
    """Dead store in conditional path."""
    x = 0
    if flag:
        x = 10  # Potentially dead if flag is always true
    else:
        x = 20  # Potentially dead if flag is always false
    return x


def unused_parameter(a, b, c):
    """Unused parameter detection."""
    # 'c' is never used - dead parameter
    return a + b


def unused_variable():
    """Unused local variable."""
    x = compute_something()
    y = 10  # UNUSED: y is never read
    return x


def compute_something():
    return 42


def live_across_loop():
    """Variable live across loop iterations."""
    total = 0  # Live at loop entry
    items = [1, 2, 3]
    for item in items:
        total = total + item  # total live here
    return total  # total live here


def short_lifetime():
    """Variable with short lifetime."""
    x = get_data()
    result = x * 2  # x dies after this line
    y = get_other_data()
    return result + y  # result and y live here


def get_data():
    return 10


def get_other_data():
    return 20


def interfering_variables():
    """Variables that are live at the same time (interfere)."""
    a = 1
    b = 2
    c = 3
    # a, b, c all live here
    result = a + b + c
    return result


def non_interfering_variables():
    """Variables with non-overlapping lifetimes."""
    a = 1
    x = a * 2
    # a dies here

    b = 3
    y = b * 2
    # b dies here

    return x + y  # Only x and y are live


def dead_in_exception():
    """Dead store if exception always thrown."""
    x = 10
    try:
        raise ValueError("always")
    except:
        x = 20
    return x  # x is 20 (exception path taken)
