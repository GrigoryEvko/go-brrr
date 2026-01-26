# Test fixtures for reaching definitions analysis
# Patterns for def-use chain construction


def simple_reaching():
    """Simple reaching definition."""
    x = 10      # Definition 1 of x
    y = x + 5   # Use of x, def 1 reaches
    return y


def multiple_definitions(flag):
    """Multiple definitions, conditional reaching."""
    if flag:
        x = 10  # Definition 1 of x
    else:
        x = 20  # Definition 2 of x
    return x    # Both definitions may reach


def killed_definition():
    """Definition killed before use."""
    x = 10      # Definition 1 - killed by def 2
    x = 20      # Definition 2 - kills def 1
    return x    # Only def 2 reaches


def loop_definition():
    """Definition in loop."""
    x = 0       # Definition 1
    for i in range(3):
        x = x + i  # Def 2, uses previous def
    return x    # Def 1 and def 2 (from loop) may reach


def uninitialized_use():
    """Potentially uninitialized use."""
    # x not defined on all paths
    if some_condition():
        x = 10
    # If condition is false, x is uninitialized
    return x  # WARNING: possibly uninitialized


def some_condition():
    return True


def def_in_try():
    """Definition in try block."""
    try:
        x = risky_operation()  # Def 1, may not execute
    except:
        x = default_value()    # Def 2, fallback
    return x  # Either def may reach


def risky_operation():
    return 42


def default_value():
    return 0


def nested_scope():
    """Nested definitions in different scopes."""
    x = 10
    for i in range(3):
        y = x + i   # x from outer scope reaches
        x = y       # New def of x
    return x


def phi_at_merge():
    """Phi function at control flow merge."""
    if True:
        x = 1  # Def 1
        y = 2  # Def 1
    else:
        x = 3  # Def 2
        y = 4  # Def 2

    # Phi node: x = phi(x@def1, x@def2)
    return x + y


def chained_definitions():
    """Chain of definitions (def-use chains)."""
    a = 1       # D1: a
    b = a + 1   # Use a(D1), D2: b
    c = b + 1   # Use b(D2), D3: c
    d = c + 1   # Use c(D3), D4: d
    return d    # Use d(D4)
