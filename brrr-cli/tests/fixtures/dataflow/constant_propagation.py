# Test fixtures for constant propagation analysis
# Various patterns for constant value tracking


def constant_simple():
    """Simple constant: x is always 10."""
    x = 10
    y = x + 5  # y = 15 (constant folding opportunity)
    return y


def constant_arithmetic():
    """Arithmetic with constants: can be folded."""
    a = 5
    b = 3
    c = a + b      # c = 8
    d = c * 2      # d = 16
    e = d - a      # e = 11
    return e


def constant_conditional_branch():
    """Constant in conditional: dead branch."""
    x = True
    if x:  # Always true - else branch is dead
        return "yes"
    else:
        return "no"


def constant_loop_invariant():
    """Loop invariant constant."""
    factor = 10
    total = 0
    items = [1, 2, 3, 4, 5]
    for item in items:
        total += item * factor  # factor is loop invariant
    return total


def not_constant_parameter(x):
    """Parameter value unknown at compile time."""
    y = x + 5  # Cannot fold - x is unknown
    return y


def not_constant_conditional(flag):
    """Value depends on conditional with unknown condition."""
    if flag:
        x = 10
    else:
        x = 20
    return x  # x is not constant (depends on flag)


def constant_redefined():
    """Constant redefined: track most recent value."""
    x = 5
    y = x  # y = 5
    x = 10
    z = x  # z = 10 (x was redefined)
    return y + z


def constant_string():
    """String constant propagation."""
    name = "hello"
    greeting = name + " world"  # Can be folded to "hello world"
    return greeting


def constant_in_loop():
    """Constant becomes non-constant in loop."""
    x = 0
    for i in range(10):
        x = x + i  # x is not constant (changes each iteration)
    return x


def constant_with_phi():
    """Constant at merge point (phi function)."""
    x = 5
    if True:
        y = x + 1  # y = 6
    else:
        y = x + 2  # Unreachable, but if reachable y = 7
    return y  # y = 6 (only one path taken)
