# Test fixtures for available expressions analysis
# Patterns for common subexpression elimination (CSE)


def cse_opportunity():
    """Common subexpression elimination opportunity."""
    a = x + y  # Expression x+y computed
    b = x + y  # Same expression - CSE candidate
    return a + b


def cse_killed():
    """Expression killed by assignment."""
    a = x + y   # x+y available
    x = 10      # x reassigned - kills x+y
    b = x + y   # Must recompute x+y
    return a + b


def cse_in_loop():
    """Loop invariant expression."""
    total = 0
    factor = a * b  # Compute once before loop
    for i in range(10):
        total += i * factor  # a*b is loop invariant
    return total


def cse_conditional():
    """Expression available on some paths."""
    if flag:
        a = x + y  # x+y available on true path
    else:
        a = 0      # x+y not computed on false path
    # x+y not available here (not on all paths)
    b = x + y
    return a + b


def cse_both_branches():
    """Expression computed on all paths."""
    if flag:
        a = x + y  # x+y computed
        b = 1
    else:
        a = x + y  # x+y computed
        b = 2
    # x+y is available (computed on all paths)
    c = x + y  # CSE candidate
    return a + b + c


def partially_available():
    """Partial redundancy - expression available on some paths."""
    if condition1:
        a = x + y  # Computed
    # x+y partially available

    if condition2:
        b = x + y  # May or may not be redundant
    else:
        b = 0

    return b


def very_busy_expression():
    """Very busy: expression computed on all forward paths."""
    # x+y is very busy here (will definitely be used)
    if flag:
        a = x + y
    else:
        b = x + y
    # Could hoist x+y before the if


def complex_expression():
    """Complex expression for CSE."""
    a = (x * y + z) / w
    b = (x * y + z) / w  # Same complex expression
    c = x * y            # Subexpression
    d = x * y + z        # Another subexpression
    return a + b + c + d


def side_effect_kill():
    """Function call may kill expressions."""
    a = x + y
    modify_x()  # May change x - kills x+y
    b = x + y   # Must recompute
    return a + b


def modify_x():
    global x
    x = 100


# Globals for the examples
x = 1
y = 2
z = 3
w = 4
a = 5
b = 6
flag = True
condition1 = True
condition2 = True
