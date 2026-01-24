# Test fixtures for circular dependency detection
# Module A imports from B, B imports from C, C imports from A


# Simulated module structure using classes
# In real code, these would be in separate files


class ModuleA:
    """Module A - depends on ModuleB."""

    def process(self, data):
        # Import from B (creates A -> B dependency)
        b = ModuleB()
        return b.transform(data)


class ModuleB:
    """Module B - depends on ModuleC."""

    def transform(self, data):
        # Import from C (creates B -> C dependency)
        c = ModuleC()
        return c.validate(data)


class ModuleC:
    """Module C - depends on ModuleA (creates cycle)."""

    def validate(self, data):
        # Import from A (creates C -> A dependency)
        # This creates a cycle: A -> B -> C -> A
        a = ModuleA()
        return data is not None


# Non-circular dependencies

class ServiceX:
    """Service X - depends on UtilY."""

    def run(self):
        y = UtilY()
        return y.helper()


class UtilY:
    """Utility Y - depends on nothing."""

    def helper(self):
        return "done"


# Function-level circular dependencies

def func_a():
    """Function A calls B."""
    return func_b() + 1


def func_b():
    """Function B calls C."""
    return func_c() + 1


def func_c():
    """Function C calls A (creates cycle)."""
    if some_condition():
        return func_a() + 1  # Cycle: A -> B -> C -> A
    return 0


def some_condition():
    return False


# Self-referential (not quite circular but recursive)

class SelfRef:
    """Self-referential class."""

    def process(self, depth=0):
        if depth > 5:
            return "done"
        # Calls itself (recursion, not circular dependency)
        return self.process(depth + 1)


def recursive_func(n):
    """Recursive function - not circular dependency."""
    if n <= 0:
        return 0
    return n + recursive_func(n - 1)
