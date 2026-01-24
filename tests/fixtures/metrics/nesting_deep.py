# Test fixtures for deep nesting analysis
# Expected: max nesting depth 5+ levels


def nesting_depth_7(data):
    """Maximum nesting depth: 7 levels."""
    if data:  # Level 1
        for item in data:  # Level 2
            if item.get("active"):  # Level 3
                try:  # Level 4
                    for sub in item.get("items", []):  # Level 5
                        if sub.get("valid"):  # Level 6
                            with open(sub["path"]) as f:  # Level 7
                                return f.read()
                except Exception:
                    pass
    return None


def nesting_if_cascade(a, b, c, d, e, f):
    """Nested if statements: 6 levels."""
    if a:
        if b:
            if c:
                if d:
                    if e:
                        if f:
                            return "all true"
                        return "f false"
                    return "e false"
                return "d false"
            return "c false"
        return "b false"
    return "a false"


def nesting_loops(matrix):
    """Nested loops: 4 levels."""
    result = 0
    for i, row in enumerate(matrix):
        for j, cell in enumerate(row):
            if cell > 0:
                for k in range(cell):
                    for m in range(k):
                        result += m * cell
    return result


def nesting_mixed(data, config):
    """Mixed nesting: loops, conditions, exceptions."""
    results = []

    for item in data:
        try:
            if item["type"] == "complex":
                for sub in item["children"]:
                    if sub["enabled"]:
                        while sub["value"] > 0:
                            try:
                                results.append(process(sub))
                                sub["value"] -= 1
                            except ValueError:
                                break
        except KeyError:
            continue

    return results


def process(x):
    """Helper function."""
    return x["value"] * 2


def nesting_with_context_managers(paths, config):
    """Nested context managers."""
    results = {}

    for path in paths:
        with open(path) as f:
            try:
                for line in f:
                    if line.strip():
                        with open(path + ".out", "a") as out:
                            if config.get("transform"):
                                out.write(line.upper())
                            else:
                                out.write(line)
            except IOError:
                pass

    return results


# Shallow nesting for comparison
def nesting_depth_1(items):
    """Nesting depth: 1 level."""
    for item in items:
        yield item * 2


def nesting_depth_2(data):
    """Nesting depth: 2 levels."""
    for item in data:
        if item > 0:
            yield item
