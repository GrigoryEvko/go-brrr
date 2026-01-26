# Test fixtures for Halstead complexity metrics
# Various operator and operand patterns


def halstead_minimal():
    """Minimal Halstead metrics: very few operators/operands."""
    return 42


def halstead_simple_expression(a, b):
    """Simple expression with few unique operators."""
    return a + b


def halstead_many_operators(a, b, c, d, e):
    """Many different operators."""
    result = a + b - c * d / e
    result = result % 7
    result = result ** 2
    result = result // 3
    result = -result

    if a > b and c < d or e == 0:
        result = a if b else c

    return result | 1 & 2 ^ 3 << 1 >> 1


def halstead_many_operands(a, b, c, d, e, f, g, h, i, j, k):
    """Many unique operands."""
    total = a + b + c + d + e
    total += f + g + h + i + j + k
    return total


def halstead_high_volume(data, config, options, state, cache):
    """High Halstead volume: many operators and operands."""
    result = {}

    # Many operands
    result["sum"] = data["a"] + data["b"] + data["c"]
    result["product"] = data["x"] * data["y"] * data["z"]
    result["diff"] = config["max"] - config["min"]
    result["ratio"] = options["numerator"] / options["denominator"]

    # Many operators
    if state["enabled"] and not state["paused"]:
        if data["value"] > config["threshold"]:
            result["status"] = "high"
        elif data["value"] < config["min"]:
            result["status"] = "low"
        else:
            result["status"] = "normal"

    # Complex expressions
    result["score"] = (
        data["a"] * config["weight_a"] +
        data["b"] * config["weight_b"] +
        data["c"] * config["weight_c"]
    ) / (config["weight_a"] + config["weight_b"] + config["weight_c"])

    # Bitwise operations
    result["flags"] = (
        (1 << options["flag1"]) |
        (1 << options["flag2"]) |
        (1 << options["flag3"])
    )

    # Conditional expressions
    result["cached"] = cache.get("key") if "key" in cache else None

    return result


def halstead_repetitive(items):
    """Repetitive code increases N (total) but not n (unique)."""
    total = 0
    total = total + items[0]
    total = total + items[1]
    total = total + items[2]
    total = total + items[3]
    total = total + items[4]
    total = total + items[5]
    total = total + items[6]
    total = total + items[7]
    total = total + items[8]
    total = total + items[9]
    return total
