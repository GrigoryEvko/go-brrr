# Test fixtures for high complexity functions
# Expected: cyclomatic complexity > 15, cognitive complexity > 10


def complex_validation(data):
    """High complexity: multiple branches and conditions."""
    # CC: ~20+ (many branches)
    if not data:
        return {"error": "No data"}

    if "type" not in data:
        return {"error": "Missing type"}

    data_type = data["type"]

    if data_type == "user":
        if "name" not in data:
            return {"error": "Missing name"}
        if "email" not in data:
            return {"error": "Missing email"}
        if "@" not in data["email"]:
            return {"error": "Invalid email"}
        if len(data["name"]) < 2:
            return {"error": "Name too short"}
        if len(data["name"]) > 100:
            return {"error": "Name too long"}
        return {"status": "valid_user", "data": data}

    elif data_type == "order":
        if "items" not in data:
            return {"error": "Missing items"}
        if not isinstance(data["items"], list):
            return {"error": "Items must be list"}
        if len(data["items"]) == 0:
            return {"error": "Empty order"}

        total = 0
        for item in data["items"]:
            if "price" not in item:
                return {"error": "Item missing price"}
            if "quantity" not in item:
                return {"error": "Item missing quantity"}
            if item["price"] < 0:
                return {"error": "Negative price"}
            if item["quantity"] <= 0:
                return {"error": "Invalid quantity"}
            total += item["price"] * item["quantity"]

        if total > 10000 and "approval" not in data:
            return {"error": "Large order needs approval"}

        return {"status": "valid_order", "total": total}

    elif data_type == "payment":
        if "method" not in data:
            return {"error": "Missing method"}
        if "amount" not in data:
            return {"error": "Missing amount"}
        if data["amount"] <= 0:
            return {"error": "Invalid amount"}

        method = data["method"]
        if method == "card":
            if "card_number" not in data:
                return {"error": "Missing card number"}
            if len(data["card_number"]) != 16:
                return {"error": "Invalid card number"}
        elif method == "bank":
            if "account" not in data:
                return {"error": "Missing account"}
            if "routing" not in data:
                return {"error": "Missing routing"}
        elif method == "crypto":
            if "wallet" not in data:
                return {"error": "Missing wallet"}
        else:
            return {"error": "Unknown payment method"}

        return {"status": "valid_payment", "amount": data["amount"]}

    else:
        return {"error": "Unknown type"}


def deeply_nested_function(data, config, options):
    """High cognitive complexity: deeply nested structures."""
    results = []

    for item in data:
        if item.get("active"):
            for sub in item.get("children", []):
                if sub.get("enabled"):
                    for prop in sub.get("properties", []):
                        if prop.get("type") == "number":
                            if prop.get("value") > 0:
                                if config.get("validate"):
                                    if options.get("strict"):
                                        if prop["value"] > options.get("max", 100):
                                            results.append({"error": "Too large"})
                                        else:
                                            results.append({"value": prop["value"]})
                                    else:
                                        results.append({"value": prop["value"]})
                                else:
                                    results.append({"value": prop["value"]})
                        elif prop.get("type") == "string":
                            if len(prop.get("value", "")) > 0:
                                results.append({"text": prop["value"]})

    return results


def many_boolean_conditions(a, b, c, d, e, f, g, h):
    """High complexity from boolean operators."""
    # Each && and || adds to cyclomatic complexity
    if a and b and c:
        return 1
    if a or b or c:
        return 2
    if (a and b) or (c and d):
        return 3
    if (a or b) and (c or d):
        return 4
    if a and (b or (c and d)):
        return 5
    if (a and b and c) or (d and e and f):
        return 6
    if a or b or c or d or e or f:
        return 7
    if a and b and c and d and e and f and g and h:
        return 8
    return 0
