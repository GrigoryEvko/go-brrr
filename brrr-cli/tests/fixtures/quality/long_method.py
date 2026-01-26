# Test fixtures for long method detection
# Contains methods of various lengths and complexity


def short_method():
    """Short method: should not be flagged."""
    return 42


def medium_method(data):
    """Medium method: borderline length."""
    result = []
    for item in data:
        if item.get("active"):
            value = item.get("value", 0)
            processed = value * 2
            result.append(processed)
    return result


def long_method_simple(data, config, options):
    """Long method with low complexity (many simple statements)."""
    result = {}

    # Section 1: Initialize
    result["status"] = "pending"
    result["items"] = []
    result["metadata"] = {}
    result["errors"] = []
    result["warnings"] = []

    # Section 2: Process configuration
    result["config_name"] = config.get("name", "default")
    result["config_version"] = config.get("version", "1.0")
    result["config_enabled"] = config.get("enabled", True)
    result["config_timeout"] = config.get("timeout", 30)
    result["config_retries"] = config.get("retries", 3)

    # Section 3: Process options
    result["opt_verbose"] = options.get("verbose", False)
    result["opt_debug"] = options.get("debug", False)
    result["opt_format"] = options.get("format", "json")
    result["opt_output"] = options.get("output", "stdout")
    result["opt_quiet"] = options.get("quiet", False)

    # Section 4: Process data
    for item in data:
        processed_item = {}
        processed_item["id"] = item.get("id")
        processed_item["name"] = item.get("name")
        processed_item["value"] = item.get("value")
        processed_item["type"] = item.get("type")
        processed_item["active"] = item.get("active")
        result["items"].append(processed_item)

    # Section 5: Add metadata
    result["metadata"]["total"] = len(result["items"])
    result["metadata"]["processed_at"] = "2024-01-01"
    result["metadata"]["processor"] = "v1"
    result["metadata"]["source"] = "api"

    # Section 6: Finalize
    result["status"] = "complete"
    result["success"] = True

    return result


def long_method_complex(data, config):
    """Long method with high complexity (should definitely be flagged)."""
    results = []
    errors = []
    warnings = []

    if not data:
        return {"error": "No data provided"}

    if not config:
        config = {"mode": "default", "threshold": 10}

    mode = config.get("mode", "default")
    threshold = config.get("threshold", 10)

    for i, item in enumerate(data):
        if not item:
            errors.append(f"Item {i} is null")
            continue

        if "type" not in item:
            warnings.append(f"Item {i} missing type")
            item["type"] = "unknown"

        item_type = item["type"]

        if item_type == "user":
            if "name" not in item:
                errors.append(f"User {i} missing name")
                continue
            if "email" not in item:
                errors.append(f"User {i} missing email")
                continue

            name = item["name"].strip()
            email = item["email"].lower().strip()

            if len(name) < 2:
                warnings.append(f"User {i} name too short")
            if "@" not in email:
                errors.append(f"User {i} invalid email")
                continue

            if mode == "strict":
                if len(name) < 5:
                    errors.append(f"User {i} name too short for strict mode")
                    continue

            results.append({
                "type": "user",
                "name": name,
                "email": email,
                "index": i
            })

        elif item_type == "product":
            if "price" not in item:
                errors.append(f"Product {i} missing price")
                continue
            if "quantity" not in item:
                errors.append(f"Product {i} missing quantity")
                continue

            price = item["price"]
            quantity = item["quantity"]

            if price < 0:
                errors.append(f"Product {i} negative price")
                continue
            if quantity <= 0:
                errors.append(f"Product {i} invalid quantity")
                continue

            if price > threshold:
                warnings.append(f"Product {i} price above threshold")

            results.append({
                "type": "product",
                "price": price,
                "quantity": quantity,
                "total": price * quantity,
                "index": i
            })

        elif item_type == "order":
            if "items" not in item:
                errors.append(f"Order {i} missing items")
                continue

            order_items = item["items"]
            if not order_items:
                warnings.append(f"Order {i} empty")
                continue

            total = 0
            for j, order_item in enumerate(order_items):
                if "price" in order_item and "quantity" in order_item:
                    total += order_item["price"] * order_item["quantity"]
                else:
                    warnings.append(f"Order {i} item {j} incomplete")

            results.append({
                "type": "order",
                "item_count": len(order_items),
                "total": total,
                "index": i
            })

        else:
            warnings.append(f"Item {i} unknown type: {item_type}")
            results.append({
                "type": "unknown",
                "original_type": item_type,
                "index": i
            })

    return {
        "results": results,
        "errors": errors,
        "warnings": warnings,
        "total_processed": len(results),
        "total_errors": len(errors),
        "total_warnings": len(warnings),
        "success": len(errors) == 0
    }
