# Test fixtures for clone detection
# Contains duplicate code patterns


# ============================================
# CLONE GROUP 1: Exact duplicates (Type-1)
# ============================================

def process_user_data_v1(user):
    """First instance of clone group 1."""
    if not user:
        return None
    name = user.get("name", "")
    email = user.get("email", "")
    if not name or not email:
        return None
    return {
        "name": name.strip(),
        "email": email.lower().strip(),
        "active": True
    }


def process_user_data_v2(user):
    """Second instance of clone group 1 - exact copy."""
    if not user:
        return None
    name = user.get("name", "")
    email = user.get("email", "")
    if not name or not email:
        return None
    return {
        "name": name.strip(),
        "email": email.lower().strip(),
        "active": True
    }


# ============================================
# CLONE GROUP 2: Renamed identifiers (Type-2)
# ============================================

def calculate_order_total(items, tax_rate):
    """First instance of clone group 2."""
    subtotal = 0
    for item in items:
        price = item["price"]
        quantity = item["quantity"]
        subtotal += price * quantity
    tax = subtotal * tax_rate
    total = subtotal + tax
    return total


def calculate_invoice_amount(products, vat_percentage):
    """Type-2 clone: same structure, renamed identifiers."""
    base_amount = 0
    for product in products:
        cost = product["price"]
        count = product["quantity"]
        base_amount += cost * count
    vat = base_amount * vat_percentage
    final_amount = base_amount + vat
    return final_amount


# ============================================
# CLONE GROUP 3: Modified structure (Type-3)
# ============================================

def validate_input_strict(data):
    """First instance of clone group 3."""
    if not data:
        return False
    if "name" not in data:
        return False
    if "value" not in data:
        return False
    if len(data["name"]) < 3:
        return False
    if data["value"] < 0:
        return False
    return True


def validate_input_lenient(data):
    """Type-3 clone: similar structure with modifications."""
    if not data:
        return False
    if "name" not in data:
        return False
    # Missing value check (modification)
    if len(data["name"]) < 1:  # Different threshold
        return False
    # Removed negative value check (modification)
    return True


# ============================================
# NOT CLONES: Similar but different logic
# ============================================

def process_request(req):
    """Not a clone - different purpose."""
    if not req:
        raise ValueError("No request")
    method = req.get("method")
    path = req.get("path")
    return f"{method} {path}"


def format_response(data):
    """Not a clone - different structure."""
    return {
        "status": "success",
        "data": data,
        "timestamp": "2024-01-01"
    }


# ============================================
# CLONE GROUP 4: Multiple similar functions
# ============================================

def save_user(user):
    """Clone group 4 instance 1."""
    validate(user)
    prepare(user)
    store("users", user)
    log("Saved user")


def save_product(product):
    """Clone group 4 instance 2 - same pattern."""
    validate(product)
    prepare(product)
    store("products", product)
    log("Saved product")


def save_order(order):
    """Clone group 4 instance 3 - same pattern."""
    validate(order)
    prepare(order)
    store("orders", order)
    log("Saved order")


# Helper stubs
def validate(x): pass
def prepare(x): pass
def store(table, x): pass
def log(msg): pass
