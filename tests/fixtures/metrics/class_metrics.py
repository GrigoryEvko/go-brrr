# Test fixtures for class-level metrics
# Tests cohesion (LCOM), coupling, and class size metrics


class HighCohesionClass:
    """High cohesion: all methods use the same attributes."""

    def __init__(self, value):
        self.value = value
        self.multiplier = 1

    def get_value(self):
        return self.value * self.multiplier

    def set_value(self, v):
        self.value = v

    def double(self):
        self.value = self.value * 2
        return self.value

    def scale(self, factor):
        self.multiplier = factor
        return self.get_value()


class LowCohesionClass:
    """Low cohesion: methods use different, unrelated attributes."""

    def __init__(self):
        self.users = []
        self.products = []
        self.orders = []
        self.logs = []
        self.config = {}

    def add_user(self, user):
        self.users.append(user)

    def get_user(self, user_id):
        for u in self.users:
            if u["id"] == user_id:
                return u
        return None

    def add_product(self, product):
        self.products.append(product)

    def get_product(self, product_id):
        for p in self.products:
            if p["id"] == product_id:
                return p
        return None

    def add_order(self, order):
        self.orders.append(order)

    def get_orders_by_user(self, user_id):
        return [o for o in self.orders if o["user_id"] == user_id]

    def log_message(self, msg):
        self.logs.append(msg)

    def get_config(self, key):
        return self.config.get(key)


class GodClass:
    """God class: too many responsibilities, methods, and lines."""

    def __init__(self, db_config, cache_config, api_config, queue_config):
        self.db = db_config
        self.cache = cache_config
        self.api = api_config
        self.queue = queue_config
        self.users = {}
        self.products = {}
        self.orders = {}
        self.payments = {}
        self.logs = []
        self.metrics = {}

    # User management
    def create_user(self, name, email):
        user = {"name": name, "email": email, "id": len(self.users)}
        self.users[user["id"]] = user
        self.log("Created user: " + name)
        return user

    def update_user(self, user_id, data):
        if user_id in self.users:
            self.users[user_id].update(data)
            self.log(f"Updated user: {user_id}")
        return self.users.get(user_id)

    def delete_user(self, user_id):
        if user_id in self.users:
            del self.users[user_id]
            self.log(f"Deleted user: {user_id}")

    def get_user(self, user_id):
        return self.users.get(user_id)

    def list_users(self):
        return list(self.users.values())

    # Product management
    def create_product(self, name, price):
        product = {"name": name, "price": price, "id": len(self.products)}
        self.products[product["id"]] = product
        return product

    def update_product(self, product_id, data):
        if product_id in self.products:
            self.products[product_id].update(data)
        return self.products.get(product_id)

    def delete_product(self, product_id):
        if product_id in self.products:
            del self.products[product_id]

    def get_product(self, product_id):
        return self.products.get(product_id)

    def list_products(self):
        return list(self.products.values())

    # Order management
    def create_order(self, user_id, items):
        order = {"user_id": user_id, "items": items, "id": len(self.orders)}
        self.orders[order["id"]] = order
        return order

    def process_order(self, order_id):
        order = self.orders.get(order_id)
        if order:
            order["status"] = "processed"
        return order

    def cancel_order(self, order_id):
        order = self.orders.get(order_id)
        if order:
            order["status"] = "cancelled"
        return order

    # Payment management
    def process_payment(self, order_id, amount, method):
        payment = {"order_id": order_id, "amount": amount, "method": method}
        self.payments[order_id] = payment
        return payment

    def refund_payment(self, order_id):
        if order_id in self.payments:
            self.payments[order_id]["status"] = "refunded"

    # Logging and metrics
    def log(self, message):
        self.logs.append({"message": message})

    def get_logs(self):
        return self.logs

    def record_metric(self, name, value):
        self.metrics[name] = value

    def get_metrics(self):
        return self.metrics


class SmallClass:
    """Small, focused class with single responsibility."""

    def __init__(self, data):
        self.data = data

    def process(self):
        return self.data.strip().lower()

    def validate(self):
        return len(self.data) > 0
