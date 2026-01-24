# Test fixtures for test quality analysis
# Contains tests with various quality characteristics

import unittest


class HighQualityTests(unittest.TestCase):
    """High quality test class with good practices."""

    def test_with_multiple_assertions(self):
        """Good: multiple assertions checking different aspects."""
        result = calculate(5, 3)
        self.assertIsNotNone(result)
        self.assertEqual(result["sum"], 8)
        self.assertEqual(result["product"], 15)
        self.assertIn("sum", result)
        self.assertIn("product", result)

    def test_boundary_values(self):
        """Good: tests boundary conditions."""
        # Test zero
        self.assertEqual(process(0), 0)
        # Test negative
        self.assertEqual(process(-1), -1)
        # Test max value
        self.assertEqual(process(2**31 - 1), 2**31 - 1)
        # Test min value
        self.assertEqual(process(-(2**31)), -(2**31))

    def test_exception_handling(self):
        """Good: tests exception cases."""
        with self.assertRaises(ValueError):
            validate(None)
        with self.assertRaises(TypeError):
            validate(123)

    def test_isolated_no_global_state(self):
        """Good: isolated test, no global state."""
        obj = DataProcessor()
        result = obj.process({"value": 10})
        self.assertEqual(result, 20)


class LowQualityTests(unittest.TestCase):
    """Low quality test class with anti-patterns."""

    def test_no_assertions(self):
        """Bad: no assertions at all."""
        result = calculate(5, 3)
        # No assertions!

    def test_single_weak_assertion(self):
        """Bad: only one weak assertion."""
        result = calculate(5, 3)
        self.assertIsNotNone(result)
        # Should check actual values

    def test_uses_global_state(self):
        """Bad: depends on global state."""
        global_counter = get_global_counter()
        self.assertTrue(global_counter > 0)

    def test_hardcoded_sleep(self):
        """Bad: uses hardcoded sleep."""
        import time
        start_async_operation()
        time.sleep(2)  # Bad practice
        result = get_async_result()
        self.assertIsNotNone(result)

    def test_print_instead_of_assert(self):
        """Bad: uses print instead of assertions."""
        result = calculate(5, 3)
        print(f"Result is {result}")  # Should be assertion


class MixedQualityTests(unittest.TestCase):
    """Mixed quality - some good, some bad."""

    def test_good_assertions(self):
        """Good test with proper assertions."""
        self.assertEqual(1 + 1, 2)
        self.assertNotEqual(1 + 1, 3)

    def test_missing_edge_cases(self):
        """Partial: tests happy path only."""
        result = divide(10, 2)
        self.assertEqual(result, 5)
        # Missing: divide by zero test


# Mock objects for tests
def calculate(a, b):
    return {"sum": a + b, "product": a * b}


def process(x):
    return x


def validate(x):
    if x is None:
        raise ValueError("None not allowed")
    if isinstance(x, int):
        raise TypeError("Int not allowed")
    return True


def divide(a, b):
    return a / b


def get_global_counter():
    return 1


def start_async_operation():
    pass


def get_async_result():
    return {"status": "done"}


class DataProcessor:
    def process(self, data):
        return data["value"] * 2
