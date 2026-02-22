"""Module docstring for comprehensive Python testing."""

import os
import sys
from typing import Optional, Any, TYPE_CHECKING
from pathlib import Path
from collections import defaultdict

if TYPE_CHECKING:
    from collections import OrderedDict


# Decorators
@property
def prop_example(self):
    return self._value


@staticmethod
def static_example():
    return 42


class MyClass:
    """A test class with various method types."""

    def __init__(self, value: int) -> None:
        self._value = value

    @property
    def value(self) -> int:
        return self._value

    @staticmethod
    def create() -> 'MyClass':
        return MyClass(0)

    @classmethod
    def from_dict(cls, data: dict) -> 'MyClass':
        return cls(data.get('value', 0))

    def regular_method(self, x: int) -> int:
        return self._value + x


# Async/await
async def fetch_data(url: str) -> bytes:
    """Fetch data asynchronously."""
    async with aiohttp.ClientSession() as session:
        async for chunk in session.get(url):
            yield chunk


# Generator
def fibonacci(n: int):
    """Generate Fibonacci numbers."""
    a, b = 0, 1
    for _ in range(n):
        yield a
        a, b = b, a + b


# Yield from
def chain(*iterables):
    for it in iterables:
        yield from it


# Match/case (3.10+)
def process_command(cmd):
    match cmd:
        case {"action": "move", "direction": direction}:
            move(direction)
        case {"action": "quit"} if confirm():
            return
        case _:
            print("unknown")


# Walrus operator
def process_data(items):
    if (n := len(items)) > 10:
        print(f"Too many: {n}")
    results = [y for x in items if (y := transform(x)) is not None]
    while (line := input()):
        process(line)


# Comprehensions
def comprehension_examples():
    squares = [x**2 for x in range(10) if x % 2 == 0]
    mapping = {k: v for k, v in pairs if k not in excluded}
    unique = {x for x in items if pred(x)}
    gen = (x for x in range(100) if expensive_check(x))
    return squares


# Complex type annotations
def complex_types(
    data: list[tuple[str, int]],
    callback: Optional['Callable[[int], bool]'] = None,
    *args: tuple[str, ...],
    **kwargs: dict[str, Any],
) -> dict[str, list[int]]:
    pass


# Security patterns
def dangerous_stuff():
    eval("user_input")
    exec(code_string)
    os.system(f"rm -rf {path}")
    import pickle
    pickle.loads(untrusted_data)
    subprocess.call(cmd, shell=True)


# Dead code after return
def unreachable_after_return():
    return 42
    print("never reached")


def _private_unused():
    """This function is not called anywhere."""
    pass


# Nested functions
def outer():
    x = 10
    def inner():
        return x
    return inner()


# Control flow
def complex_control_flow(x, y, z):
    if x > 0:
        if y > 0:
            return x + y
        elif z > 0:
            return x + z
        else:
            for i in range(x):
                if i % 2 == 0:
                    continue
                try:
                    result = process(i)
                except ValueError:
                    break
                except (TypeError, KeyError) as e:
                    raise RuntimeError("bad") from e
                finally:
                    cleanup()
            return -1
    while x > 0:
        x -= 1
    return 0


# Exception handling
def exception_handling():
    try:
        risky()
    except ValueError as e:
        handle_value_error(e)
    except (TypeError, KeyError):
        handle_type_error()
    except Exception:
        handle_generic()
    else:
        success()
    finally:
        cleanup()


# Context managers
def context_managers():
    with open("file.txt") as f:
        data = f.read()
    with open("a") as a, open("b") as b:
        merge(a, b)
