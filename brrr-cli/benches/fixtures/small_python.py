"""
Small Python module for benchmarking AST extraction.

This module contains typical Python constructs including functions,
classes, decorators, type hints, and various import styles.
"""

from __future__ import annotations

import os
import sys
import json
import asyncio
from typing import Optional, List, Dict, Any, TypeVar, Generic
from dataclasses import dataclass, field
from collections import defaultdict
from pathlib import Path
from abc import ABC, abstractmethod


T = TypeVar("T")
K = TypeVar("K")
V = TypeVar("V")


def simple_function(x: int) -> int:
    """A simple pure function."""
    return x * 2


def function_with_defaults(
    name: str,
    count: int = 10,
    prefix: str = "item_",
    suffix: Optional[str] = None,
) -> List[str]:
    """Generate a list of strings with configurable formatting."""
    items = []
    for i in range(count):
        item = f"{prefix}{name}_{i}"
        if suffix:
            item = f"{item}{suffix}"
        items.append(item)
    return items


async def async_fetch_data(url: str, timeout: float = 30.0) -> Dict[str, Any]:
    """Asynchronously fetch data from a URL with timeout."""
    await asyncio.sleep(0.1)  # Simulate network delay
    return {"url": url, "status": "success", "data": {}}


async def async_batch_processor(
    items: List[str],
    batch_size: int = 100,
) -> List[Dict[str, Any]]:
    """Process items in batches asynchronously."""
    results = []
    for i in range(0, len(items), batch_size):
        batch = items[i : i + batch_size]
        batch_results = await asyncio.gather(
            *[async_fetch_data(item) for item in batch]
        )
        results.extend(batch_results)
    return results


@dataclass
class Point:
    """A 2D point with x and y coordinates."""

    x: float
    y: float

    def distance_to(self, other: Point) -> float:
        """Calculate Euclidean distance to another point."""
        dx = self.x - other.x
        dy = self.y - other.y
        return (dx * dx + dy * dy) ** 0.5

    def __add__(self, other: Point) -> Point:
        return Point(self.x + other.x, self.y + other.y)


@dataclass
class Rectangle:
    """A rectangle defined by two corners."""

    top_left: Point
    bottom_right: Point

    @property
    def width(self) -> float:
        return abs(self.bottom_right.x - self.top_left.x)

    @property
    def height(self) -> float:
        return abs(self.bottom_right.y - self.top_left.y)

    @property
    def area(self) -> float:
        return self.width * self.height

    def contains(self, point: Point) -> bool:
        """Check if a point is inside the rectangle."""
        return (
            self.top_left.x <= point.x <= self.bottom_right.x
            and self.top_left.y <= point.y <= self.bottom_right.y
        )


class BaseProcessor(ABC, Generic[T]):
    """Abstract base class for data processors."""

    def __init__(self, name: str):
        self.name = name
        self._cache: Dict[str, T] = {}

    @abstractmethod
    def process(self, data: T) -> T:
        """Process the input data."""
        pass

    def process_with_cache(self, key: str, data: T) -> T:
        """Process data with caching."""
        if key in self._cache:
            return self._cache[key]
        result = self.process(data)
        self._cache[key] = result
        return result


class StringProcessor(BaseProcessor[str]):
    """Processor for string data."""

    def __init__(self, name: str, uppercase: bool = False):
        super().__init__(name)
        self.uppercase = uppercase

    def process(self, data: str) -> str:
        """Process string by optionally converting to uppercase."""
        if self.uppercase:
            return data.upper()
        return data.lower()


class NumberProcessor(BaseProcessor[float]):
    """Processor for numeric data."""

    def __init__(self, name: str, scale: float = 1.0):
        super().__init__(name)
        self.scale = scale

    def process(self, data: float) -> float:
        """Scale the input number."""
        return data * self.scale


class ConfigManager:
    """Manages application configuration."""

    _instance: Optional[ConfigManager] = None

    def __new__(cls) -> ConfigManager:
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._config = {}
        return cls._instance

    def get(self, key: str, default: Any = None) -> Any:
        """Get a configuration value."""
        return self._config.get(key, default)

    def set(self, key: str, value: Any) -> None:
        """Set a configuration value."""
        self._config[key] = value

    def load_from_file(self, path: Path) -> bool:
        """Load configuration from a JSON file."""
        if not path.exists():
            return False
        with open(path) as f:
            self._config.update(json.load(f))
        return True


def create_pipeline(*processors: BaseProcessor) -> callable:
    """Create a processing pipeline from multiple processors."""

    def pipeline(data):
        result = data
        for processor in processors:
            result = processor.process(result)
        return result

    return pipeline


def validate_input(
    data: Dict[str, Any],
    required_fields: List[str],
    optional_fields: Optional[List[str]] = None,
) -> tuple[bool, List[str]]:
    """Validate input data against required and optional fields."""
    errors = []
    for field in required_fields:
        if field not in data:
            errors.append(f"Missing required field: {field}")
    return len(errors) == 0, errors


if __name__ == "__main__":
    # Example usage
    p1 = Point(0, 0)
    p2 = Point(3, 4)
    print(f"Distance: {p1.distance_to(p2)}")
