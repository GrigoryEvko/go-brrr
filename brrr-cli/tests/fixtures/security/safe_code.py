# Test fixture for safe code (no false positives expected)
# This file contains patterns that look suspicious but are actually safe

import os
import json
import hashlib
import logging


# Safe: Constant SQL queries
SQL_CREATE_TABLE = """
    CREATE TABLE users (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        email TEXT UNIQUE
    )
"""


# Safe: Environment variables for secrets
API_KEY = os.environ.get("API_KEY")
DATABASE_URL = os.getenv("DATABASE_URL")


# Safe: Placeholder/example values
EXAMPLE_KEY = "YOUR_API_KEY_HERE"
SAMPLE_TOKEN = "xxxx-xxxx-xxxx-xxxx"


def safe_json_parsing(data_str):
    """Safe: JSON parsing, not eval."""
    return json.loads(data_str)


def safe_file_path_constant():
    """Safe: Hardcoded paths."""
    with open("/etc/hostname", "r") as f:
        return f.read()


def safe_hash_for_checksums(data):
    """Safe: MD5 for checksums (not security)."""
    # Note: MD5 is weak for security but OK for checksums
    return hashlib.md5(data).hexdigest()


def safe_subprocess_list(filename):
    """Safe: subprocess with list arguments."""
    import subprocess
    result = subprocess.run(["cat", filename], capture_output=True)
    return result.stdout


def safe_logging_constant():
    """Safe: Logging only constants."""
    logger = logging.getLogger(__name__)
    logger.info("Application started")
    logger.warning("Rate limit approaching")


def safe_parameterized_query(user_id, cursor):
    """Safe: Parameterized SQL query."""
    cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
    return cursor.fetchall()


def safe_path_validated(user_filename, base_dir):
    """Safe: Path validation before use."""
    full_path = os.path.join(base_dir, user_filename)
    real_path = os.path.realpath(full_path)

    if not real_path.startswith(os.path.realpath(base_dir)):
        raise ValueError("Invalid path")

    return full_path


def safe_url_allowlist(url, allowed):
    """Safe: URL allowlist validation."""
    from urllib.parse import urlparse
    parsed = urlparse(url)
    if parsed.netloc not in allowed:
        raise ValueError("Domain not allowed")
    return url


class SafeDataProcessor:
    """Safe class with no vulnerabilities."""

    def __init__(self, config):
        self.config = config
        self.logger = logging.getLogger(__name__)

    def process(self, data):
        """Process data safely."""
        self.logger.info("Processing started")
        result = json.loads(data)
        self.logger.info("Processing completed")
        return result
