# Test fixtures for path traversal detection
# Contains various path traversal vulnerability patterns

import os
import shutil


def vulnerable_open_file(user_path):
    """Vulnerable: direct file open with user input."""
    # VULNERABLE: User-controlled path
    with open(user_path, 'r') as f:
        return f.read()


def vulnerable_path_join(user_filename):
    """Vulnerable: os.path.join with user input (bypass possible)."""
    base_dir = "/var/www/uploads"
    # VULNERABLE: Path join can be bypassed with absolute path
    full_path = os.path.join(base_dir, user_filename)
    with open(full_path, 'r') as f:
        return f.read()


def vulnerable_file_delete(file_path):
    """Vulnerable: delete file based on user input."""
    # VULNERABLE: User-controlled file deletion
    os.remove(file_path)


def vulnerable_copy_file(src, dest):
    """Vulnerable: copy with user-controlled paths."""
    # VULNERABLE: Both paths user-controlled
    shutil.copy(src, dest)


def vulnerable_read_binary(filename):
    """Vulnerable: binary file read with user input."""
    # VULNERABLE: User-controlled path in binary read
    with open(filename, 'rb') as f:
        return f.read()


def safe_validated_path(user_filename):
    """Safe: path validation before access."""
    base_dir = "/var/www/uploads"
    # Build path and validate
    full_path = os.path.join(base_dir, user_filename)
    real_path = os.path.realpath(full_path)

    # SAFE: Validate that resolved path is under base directory
    if not real_path.startswith(os.path.realpath(base_dir)):
        raise ValueError("Invalid path")

    with open(real_path, 'r') as f:
        return f.read()


def safe_hardcoded_path():
    """Safe: hardcoded path only."""
    # SAFE: No user input
    with open("/etc/hostname", 'r') as f:
        return f.read()


def safe_path_from_whitelist(filename):
    """Safe: filename from whitelist."""
    allowed_files = ["config.json", "settings.yaml", "README.md"]

    # SAFE: Validated against whitelist
    if filename not in allowed_files:
        raise ValueError("File not allowed")

    with open(os.path.join("/config", filename), 'r') as f:
        return f.read()
