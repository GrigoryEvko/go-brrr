# Test fixtures for unsafe deserialization detection
# Contains various deserialization vulnerability patterns

import pickle
import yaml
import marshal
import shelve


def vulnerable_pickle_loads(user_data):
    """Vulnerable: pickle.loads with user data."""
    # VULNERABLE: pickle can execute arbitrary code
    return pickle.loads(user_data)


def vulnerable_pickle_load(user_file):
    """Vulnerable: pickle.load with user file."""
    # VULNERABLE: pickle from untrusted source
    with open(user_file, 'rb') as f:
        return pickle.load(f)


def vulnerable_yaml_load(yaml_content):
    """Vulnerable: yaml.load without safe loader."""
    # VULNERABLE: yaml.load can execute code
    return yaml.load(yaml_content)


def vulnerable_yaml_unsafe_load(data):
    """Vulnerable: yaml.unsafe_load explicit."""
    # VULNERABLE: Explicitly unsafe
    return yaml.unsafe_load(data)


def vulnerable_marshal_loads(data):
    """Vulnerable: marshal.loads with user data."""
    # VULNERABLE: marshal can be exploited
    return marshal.loads(data)


def vulnerable_shelve_open(user_path):
    """Vulnerable: shelve with user-controlled path."""
    # VULNERABLE: shelve uses pickle internally
    db = shelve.open(user_path)
    return db['key']


def vulnerable_eval_json(json_str):
    """Vulnerable: eval for JSON parsing."""
    # VULNERABLE: eval can execute code
    return eval(json_str)


def safe_json_loads(json_data):
    """Safe: json.loads for JSON data."""
    import json
    # SAFE: JSON parser doesn't execute code
    return json.loads(json_data)


def safe_yaml_safe_load(yaml_content):
    """Safe: yaml.safe_load for YAML data."""
    # SAFE: SafeLoader prevents code execution
    return yaml.safe_load(yaml_content)


def safe_yaml_cloader(yaml_content):
    """Safe: yaml with CSafeLoader."""
    # SAFE: CSafeLoader is safe
    return yaml.load(yaml_content, Loader=yaml.CSafeLoader)


def safe_pickle_hmac_verified(data, signature, key):
    """Safe: pickle with HMAC verification."""
    import hmac
    import hashlib

    # SAFE: Verify signature before unpickling
    expected_sig = hmac.new(key, data, hashlib.sha256).digest()
    if not hmac.compare_digest(signature, expected_sig):
        raise ValueError("Invalid signature")

    return pickle.loads(data)
