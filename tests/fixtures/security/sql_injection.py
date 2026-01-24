# Test fixtures for SQL injection detection
# Contains various SQL injection vulnerability patterns

import sqlite3


def vulnerable_string_concat(user_id):
    """Vulnerable: direct string concatenation."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # VULNERABLE: String concatenation
    query = "SELECT * FROM users WHERE id = " + user_id
    cursor.execute(query)
    return cursor.fetchall()


def vulnerable_fstring(username):
    """Vulnerable: f-string interpolation."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # VULNERABLE: f-string
    cursor.execute(f"SELECT * FROM users WHERE name = '{username}'")
    return cursor.fetchall()


def vulnerable_format_string(email):
    """Vulnerable: format string interpolation."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # VULNERABLE: format()
    query = "DELETE FROM users WHERE email = '{}'".format(email)
    cursor.execute(query)


def vulnerable_percent_format(user_input):
    """Vulnerable: percent formatting."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # VULNERABLE: % formatting
    query = "UPDATE users SET status = '%s'" % user_input
    cursor.execute(query)


def safe_parameterized_query(user_id):
    """Safe: parameterized query."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # SAFE: Parameterized query
    cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
    return cursor.fetchall()


def safe_parameterized_named(username, email):
    """Safe: named parameterized query."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # SAFE: Named parameters
    cursor.execute(
        "SELECT * FROM users WHERE name = :name AND email = :email",
        {"name": username, "email": email}
    )
    return cursor.fetchall()


def safe_constant_query():
    """Safe: constant query string."""
    conn = sqlite3.connect("test.db")
    cursor = conn.cursor()
    # SAFE: No user input
    cursor.execute("SELECT COUNT(*) FROM users WHERE active = 1")
    return cursor.fetchone()
