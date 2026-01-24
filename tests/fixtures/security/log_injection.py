# Test fixtures for log injection detection
# Contains various log injection vulnerability patterns

import logging

logger = logging.getLogger(__name__)


def vulnerable_log_user_input(user_input):
    """Vulnerable: logging user input directly."""
    # VULNERABLE: User input can inject fake log entries
    logger.info("User action: " + user_input)


def vulnerable_log_format_string(username):
    """Vulnerable: f-string with user data in log."""
    # VULNERABLE: Can inject newlines and fake log entries
    logger.warning(f"Login attempt for user: {username}")


def vulnerable_log_percent_format(request_path):
    """Vulnerable: percent formatting with user data."""
    # VULNERABLE: User-controlled log content
    logging.error("Request failed for path: %s" % request_path)


def vulnerable_log_carriage_return(user_data):
    """Vulnerable: potential CRLF injection."""
    # VULNERABLE: Newlines can forge log entries
    logger.info("Processing data: " + user_data)


def vulnerable_log_exception_user_msg(user_message):
    """Vulnerable: exception with user message."""
    try:
        raise ValueError(user_message)
    except ValueError as e:
        # VULNERABLE: User-controlled exception message
        logger.exception("Error: %s", e)


def safe_structured_logging(username, action):
    """Safe: structured logging with separate fields."""
    # SAFE: Structured logging prevents injection
    logger.info("User action", extra={"username": username, "action": action})


def safe_sanitized_logging(user_input):
    """Safe: sanitized before logging."""
    # SAFE: Sanitize special characters
    sanitized = user_input.replace('\n', '\\n').replace('\r', '\\r')
    logger.info("User input: %s", sanitized)


def safe_constant_log():
    """Safe: only constants in log."""
    # SAFE: No user input
    logger.info("Application started successfully")
