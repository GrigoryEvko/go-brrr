# Test fixtures for SSRF (Server-Side Request Forgery) detection
# Contains various SSRF vulnerability patterns

import urllib.request
import requests
import httpx


def vulnerable_requests_get(user_url):
    """Vulnerable: requests.get with user URL."""
    # VULNERABLE: User-controlled URL
    response = requests.get(user_url)
    return response.text


def vulnerable_urllib_open(url):
    """Vulnerable: urllib with user URL."""
    # VULNERABLE: User-controlled URL
    with urllib.request.urlopen(url) as response:
        return response.read()


def vulnerable_httpx_get(target_url):
    """Vulnerable: httpx with user URL."""
    # VULNERABLE: User-controlled URL
    response = httpx.get(target_url)
    return response.text


def vulnerable_requests_post(endpoint, data):
    """Vulnerable: requests.post with user endpoint."""
    # VULNERABLE: User-controlled endpoint
    response = requests.post(endpoint, json=data)
    return response.json()


def vulnerable_url_from_header(headers):
    """Vulnerable: URL from request header."""
    # VULNERABLE: Attacker can supply internal URLs
    webhook_url = headers.get('X-Webhook-URL')
    return requests.post(webhook_url, json={"status": "ok"})


def vulnerable_url_from_query(request_params):
    """Vulnerable: URL from query parameter."""
    # VULNERABLE: User controls target
    target = request_params.get('callback_url')
    return requests.get(target)


def safe_allowlist_url(user_url, allowed_domains):
    """Safe: URL checked against allowlist."""
    from urllib.parse import urlparse

    parsed = urlparse(user_url)
    # SAFE: Allowlist validation
    if parsed.netloc not in allowed_domains:
        raise ValueError(f"Domain not allowed: {parsed.netloc}")

    return requests.get(user_url)


def safe_internal_url_blocked(url):
    """Safe: internal URLs blocked."""
    from urllib.parse import urlparse
    import ipaddress

    parsed = urlparse(url)
    hostname = parsed.hostname

    # SAFE: Block internal addresses
    try:
        ip = ipaddress.ip_address(hostname)
        if ip.is_private or ip.is_loopback or ip.is_reserved:
            raise ValueError("Internal addresses not allowed")
    except ValueError:
        pass  # Not an IP, allow hostname

    return requests.get(url)


def safe_hardcoded_url():
    """Safe: hardcoded URL only."""
    # SAFE: No user input
    return requests.get("https://api.example.com/status")
