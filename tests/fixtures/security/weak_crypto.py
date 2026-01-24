# Test fixtures for weak cryptography detection
# Contains various weak cryptography patterns

import hashlib
from Crypto.Cipher import DES, Blowfish, ARC4
from Crypto.PublicKey import RSA


def vulnerable_md5_hash(data):
    """Vulnerable: MD5 for password hashing."""
    # VULNERABLE: MD5 is cryptographically broken
    return hashlib.md5(data.encode()).hexdigest()


def vulnerable_sha1_hash(password):
    """Vulnerable: SHA1 for password hashing."""
    # VULNERABLE: SHA1 is cryptographically weak
    return hashlib.sha1(password.encode()).hexdigest()


def vulnerable_des_encryption(key, plaintext):
    """Vulnerable: DES encryption."""
    # VULNERABLE: DES has 56-bit key, easily broken
    cipher = DES.new(key, DES.MODE_ECB)
    return cipher.encrypt(plaintext)


def vulnerable_blowfish_small_key(plaintext):
    """Vulnerable: Blowfish with small key."""
    # VULNERABLE: 32-bit key is too small
    key = b'1234'
    cipher = Blowfish.new(key, Blowfish.MODE_ECB)
    return cipher.encrypt(plaintext)


def vulnerable_arc4_encryption(key, data):
    """Vulnerable: RC4/ARC4 stream cipher."""
    # VULNERABLE: RC4 has known biases
    cipher = ARC4.new(key)
    return cipher.encrypt(data)


def vulnerable_ecb_mode(key, plaintext):
    """Vulnerable: ECB mode encryption."""
    from Crypto.Cipher import AES
    # VULNERABLE: ECB mode reveals patterns
    cipher = AES.new(key, AES.MODE_ECB)
    return cipher.encrypt(plaintext)


def vulnerable_small_rsa_key():
    """Vulnerable: RSA with small key size."""
    # VULNERABLE: 512-bit RSA key is too small
    key = RSA.generate(512)
    return key


def safe_sha256_hash(data):
    """Safe: SHA-256 for general hashing."""
    # SAFE: SHA-256 is secure
    return hashlib.sha256(data.encode()).hexdigest()


def safe_sha512_hash(data):
    """Safe: SHA-512 for hashing."""
    # SAFE: SHA-512 is secure
    return hashlib.sha512(data.encode()).hexdigest()


def safe_aes_gcm(key, plaintext, nonce):
    """Safe: AES-GCM authenticated encryption."""
    from Crypto.Cipher import AES
    # SAFE: AES-GCM provides confidentiality and authenticity
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    return cipher.encrypt_and_digest(plaintext)


def safe_rsa_key():
    """Safe: RSA with proper key size."""
    # SAFE: 2048-bit RSA key
    key = RSA.generate(2048)
    return key
