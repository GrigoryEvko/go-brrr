# Test fixtures for command injection detection
# Contains various command injection vulnerability patterns

import os
import subprocess


def vulnerable_os_system(user_input):
    """Vulnerable: os.system with user input."""
    # VULNERABLE: User input in shell command
    os.system("ls -la " + user_input)


def vulnerable_subprocess_shell(filename):
    """Vulnerable: subprocess with shell=True."""
    # VULNERABLE: shell=True with user input
    subprocess.call("cat " + filename, shell=True)


def vulnerable_os_popen(cmd):
    """Vulnerable: os.popen with user input."""
    # VULNERABLE: User controlled command
    result = os.popen("grep -r " + cmd)
    return result.read()


def vulnerable_subprocess_run_shell(user_cmd):
    """Vulnerable: subprocess.run with shell=True."""
    # VULNERABLE: User input reaches shell
    subprocess.run(f"echo {user_cmd}", shell=True)


def safe_subprocess_list(filename):
    """Safe: subprocess with argument list."""
    # SAFE: Arguments passed as list
    result = subprocess.run(["cat", filename], capture_output=True)
    return result.stdout


def safe_subprocess_no_shell(args):
    """Safe: subprocess without shell=True."""
    # SAFE: shell=False (default)
    result = subprocess.call(["ls", "-la", args])
    return result


def safe_constant_command():
    """Safe: no user input in command."""
    # SAFE: Hardcoded command
    os.system("date")
