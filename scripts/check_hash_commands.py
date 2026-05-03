#!/usr/bin/env python3
"""Fail if Lean files contain accidental interactive `#` commands."""

import re
import subprocess
import sys
from pathlib import Path


ALLOWED = {
    ("FermatsLastTheorem.lean", 30, "#print axioms PNat.pow_add_pow_ne_pow"),
}
COMMAND_RE = re.compile(r"(?<![`A-Za-z0-9_'])#([A-Za-z_][A-Za-z0-9_']*)\b")


def root() -> Path:
    out = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True)
    return Path(out.strip())


def lean_files(repo: Path) -> list[Path]:
    files: set[Path] = set()
    for args in ([], ["--others", "--exclude-standard"]):
        out = subprocess.check_output(
            ["git", "ls-files", "--full-name", *args, "*.lean"],
            cwd=repo,
            text=True,
        )
        files.update(Path(line) for line in out.splitlines())
    return sorted(files)


def without_comments_and_strings(text: str) -> str:
    chars = list(text)
    i = 0
    block_comment = 0
    string = False

    while i < len(chars):
        c = chars[i]
        nxt = chars[i + 1] if i + 1 < len(chars) else ""

        if string:
            if c == "\\" and i + 1 < len(chars):
                chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
                continue
            if c == '"':
                string = False
            if c != "\n":
                chars[i] = " "
            i += 1
            continue

        if block_comment:
            if c == "/" and nxt == "-":
                chars[i] = chars[i + 1] = " "
                block_comment += 1
                i += 2
                continue
            if c == "-" and nxt == "/":
                chars[i] = chars[i + 1] = " "
                block_comment -= 1
                i += 2
                continue
            if c != "\n":
                chars[i] = " "
            i += 1
            continue

        if c == "-" and nxt == "-":
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
        elif c == "/" and nxt == "-":
            chars[i] = chars[i + 1] = " "
            block_comment = 1
            i += 2
        elif c == '"':
            chars[i] = " "
            string = True
            i += 1
        else:
            i += 1

    return "".join(chars)


def normalized(line: str) -> str:
    return " ".join(line.split())


def unexpected_commands(path: Path, text: str) -> list[str]:
    clean = without_comments_and_strings(text)
    original = text.splitlines()
    errors = []
    for number, line in enumerate(clean.splitlines(), start=1):
        for match in COMMAND_RE.finditer(line):
            command = "#" + match.group(1)
            source = normalized(original[number - 1])
            if command == "#adaptation_note" or (path.as_posix(), number, source) in ALLOWED:
                continue
            errors.append(f"{path}:{number}: unexpected `{command}` command")
    return errors


def main() -> int:
    repo = root()
    errors = []
    for path in lean_files(repo):
        errors.extend(unexpected_commands(path, (repo / path).read_text(encoding="utf-8")))

    if errors:
        print("Unexpected Lean `#` commands found:")
        print("\n".join(errors))
        print("\nRemove debugging commands such as `#check`, `#eval`, `#lint`, and `#print`.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
