#!/usr/bin/env python3
"""Enforce explicit tracking of unproved top-level theorem declarations."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Iterable


THEOREM_RE = re.compile(r"^\s*THEOREM\s+([A-Za-z0-9_]+)\b")
PROOF_RE = re.compile(r"^\s*PROOF\b")
OBVIOUS_RE = re.compile(r"^\s*OBVIOUS\b")
MODULE_END_RE = re.compile(r"^\s*=+\s*$")
MODULE_HEADER_RE = re.compile(r"^\s*-+\s*MODULE\b")


ALLOWED_UNPROVED = set()


def iter_toplevel_modules(spec_dir: Path) -> Iterable[Path]:
    for path in sorted(spec_dir.glob("AdaptiveBFT*.tla")):
        if path.is_file():
            yield path


def theorem_coverage(path: Path) -> tuple[set[str], set[str]]:
    text = path.read_text(encoding="utf-8", errors="replace").splitlines()
    proved: set[str] = set()
    unproved: set[str] = set()
    i = 0
    while i < len(text):
        m = THEOREM_RE.match(text[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        key = f"{path.name}:{name}"
        j = i + 1
        has_proof = False
        while j < len(text):
            if THEOREM_RE.match(text[j]) or MODULE_END_RE.match(text[j]) or MODULE_HEADER_RE.match(text[j]):
                break
            if PROOF_RE.match(text[j]) or OBVIOUS_RE.match(text[j]):
                has_proof = True
                break
            j += 1
        if has_proof:
            proved.add(key)
        else:
            unproved.add(key)
        i = j
    return proved, unproved


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    spec_dir = root / "specifications"

    proved_all: set[str] = set()
    unproved_all: set[str] = set()
    for module in iter_toplevel_modules(spec_dir):
        proved, unproved = theorem_coverage(module)
        proved_all |= proved
        unproved_all |= unproved

    unexpected = sorted(unproved_all - ALLOWED_UNPROVED)
    stale_allowlist = sorted(ALLOWED_UNPROVED - unproved_all)

    if unexpected:
        print("ERROR: found new unproved theorem declarations not in allowlist:")
        for item in unexpected:
            print(f"  - {item}")
    if stale_allowlist:
        print("ERROR: allowlist contains entries that are now proved/removed:")
        for item in stale_allowlist:
            print(f"  - {item}")

    print(f"Theorem coverage summary: proved={len(proved_all)}, allowlisted_unproved={len(unproved_all)}")
    if not unexpected and not stale_allowlist:
        print("Theorem coverage check: PASS")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
