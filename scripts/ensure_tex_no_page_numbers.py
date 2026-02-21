#!/usr/bin/env python3
"""Ensure TLATeX-generated documents suppress page numbers.

Usage:
  python scripts/ensure_tex_no_page_numbers.py <path-to-tex>
"""

from __future__ import annotations

import argparse
from pathlib import Path


MARKER = "\\pagestyle{empty}"


def patch_tex(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if MARKER in text:
        return False

    token = "\\begin{document}"
    replacement = (
        "\\begin{document}\n"
        "\\pagestyle{empty}\n"
        "\\thispagestyle{empty}"
    )
    if token not in text:
        raise ValueError(f"{path} does not contain {token}")

    text = text.replace(token, replacement, 1)
    path.write_text(text, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("tex", type=Path)
    args = parser.parse_args()

    tex_path = args.tex
    if not tex_path.exists():
        raise FileNotFoundError(f"{tex_path} not found")

    changed = patch_tex(tex_path)
    print(f"{tex_path}: {'patched' if changed else 'already-patched'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

