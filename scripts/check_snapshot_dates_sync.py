#!/usr/bin/env python3
"""Check that verification_tables snapshot-date notes match latest artifacts."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "docs" / "verification_tables.tex"

MV5_MD = ROOT / "docs" / "results" / "mv5_suite_latest.md"
N7_MD = ROOT / "docs" / "results" / "scale_n7_attack_latest.md"
N7LITE_MD = ROOT / "docs" / "results" / "scale_n7lite_suite_latest.md"
TRANSFER_MD = ROOT / "docs" / "results" / "transfer_snapshot_latest.md"
WRAPPER_MD = ROOT / "docs" / "results" / "wrapper_projection_latest.md"


def parse_iso_date(md: Path) -> str:
    text = md.read_text(encoding="utf-8")
    m = re.search(r"^- date:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})\b", text, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing ISO date line in {md}")
    return m.group(1)


def parse_stamp_date(md: Path, heading_pattern: str) -> str:
    text = md.read_text(encoding="utf-8")
    m = re.search(heading_pattern, text, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing stamped heading date in {md}")
    raw = m.group(1)
    return f"{raw[0:4]}-{raw[4:6]}-{raw[6:8]}"


def pick_date(tex: str, pattern: str, label: str) -> str:
    m = re.search(pattern, tex, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing note row for {label} in {TEX}")
    return m.group(1)


def main() -> int:
    tex = TEX.read_text(encoding="utf-8")

    expected = {
        "mv5": parse_iso_date(MV5_MD),
        "n7lite": parse_iso_date(N7LITE_MD),
        "n7": parse_iso_date(N7_MD),
        "transfer": parse_stamp_date(
            TRANSFER_MD, r"^# .*?\(([0-9]{8})-[0-9]{6}\)\s*$"
        ),
        "wrapper": parse_stamp_date(
            WRAPPER_MD, r"^# Wrapper Projection Snapshot \(([0-9]{8})-[0-9]{6}\)\s*$"
        ),
    }

    found = {
        "mv5": pick_date(
            tex,
            r"\\item Snapshot source: \\texttt\{make suite-mv5\} \(artifact: \\texttt\{docs/results/mv5\\_suite\\_latest\.md\}, executed on ([0-9]{4}-[0-9]{2}-[0-9]{2})\)\.",
            "mv5",
        ),
        "n7lite": pick_date(
            tex,
            r"\\item Snapshot source: \\texttt\{make scale-n7lite\} \(artifact: \\texttt\{docs/results/scale\\_n7lite\\_suite\\_latest\.md\}, executed on ([0-9]{4}-[0-9]{2}-[0-9]{2})\)\.",
            "n7lite",
        ),
        "n7": pick_date(
            tex,
            r"\\item Snapshot source: \\texttt\{make scale-n7\} \(artifact: \\texttt\{docs/results/scale\\_n7\\_attack\\_latest\.md\}, executed on ([0-9]{4}-[0-9]{2}-[0-9]{2})\)\.",
            "n7",
        ),
        "transfer": pick_date(
            tex,
            r"\\item Commands: \\texttt\{make test-transfer\}, \\texttt\{make test-transfer-mv3\}, \\texttt\{make test-transfer-mv4\} \(executed on ([0-9]{4}-[0-9]{2}-[0-9]{2})\)\.",
            "transfer",
        ),
        "wrapper": pick_date(
            tex,
            r"\\texttt\{docs/results/wrapper\\_projection\\_latest\.md\}, executed on ([0-9]{4}-[0-9]{2}-[0-9]{2})\)\.",
            "wrapper",
        ),
    }

    errors = 0
    for key in ("mv5", "n7lite", "n7", "transfer", "wrapper"):
        if expected[key] != found[key]:
            print(
                f"[ERROR] snapshot-date mismatch for {key}: "
                f"artifact={expected[key]} tex={found[key]}"
            )
            errors += 1

    if errors:
        print(f"\nFAILED: {errors} snapshot-date mismatch(es).")
        return 1

    print("OK: verification_tables snapshot dates are synchronized with latest artifacts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

