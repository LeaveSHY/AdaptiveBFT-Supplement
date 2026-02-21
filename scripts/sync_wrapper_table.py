#!/usr/bin/env python3
"""Synchronize wrapper-projection rows in docs/verification_tables.tex."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WRAPPER_MD = ROOT / "docs" / "results" / "wrapper_projection_latest.md"
TEX = ROOT / "docs" / "verification_tables.tex"


def parse_wrapper_snapshot() -> dict[tuple[str, str], tuple[str, str, str, str]]:
    if not WRAPPER_MD.exists():
        raise FileNotFoundError(f"Missing wrapper snapshot: {WRAPPER_MD}")

    section = ""
    out: dict[tuple[str, str], tuple[str, str, str, str]] = {}
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|"
    )

    for raw in WRAPPER_MD.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("## baseline"):
            section = "baseline"
            continue
        if line.startswith("## mv4"):
            section = "mv4"
            continue

        m = row_re.match(line)
        if not m or not section:
            continue

        if m.group("result") != "PASS":
            raise RuntimeError(
                f"Wrapper projection snapshot contains non-PASS row: {line}"
            )

        model = m.group("model")
        states = f"{int(m.group('states')):,}"
        distinct = f"{int(m.group('distinct')):,}"
        diam = m.group("diam")
        wall = m.group("wall").strip()
        out[(section, model)] = (states, distinct, diam, wall)

    required = {
        ("baseline", "MC_AdaptiveAttack"),
        ("baseline", "MC_LivenessAPS"),
        ("baseline", "MC_LivenessAPSAttack"),
        ("mv4", "MC_AdaptiveAttack"),
        ("mv4", "MC_LivenessAPS"),
        ("mv4", "MC_LivenessAPSAttack"),
    }
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"Wrapper snapshot is missing rows: {missing}")
    return out


def parse_wrapper_date() -> str:
    text = WRAPPER_MD.read_text(encoding="utf-8")
    m = re.search(r"^# Wrapper Projection Snapshot \(([0-9]{8})-[0-9]{6}\)\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing stamped heading date in {WRAPPER_MD}")
    raw = m.group(1)
    return f"{raw[0:4]}-{raw[4:6]}-{raw[6:8]}"


def sync_tex(rows: dict[tuple[str, str], tuple[str, str, str, str]]) -> int:
    text = TEX.read_text(encoding="utf-8")
    changed = 0

    row_re = re.compile(
        r"^(?P<indent>\s*)(?P<profile>baseline|\\texttt\{MaxView=4\})\s*&\s*"
        r"(?P<model>MC\\_[A-Za-z0-9]+)\s*&\s*"
        r"(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*"
        r"(?P<wall>[^&]+?)\s*&\s*Pass\s*&\s*(?P<props>[^\\]+)\\\\\s*$",
        re.MULTILINE,
    )

    def repl(m: re.Match[str]) -> str:
        nonlocal changed
        profile_token = m.group("profile")
        profile = "baseline" if profile_token == "baseline" else "mv4"
        model = m.group("model").replace("\\_", "_")
        key = (profile, model)

        if key not in rows:
            return m.group(0)

        states, distinct, diam, wall = rows[key]
        existing = (
            m.group("states"),
            m.group("distinct"),
            m.group("diam"),
            m.group("wall").strip(),
        )
        desired = (states, distinct, diam, wall)
        if existing != desired:
            changed += 1

        return (
            f"{m.group('indent')}{profile_token} & {m.group('model')} & "
            f"{states} & {distinct} & {diam} & {wall} & Pass & "
            f"{m.group('props').strip()} \\\\"
        )

    updated = row_re.sub(repl, text)
    wrapper_date = parse_wrapper_date()
    updated2, n_note = re.subn(
        r"(\\item Snapshot source: \\texttt\{make wrapper-projection\} \(latest artifact:\s*\\texttt\{docs/results/wrapper\\_projection\\_latest\.md\}, executed on )([0-9]{4}-[0-9]{2}-[0-9]{2})(\)\.)",
        rf"\g<1>{wrapper_date}\g<3>",
        updated,
        flags=re.MULTILINE,
    )
    if n_note != 1:
        raise RuntimeError(f"expected exactly one wrapper date note in {TEX}, got {n_note}")
    if updated2 != text:
        changed += 1
    updated = updated2
    if changed:
        TEX.write_text(updated, encoding="utf-8")
    return changed


def main() -> int:
    rows = parse_wrapper_snapshot()
    changed = sync_tex(rows)
    if changed:
        print(f"Updated wrapper-projection table rows: {changed}")
    else:
        print("Wrapper-projection table already synchronized.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
