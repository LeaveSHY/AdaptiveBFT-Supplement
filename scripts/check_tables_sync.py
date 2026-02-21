#!/usr/bin/env python3
"""Check consistency between matrix CSV and paper-facing tables (README + LaTeX)."""

from __future__ import annotations

import csv
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Optional, Tuple

ROOT = Path(__file__).resolve().parents[1]
RESULTS_DIR = ROOT / "docs" / "results"
README = ROOT / "README.md"
TEX = ROOT / "docs" / "verification_tables.tex"

PROFILE_ORDER = ["baseline", "mv3", "mv4"]
MODEL_ORDER = ["MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack"]
MODEL_MAP = {
    "attack": "MC_AdaptiveAttack",
    "aps": "MC_LivenessAPS",
    "joint": "MC_LivenessAPSAttack",
}


@dataclass(frozen=True)
class Metrics:
    states: int
    distinct: int
    diameter: int
    wall_seconds: Optional[int]


def parse_int(text: str) -> int:
    return int(text.replace(",", "").strip())


def parse_duration_seconds(text: str) -> Optional[int]:
    s = text.strip().lower()
    s = s.replace('"', "")
    s = s.replace("\\", "")
    s = s.replace("$", "")
    s = s.replace(" ", "")
    s = s.replace("<1s", "0s")

    if not s:
        return None

    patterns = [
        (r"^(\d+)h(\d+)min$", lambda m: int(m.group(1)) * 3600 + int(m.group(2)) * 60),
        (r"^(\d+)h(\d+)m$", lambda m: int(m.group(1)) * 3600 + int(m.group(2)) * 60),
        (r"^(\d+)min(\d+)s$", lambda m: int(m.group(1)) * 60 + int(m.group(2))),
        (r"^(\d+)m(\d+)s$", lambda m: int(m.group(1)) * 60 + int(m.group(2))),
        (r"^(\d+)s$", lambda m: int(m.group(1))),
    ]

    for pat, fn in patterns:
        m = re.match(pat, s)
        if m:
            return fn(m)
    return None


def latest_matrix_csv() -> Path:
    strict = re.compile(r"^tlc_matrix_\d{8}-\d{6}\.csv$")
    files = sorted(p for p in RESULTS_DIR.glob("tlc_matrix_*.csv") if strict.match(p.name))
    if not files:
        raise FileNotFoundError(f"No matrix CSV found under {RESULTS_DIR}")
    return files[-1]


def load_expected(csv_path: Path) -> Dict[Tuple[str, str], Metrics]:
    out: Dict[Tuple[str, str], Metrics] = {}
    with csv_path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if not row.get("states_generated", "").strip():
                continue
            profile = row["profile"].strip()
            model = MODEL_MAP[row["model"].strip()]
            out[(profile, model)] = Metrics(
                states=parse_int(row["states_generated"]),
                distinct=parse_int(row["distinct_states"]),
                diameter=parse_int(row["diameter"]),
                wall_seconds=parse_duration_seconds(row["wall_clock"]),
            )
    return out


def parse_readme() -> Dict[Tuple[str, str], Metrics]:
    profile = None
    out: Dict[Tuple[str, str], Metrics] = {}
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|[^|]*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|"
    )

    for line in README.read_text(encoding="utf-8").splitlines():
        if line.startswith("Baseline (`MaxView=2`"):
            profile = "baseline"
            continue
        if line.startswith("Deeper profile (`MaxView=3`"):
            profile = "mv3"
            continue
        if line.startswith("Strengthened profile (`MaxView=4`"):
            profile = "mv4"
            continue
        if line.startswith("MaxView=5 deepened full-suite snapshot"):
            profile = None
            continue

        m = row_re.match(line)
        if m and profile:
            model = m.group("model")
            out[(profile, model)] = Metrics(
                states=parse_int(m.group("states")),
                distinct=parse_int(m.group("distinct")),
                diameter=parse_int(m.group("diam")),
                wall_seconds=parse_duration_seconds(m.group("wall")),
            )
    return out


def parse_tex() -> Dict[Tuple[str, str], Metrics]:
    profile = None
    out: Dict[Tuple[str, str], Metrics] = {}
    row_re = re.compile(
        r"^MC\\_(?P<model>[A-Za-z0-9]+)\s*&\s*(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&"
    )

    for line in TEX.read_text(encoding="utf-8").splitlines():
        if "baseline profile" in line:
            profile = "baseline"
            continue
        if "MaxView=3" in line:
            profile = "mv3"
            continue
        if "MaxView=4" in line:
            profile = "mv4"
            continue
        if "MaxView=5" in line:
            profile = None
            continue

        m = row_re.match(line.strip())
        if m and profile:
            model = f"MC_{m.group('model')}"
            out[(profile, model)] = Metrics(
                states=parse_int(m.group("states")),
                distinct=parse_int(m.group("distinct")),
                diameter=parse_int(m.group("diam")),
                wall_seconds=parse_duration_seconds(m.group("wall")),
            )
    return out


def compare(source: str, observed: Dict[Tuple[str, str], Metrics], expected: Dict[Tuple[str, str], Metrics]) -> int:
    errors = 0
    for profile in PROFILE_ORDER:
        for model in MODEL_ORDER:
            key = (profile, model)
            if key not in expected:
                print(f"[ERROR] expected missing in CSV for {key}")
                errors += 1
                continue
            if key not in observed:
                print(f"[ERROR] {source} missing row for {key}")
                errors += 1
                continue

            exp = expected[key]
            got = observed[key]
            if exp.states != got.states:
                print(f"[ERROR] {source} {key} states mismatch: expected {exp.states}, got {got.states}")
                errors += 1
            if exp.distinct != got.distinct:
                print(f"[ERROR] {source} {key} distinct mismatch: expected {exp.distinct}, got {got.distinct}")
                errors += 1
            if exp.diameter != got.diameter:
                print(f"[ERROR] {source} {key} diameter mismatch: expected {exp.diameter}, got {got.diameter}")
                errors += 1

            if exp.wall_seconds is not None and got.wall_seconds is not None:
                # Runtime can vary between reruns; allow small drift while still catching stale tables.
                if abs(exp.wall_seconds - got.wall_seconds) > 300:
                    print(
                        f"[ERROR] {source} {key} wall-clock drift too large: expected {exp.wall_seconds}s, got {got.wall_seconds}s"
                    )
                    errors += 1

    return errors


def main() -> int:
    csv_path = latest_matrix_csv()
    expected = load_expected(csv_path)
    readme_rows = parse_readme()
    tex_rows = parse_tex()

    errors = 0
    errors += compare("README", readme_rows, expected)
    errors += compare("verification_tables.tex", tex_rows, expected)

    if errors:
        print(f"\nFAILED: {errors} mismatch(es). Source CSV: {csv_path}")
        return 1

    print(f"OK: README and verification tables are synchronized with {csv_path.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
