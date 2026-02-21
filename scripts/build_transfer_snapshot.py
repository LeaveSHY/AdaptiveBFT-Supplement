#!/usr/bin/env python3
"""Build transfer-diagnostics markdown snapshot from bundle transfer logs."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict


@dataclass(frozen=True)
class Metrics:
    states: str
    distinct: str
    diameter: str
    wall: str
    result: str


def parse_tlc_log(log_path: Path) -> Metrics:
    text = log_path.read_text(encoding="utf-8", errors="replace")

    m = re.findall(
        r"^([0-9,]+)\s+states generated,\s+([0-9,]+)\s+distinct states found(?:,.*)?\.?$",
        text,
        re.MULTILINE,
    )
    d = re.findall(
        r"^The depth of the complete state graph search is\s+([0-9]+)\.$",
        text,
        re.MULTILINE,
    )
    w = re.findall(r"^Finished in\s+(.+?)\s+at\b", text, re.MULTILINE)

    return Metrics(
        states=m[-1][0] if m else "-",
        distinct=m[-1][1] if m else "-",
        diameter=d[-1] if d else "-",
        wall=w[-1].strip() if w else "-",
        result="Pass" if "No error has been found." in text else "Fail",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--bundle-stamp", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    models_dir = root / "models"
    out_path = args.out.resolve()
    stamp = args.bundle_stamp

    rows: Dict[str, Metrics] = {
        "baseline": parse_tlc_log(models_dir / f"_bundle_{stamp}_transfer_baseline.out"),
        "mv3": parse_tlc_log(models_dir / f"_bundle_{stamp}_transfer_mv3.out"),
        "mv4": parse_tlc_log(models_dir / f"_bundle_{stamp}_transfer_mv4.out"),
    }

    lines = [
        f"# Transfer Diagnostics Snapshot ({stamp})",
        "",
        "Commands executed:",
        "",
        "- `make test-transfer`",
        "- `make test-transfer-mv3`",
        "- `make test-transfer-mv4`",
        "",
        "Model:",
        "",
        "- `models/MC_RefinementTransfer.tla`",
        "- properties: `InitProjectionChecked`, `StepProjectionChecked`, `StepBoxProjectionChecked`, `SpecProjectionChecked`, `SpecToAbstractSpecChecked`",
        "",
        "Results:",
        "",
        "| Profile | States generated | Distinct states | Diameter | Wall-clock | TLC result |",
        "|---|---:|---:|---:|---:|---|",
        f"| baseline (`MaxView=2`) | {rows['baseline'].states} | {rows['baseline'].distinct} | {rows['baseline'].diameter} | {rows['baseline'].wall} | {rows['baseline'].result} |",
        f"| `MaxView=3` | {rows['mv3'].states} | {rows['mv3'].distinct} | {rows['mv3'].diameter} | {rows['mv3'].wall} | {rows['mv3'].result} |",
        f"| `MaxView=4` | {rows['mv4'].states} | {rows['mv4'].distinct} | {rows['mv4'].diameter} | {rows['mv4'].wall} | {rows['mv4'].result} |",
        "",
        "Constraint envelope:",
        "",
        '- `TransferConstraint == /\\ st.schedulerState = "Monitor"`',
        '- `/\\ st.networkCondition = "Stable"`',
        "- `/\\ st.view = 0`",
        "- `/\\ Len(st.chain) = 0`",
        "",
        "Interpretation:",
        "",
        "- This is bounded, constraint-scoped transfer diagnostics.",
        "- It supports concrete-step to abstract-step/stutter alignment claims.",
        "- It is not a closed unbounded refinement theorem by itself.",
        "",
    ]
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
