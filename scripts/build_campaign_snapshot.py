#!/usr/bin/env python3
"""Build a unified reviewer-facing campaign snapshot (matrix/transfer/wrapper/n7+n7lite)."""

from __future__ import annotations

import argparse
import csv
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple


@dataclass(frozen=True)
class Metrics:
    states: str
    distinct: str
    diameter: str
    wall: str
    result: str


def parse_tlc_log(log_path: Path) -> Metrics:
    text = log_path.read_text(encoding="utf-8", errors="replace")
    states = "-"
    distinct = "-"
    diameter = "-"
    wall = "-"
    result = "FAIL"

    m = re.findall(
        r"^([0-9,]+)\s+states generated,\s+([0-9,]+)\s+distinct states found(?:,.*)?\.?$",
        text,
        re.MULTILINE,
    )
    if m:
        states, distinct = m[-1]

    d = re.findall(
        r"^The depth of the complete state graph search is\s+([0-9]+)\.$",
        text,
        re.MULTILINE,
    )
    if d:
        diameter = d[-1]

    w = re.findall(r"^Finished in\s+(.+?)\s+at\b", text, re.MULTILINE)
    if w:
        wall = w[-1].strip()

    if "No error has been found." in text:
        result = "PASS"

    return Metrics(states=states, distinct=distinct, diameter=diameter, wall=wall, result=result)


def latest_matrix_csv(results_dir: Path) -> Path:
    full_pat = re.compile(r"^tlc_matrix_\d{8}-\d{6}\.csv$")
    full_files = sorted(
        p for p in results_dir.glob("tlc_matrix_*.csv") if full_pat.match(p.name)
    )
    if full_files:
        return full_files[-1]

    progress = results_dir / "tlc_matrix_progress_latest.csv"
    if progress.exists():
        return progress
    raise FileNotFoundError(f"no matrix CSV found under {results_dir}")


def parse_matrix(csv_path: Path) -> Dict[Tuple[str, str], Metrics]:
    out: Dict[Tuple[str, str], Metrics] = {}
    with csv_path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            key = (row["profile"].strip(), row["model"].strip())
            out[key] = Metrics(
                states=row["states_generated"].strip() or "-",
                distinct=row["distinct_states"].strip() or "-",
                diameter=row["diameter"].strip() or "-",
                wall=row["wall_clock"].strip().strip('"') or "-",
                result=row["result"].strip() or "FAIL",
            )
    return out


def parse_wrapper(wrapper_md: Path) -> List[Tuple[str, str, Metrics]]:
    rows: List[Tuple[str, str, Metrics]] = []
    section = ""
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|"
    )
    for raw in wrapper_md.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("## baseline"):
            section = "baseline"
            continue
        if line.startswith("## mv4"):
            section = "mv4"
            continue
        m = row_re.match(line)
        if m and section:
            rows.append(
                (
                    section,
                    m.group("model"),
                    Metrics(
                        states=m.group("states"),
                        distinct=m.group("distinct"),
                        diameter=m.group("diam"),
                        wall=m.group("wall").strip(),
                        result=m.group("result"),
                    ),
                )
            )
    return rows


def parse_n7(scale_md: Path) -> Metrics:
    text = scale_md.read_text(encoding="utf-8")

    def find_line(pattern: str) -> str:
        m = re.search(pattern, text, re.MULTILINE)
        return m.group(1).strip() if m else "-"

    return Metrics(
        states=find_line(r"^- states generated:\s*([0-9,]+)\s*$"),
        distinct=find_line(r"^- distinct states:\s*([0-9,]+)\s*$"),
        diameter=find_line(r"^- diameter:\s*([0-9]+)\s*$"),
        wall=find_line(r"^- wall-clock:\s*(.+)\s*$"),
        result=find_line(r"^- result:\s*(PASS|FAIL)\s*$"),
    )


def parse_n7lite(scale_md: Path) -> List[Tuple[str, Metrics]]:
    rows: List[Tuple[str, Metrics]] = []
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|$"
    )
    for raw in scale_md.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        rows.append(
            (
                m.group("model"),
                Metrics(
                    states=m.group("states"),
                    distinct=m.group("distinct"),
                    diameter=m.group("diam"),
                    wall=m.group("wall").strip(),
                    result=m.group("result"),
                ),
            )
        )
    return rows


def parse_md_model_table(md_path: Path) -> List[Tuple[str, Metrics]]:
    rows: List[Tuple[str, Metrics]] = []
    if not md_path.exists():
        return rows
    row_re = re.compile(
        r"^\|\s*`?(?P<model>MC_[^`|]+)`?\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL|TIMEOUT)\s*\|$"
    )
    for raw in md_path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        rows.append(
            (
                m.group("model").strip(),
                Metrics(
                    states=m.group("states").strip(),
                    distinct=m.group("distinct").strip(),
                    diameter=m.group("diam").strip(),
                    wall=m.group("wall").strip(),
                    result=m.group("result").strip(),
                ),
            )
        )
    return rows


def parse_proof_snapshot(proof_md: Path) -> List[Tuple[str, str, str, str]]:
    rows: List[Tuple[str, str, str, str]] = []
    if not proof_md.exists():
        return rows
    row_re = re.compile(
        r"^\|\s*`(?P<module>[^`]+)`\s*\|\s*(?P<backend>TLAPS|SANY)\s*\|\s*(?P<status>PASS|MISSING|NO_OBLIGATION_LINE)\s*\|\s*(?P<obl>[^|]+)\|\s*`(?P<evidence>[^`]+)`\s*\|$"
    )
    for raw in proof_md.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        rows.append(
            (
                m.group("module"),
                m.group("backend"),
                m.group("status"),
                m.group("obl").strip(),
            )
        )
    return rows


def parse_concrete_probe(probe_md: Path) -> List[Tuple[str, str, str, str]]:
    rows: List[Tuple[str, str, str, str]] = []
    if not probe_md.exists():
        return rows
    row_re = re.compile(
        r"^\|\s*`(?P<module>[^`]+)`\s*\|\s*(?P<status>PASS|FAIL|TIMEOUT|SKIP)\s*\|\s*(?P<duration>[^|]+)\|\s*(?P<exit>[^|]+)\|"
    )
    for raw in probe_md.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        rows.append(
            (
                m.group("module"),
                m.group("status"),
                m.group("duration").strip(),
                m.group("exit").strip(),
            )
        )
    return rows


def write_snapshot(
    out_path: Path,
    bundle_stamp: str,
    matrix_csv: Path,
    matrix: Dict[Tuple[str, str], Metrics],
    transfer_metrics: Dict[str, Metrics],
    wrapper_rows: List[Tuple[str, str, Metrics]],
    n7_metrics: Metrics,
    n7lite_rows: List[Tuple[str, Metrics]],
    mv5_rows: List[Tuple[str, Metrics]],
    proof_rows: List[Tuple[str, str, str, str]],
    concrete_probe_rows: List[Tuple[str, str, str, str]],
) -> None:
    lines: List[str] = []
    lines.append(f"# Unified Campaign Snapshot ({bundle_stamp})")
    lines.append("")
    lines.append("This snapshot consolidates matrix, transfer, wrapper, and n=7 scale evidence.")
    lines.append("")

    lines.append("## Matrix (latest CSV)")
    lines.append("")
    lines.append(f"- source: `{matrix_csv.relative_to(matrix_csv.parents[2]).as_posix()}`")
    lines.append("")
    lines.append("| Profile | Model | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---|---:|---:|---:|---:|---|")
    for profile in ("baseline", "mv3", "mv4"):
        for model in ("attack", "aps", "joint"):
            key = (profile, model)
            m = matrix.get(key, Metrics("-", "-", "-", "-", "FAIL"))
            lines.append(
                f"| {profile} | {model} | {m.states} | {m.distinct} | {m.diameter} | {m.wall} | {m.result} |"
            )
    lines.append("")

    lines.append("## Transfer (bundle run)")
    lines.append("")
    lines.append("| Profile | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---:|---:|---:|---:|---|")
    for profile in ("baseline", "mv3", "mv4"):
        m = transfer_metrics.get(profile, Metrics("-", "-", "-", "-", "FAIL"))
        lines.append(f"| {profile} | {m.states} | {m.distinct} | {m.diameter} | {m.wall} | {m.result} |")
    lines.append("")

    lines.append("## Wrapper Projection (latest snapshot)")
    lines.append("")
    lines.append("| Profile | Model | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---|---:|---:|---:|---:|---|")
    for profile, model, m in wrapper_rows:
        lines.append(
            f"| {profile} | {model} | {m.states} | {m.distinct} | {m.diameter} | {m.wall} | {m.result} |"
        )
    lines.append("")

    lines.append("## n=7 Scale Snapshot")
    lines.append("")
    lines.append("| Model | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---:|---:|---:|---:|---|")
    lines.append(
        f"| MC_AdaptiveAttack (n7) | {n7_metrics.states} | {n7_metrics.distinct} | {n7_metrics.diameter} | {n7_metrics.wall} | {n7_metrics.result} |"
    )
    lines.append("")
    lines.append("## n=7 Quick Scale Snapshot (n7lite)")
    lines.append("")
    lines.append("| Model | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---:|---:|---:|---:|---|")
    for model, m in n7lite_rows:
        lines.append(
            f"| {model} | {m.states} | {m.distinct} | {m.diameter} | {m.wall} | {m.result} |"
        )
    lines.append("")
    lines.append("## MaxView=5 Full-Suite Snapshot")
    lines.append("")
    lines.append("| Model | States | Distinct | Diameter | Wall-clock | Result |")
    lines.append("|---|---:|---:|---:|---:|---|")
    if mv5_rows:
        for model, m in mv5_rows:
            lines.append(
                f"| {model} | {m.states} | {m.distinct} | {m.diameter} | {m.wall} | {m.result} |"
            )
    else:
        lines.append("| (missing `mv5_suite_latest.md`) | - | - | - | - | FAIL |")
    lines.append("")
    lines.append("## Proof Track Snapshot (latest)")
    lines.append("")
    lines.append("| Module | Backend | Status | Obligations |")
    lines.append("|---|---|---|---:|")
    if proof_rows:
        for module, backend, status, obl in proof_rows:
            lines.append(f"| `{module}` | {backend} | {status} | {obl} |")
    else:
        lines.append("| (missing `proof_snapshot_latest.md`) | - | - | - |")
    lines.append("")
    lines.append("## Concrete TLAPS Probe (latest)")
    lines.append("")
    lines.append("| Module | Status | Duration | Exit |")
    lines.append("|---|---|---:|---:|")
    if concrete_probe_rows:
        for module, status, duration, exit_code in concrete_probe_rows:
            lines.append(f"| `{module}` | {status} | {duration} | {exit_code} |")
    else:
        lines.append("| (missing `concrete_tlaps_probe_latest.md`) | - | - | - |")
    lines.append("")
    lines.append("Interpretation: bounded model-checking evidence under explicit assumptions; not an unbounded closed theorem.")
    lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--bundle-stamp", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    results_dir = root / "docs" / "results"
    models_dir = root / "models"
    wrapper_md = results_dir / "wrapper_projection_latest.md"
    n7_md = results_dir / "scale_n7_attack_latest.md"
    n7lite_md = results_dir / "scale_n7lite_suite_latest.md"
    mv5_md = results_dir / "mv5_suite_latest.md"
    proof_md = results_dir / "proof_snapshot_latest.md"
    concrete_probe_md = results_dir / "concrete_tlaps_probe_latest.md"

    matrix_csv = latest_matrix_csv(results_dir)
    matrix = parse_matrix(matrix_csv)

    transfer_metrics = {
        "baseline": parse_tlc_log(models_dir / f"_bundle_{args.bundle_stamp}_transfer_baseline.out"),
        "mv3": parse_tlc_log(models_dir / f"_bundle_{args.bundle_stamp}_transfer_mv3.out"),
        "mv4": parse_tlc_log(models_dir / f"_bundle_{args.bundle_stamp}_transfer_mv4.out"),
    }

    wrapper_rows = parse_wrapper(wrapper_md)
    n7_metrics = parse_n7(n7_md)
    n7lite_rows = parse_n7lite(n7lite_md) if n7lite_md.exists() else []
    mv5_rows = parse_md_model_table(mv5_md)
    proof_rows = parse_proof_snapshot(proof_md)
    concrete_probe_rows = parse_concrete_probe(concrete_probe_md)

    write_snapshot(
        out_path=args.out,
        bundle_stamp=args.bundle_stamp,
        matrix_csv=matrix_csv,
        matrix=matrix,
        transfer_metrics=transfer_metrics,
        wrapper_rows=wrapper_rows,
        n7_metrics=n7_metrics,
        n7lite_rows=n7lite_rows,
        mv5_rows=mv5_rows,
        proof_rows=proof_rows,
        concrete_probe_rows=concrete_probe_rows,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
