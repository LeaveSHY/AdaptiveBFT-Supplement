#!/usr/bin/env python3
"""Build a compact release-status dashboard from latest verification artifacts."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Tuple


@dataclass(frozen=True)
class Row:
    name: str
    status: str
    detail: str


TABLE_ROW_RE = re.compile(r"^\|\s*`?(?P<name>[^`|]+)`?\s*\|\s*(?P<body>.+)\|\s*$")


def parse_bundle(bundle: Path) -> Tuple[List[Row], bool]:
    rows: List[Row] = []
    if not bundle.exists():
        return rows, False
    for line in bundle.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.startswith("|"):
            continue
        parts = [p.strip() for p in line.strip().strip("|").split("|")]
        if len(parts) < 5 or parts[0] in {"Step", "---"}:
            continue
        step, _cmd, status, duration, _log = parts[:5]
        rows.append(Row(name=step, status=status, detail=duration))
    all_pass = bool(rows) and all(r.status == "PASS" for r in rows)
    return rows, all_pass


def parse_model_table(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    for line in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or "Model" in line:
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 6:
            continue
        model = parts[0].strip("`")
        wall = parts[4]
        result = parts[5]
        rows.append(Row(name=model, status=result, detail=wall))
    return rows


def parse_proof_table(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    for line in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or "Module" in line:
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 5:
            continue
        module = parts[0].strip("`")
        backend = parts[1]
        status = parts[2]
        obligations = parts[3]
        rows.append(Row(name=module, status=status, detail=f"{backend}, obligations={obligations}"))
    return rows


def parse_blockers_table(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    for line in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Theorem |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 3:
            continue
        theorem = parts[0].strip("`")
        loc = parts[1].strip("`")
        status = parts[2]
        rows.append(Row(name=theorem, status=status, detail=loc))
    return rows


def parse_closure_attempts(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    for line in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Strategy |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 6:
            continue
        strategy = parts[0].strip("`")
        status = parts[1]
        detail = f"exit={parts[2]}, duration={parts[3]}"
        rows.append(Row(name=strategy, status=status, detail=detail))
    return rows


def parse_failure_taxonomy(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    in_grouped = False
    for raw in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line == "## Grouped Goal Signatures":
            in_grouped = True
            continue
        if in_grouped and line.startswith("## "):
            break
        if not in_grouped:
            continue
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Goal Signature |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 3:
            continue
        goal_sig, strategies, hits = parts[:3]
        rows.append(Row(name=goal_sig, status=hits, detail=strategies))
    return rows


def parse_closure_trend(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    in_agg = False
    for raw in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line == "## Strategy Aggregates":
            in_agg = True
            continue
        if in_agg and line.startswith("## "):
            break
        if not in_agg:
            continue
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Strategy |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 6:
            continue
        strategy = parts[0].strip("`")
        runs = parts[1]
        passed = parts[2]
        failed = parts[3]
        rows.append(Row(name=strategy, status=f"runs={runs}", detail=f"pass={passed}, fail={failed}"))
    return rows


def parse_goalpack(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    in_ranked = False
    for raw in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line == "## Ranked Unproved Goals":
            in_ranked = True
            continue
        if in_ranked and line.startswith("## "):
            break
        if not in_ranked:
            continue
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Rank |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 5:
            continue
        rank = parts[0]
        goal_line = parts[1]
        hits = parts[2]
        goal_formula = parts[4]
        rows.append(
            Row(
                name=f"rank={rank}, line={goal_line}",
                status=f"hits={hits}",
                detail=goal_formula,
            )
        )
    return rows


def parse_concrete_probe(md_path: Path) -> List[Row]:
    rows: List[Row] = []
    if not md_path.exists():
        return rows
    for line in md_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Module |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 8:
            continue
        module = parts[0].strip("`")
        status = parts[1]
        if len(parts) >= 9:
            timeout_val = parts[2]
            duration = parts[3]
            proved = parts[5]
            failed = parts[6]
            detail = f"timeout={timeout_val}, {duration}, proved={proved}, failed={failed}"
        else:
            duration = parts[2]
            proved = parts[4]
            failed = parts[5]
            detail = f"{duration}, proved={proved}, failed={failed}"
        rows.append(
            Row(
                name=module,
                status=status,
                detail=detail,
            )
        )
    return rows


def write_status(
    out_path: Path,
    bundle_rows: List[Row],
    bundle_all_pass: bool,
    mv5_rows: List[Row],
    n7lite_full_rows: List[Row],
    proof_rows: List[Row],
    concrete_probe_rows: List[Row],
    blocker_rows: List[Row],
    closure_rows: List[Row],
    taxonomy_rows: List[Row],
    trend_rows: List[Row],
    goalpack_rows: List[Row],
    campaign_path: Path,
    closure_path: Path,
    taxonomy_path: Path,
    trend_path: Path,
    goalpack_path: Path,
) -> None:
    now = datetime.now(timezone.utc).astimezone()
    lines: List[str] = []
    lines.append("# Release Status Dashboard")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append("- scope: bounded TLC evidence + assumption-explicit theorem track")
    lines.append("- claim boundary: not a closed full-concrete unbounded proof")
    lines.append("")

    lines.append("## Strong-Claim Bundle")
    lines.append("")
    lines.append(f"- overall: {'PASS' if bundle_all_pass else 'FAIL'}")
    lines.append("")
    lines.append("| Step | Status | Duration |")
    lines.append("|---|---|---:|")
    if bundle_rows:
        for row in bundle_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (missing bundle summary) | FAIL | - |")
    lines.append("")

    lines.append("## MaxView=5 Full Suite")
    lines.append("")
    lines.append("| Model | Result | Wall-clock |")
    lines.append("|---|---|---:|")
    if mv5_rows:
        for row in mv5_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (missing mv5 suite snapshot) | FAIL | - |")
    lines.append("")

    lines.append("## n=7 Quick Full-Suite (n7lite)")
    lines.append("")
    lines.append("| Model | Result | Wall-clock |")
    lines.append("|---|---|---:|")
    if n7lite_full_rows:
        for row in n7lite_full_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (optional snapshot missing) | - | run `MODE_TIMEOUT_SEC=900 make scale-n7lite-full` |")
    lines.append("")

    lines.append("## Proof Track")
    lines.append("")
    lines.append("| Module | Status | Detail |")
    lines.append("|---|---|---|")
    if proof_rows:
        for row in proof_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (missing proof snapshot) | FAIL | - |")
    lines.append("")

    lines.append("## Concrete TLAPS Probe")
    lines.append("")
    lines.append("| Module | Status | Detail |")
    lines.append("|---|---|---|")
    if concrete_probe_rows:
        for row in concrete_probe_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (missing concrete probe) | - | run `make concrete-tlaps-probe` |")
    lines.append("")

    lines.append("## Open Theorem Blockers")
    lines.append("")
    lines.append("| Theorem | Status | Location |")
    lines.append("|---|---|---|")
    if blocker_rows:
        for row in blocker_rows:
            lines.append(f"| `{row.name}` | {row.status} | `{row.detail}` |")
    else:
        lines.append("| (none) | fully-closed | - |")
    lines.append("")

    lines.append("## Safety-Transfer Closure Attempts")
    lines.append("")
    lines.append("| Strategy | Status | Detail |")
    lines.append("|---|---|---|")
    if closure_rows:
        for row in closure_rows:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (no attempt artifact) | - | run `make closure-attempt-safety` |")
    lines.append("")

    lines.append("## Safety-Transfer Failure Taxonomy")
    lines.append("")
    lines.append("| Goal Signature | Hits | Strategies |")
    lines.append("|---|---:|---|")
    if taxonomy_rows:
        for row in taxonomy_rows[:5]:
            sig = row.name.replace("|", "\\|")
            lines.append(f"| {sig} | {row.status} | {row.detail} |")
    else:
        lines.append("| (no taxonomy artifact) | 0 | run `make closure-failure-taxonomy` |")
    lines.append("")

    lines.append("## Safety-Transfer Closure Trend")
    lines.append("")
    lines.append("| Strategy | Runs | Pass/Fail |")
    lines.append("|---|---|---|")
    if trend_rows:
        for row in trend_rows[:5]:
            lines.append(f"| `{row.name}` | {row.status} | {row.detail} |")
    else:
        lines.append("| (no trend artifact) | - | run `make closure-trend` |")
    lines.append("")

    lines.append("## Safety-Transfer Goalpack")
    lines.append("")
    lines.append("| Goal | Hits | Formula |")
    lines.append("|---|---|---|")
    if goalpack_rows:
        for row in goalpack_rows[:5]:
            formula = row.detail.replace("|", "\\|")
            lines.append(f"| {row.name} | {row.status} | {formula} |")
    else:
        lines.append("| (no goalpack artifact) | - | run `make closure-attempt-safety` |")
    lines.append("")

    lines.append("## Linked Artifacts")
    lines.append("")
    lines.append("- `docs/results/strong_claim_bundle_latest.md`")
    lines.append("- `docs/results/mv5_suite_latest.md`")
    if (out_path.parent / "scale_n7lite_full_suite_latest.md").exists():
        lines.append("- `docs/results/scale_n7lite_full_suite_latest.md`")
    lines.append("- `docs/results/proof_snapshot_latest.md`")
    lines.append("- `docs/results/proof_blockers_latest.md`")
    if (out_path.parent / "concrete_tlaps_probe_latest.md").exists():
        lines.append("- `docs/results/concrete_tlaps_probe_latest.md`")
    if closure_path.exists():
        lines.append("- `docs/results/safety_transfer_closure_attempt_latest.md`")
    if taxonomy_path.exists():
        lines.append("- `docs/results/safety_transfer_failure_taxonomy_latest.md`")
    if trend_path.exists():
        lines.append("- `docs/results/safety_transfer_closure_trend_latest.md`")
    if goalpack_path.exists():
        lines.append("- `docs/results/safety_transfer_goalpack_latest.md`")
    if campaign_path.exists():
        lines.append("- `docs/results/campaign_snapshot_latest.md`")
    lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    results = root / "docs" / "results"
    bundle = results / "strong_claim_bundle_latest.md"
    mv5 = results / "mv5_suite_latest.md"
    n7lite_full = results / "scale_n7lite_full_suite_latest.md"
    proof = results / "proof_snapshot_latest.md"
    blockers = results / "proof_blockers_latest.md"
    closure = results / "safety_transfer_closure_attempt_latest.md"
    taxonomy = results / "safety_transfer_failure_taxonomy_latest.md"
    trend = results / "safety_transfer_closure_trend_latest.md"
    goalpack = results / "safety_transfer_goalpack_latest.md"
    campaign = results / "campaign_snapshot_latest.md"
    concrete_probe = results / "concrete_tlaps_probe_latest.md"

    bundle_rows, bundle_all_pass = parse_bundle(bundle)
    mv5_rows = parse_model_table(mv5)
    n7lite_full_rows = parse_model_table(n7lite_full)
    proof_rows = parse_proof_table(proof)
    concrete_probe_rows = parse_concrete_probe(concrete_probe)
    blocker_rows = parse_blockers_table(blockers)
    closure_rows = parse_closure_attempts(closure)
    taxonomy_rows = parse_failure_taxonomy(taxonomy)
    trend_rows = parse_closure_trend(trend)
    goalpack_rows = parse_goalpack(goalpack)

    write_status(
        out_path=args.out,
        bundle_rows=bundle_rows,
        bundle_all_pass=bundle_all_pass,
        mv5_rows=mv5_rows,
        n7lite_full_rows=n7lite_full_rows,
        proof_rows=proof_rows,
        concrete_probe_rows=concrete_probe_rows,
        blocker_rows=blocker_rows,
        closure_rows=closure_rows,
        taxonomy_rows=taxonomy_rows,
        trend_rows=trend_rows,
        goalpack_rows=goalpack_rows,
        campaign_path=campaign,
        closure_path=closure,
        taxonomy_path=taxonomy,
        trend_path=trend,
        goalpack_path=goalpack,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
