#!/usr/bin/env python3
"""Validate submission-ready artifacts and package integrity."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import List
from zipfile import ZipFile


@dataclass(frozen=True)
class CheckRow:
    name: str
    status: str
    detail: str


REQUIRED_FILES = [
    "README.md",
    "docs/claim_boundary.md",
    "docs/proof_roadmap.md",
    "docs/assumption_to_evidence_map.md",
    "docs/reviewer_checklist.md",
    "docs/submission_guide.md",
    "docs/paper_claim_text.tex",
    "docs/formal_figures.tex",
    "docs/verification_tables.tex",
    "docs/results/release_status_latest.md",
    "docs/results/submission_rc_latest.md",
    "docs/results/submission_ready_latest.md",
    "docs/results/submission_artifact_manifest_latest.md",
    "docs/results/submission_bundle_latest.zip",
    "docs/results/strong_claim_bundle_latest.md",
    "docs/results/fastlane_release_latest.md",
    "docs/results/proof_snapshot_latest.md",
    "docs/results/concrete_tlaps_probe_latest.md",
    "docs/results/wrapper_projection_latest.md",
    "docs/results/mv5_suite_latest.md",
    "AdaptiveBFT_MainFlow.pdf",
    "AdaptiveBFT_Types.pdf",
    "modules/AVC_RVS.pdf",
    "modules/APS_Mempool.pdf",
    "AdaptiveBFT_Properties.pdf",
]

REQUIRED_IN_ZIP = [
    "README.md",
    "Makefile",
    "run.sh",
    "docs/claim_boundary.md",
    "docs/proof_roadmap.md",
    "docs/assumption_to_evidence_map.md",
    "docs/reviewer_checklist.md",
    "docs/submission_guide.md",
    "docs/paper_claim_text.tex",
    "docs/formal_figures.tex",
    "docs/verification_tables.tex",
    "docs/results/release_status_latest.md",
    "docs/results/submission_rc_latest.md",
    "docs/results/submission_ready_latest.md",
    "docs/results/submission_artifact_manifest_latest.md",
    "AdaptiveBFT_MainFlow.pdf",
    "AdaptiveBFT_Types.pdf",
    "modules/AVC_RVS.pdf",
    "modules/APS_Mempool.pdf",
    "AdaptiveBFT_Properties.pdf",
]


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def parse_value(text: str, key_prefix: str) -> str:
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(key_prefix):
            return s[len(key_prefix) :].strip()
    return ""


def parse_release_overall(text: str) -> str:
    m = re.search(r"- overall:\s*(PASS|FAIL)", text)
    return m.group(1) if m else "UNKNOWN"


def check_files(root: Path) -> CheckRow:
    missing = [p for p in REQUIRED_FILES if not (root / p).exists()]
    if missing:
        return CheckRow("required_files", "FAIL", f"missing={len(missing)}")
    return CheckRow("required_files", "PASS", f"count={len(REQUIRED_FILES)}")


def check_release_status(root: Path) -> CheckRow:
    text = read_text(root / "docs" / "results" / "release_status_latest.md")
    overall = parse_release_overall(text)
    return CheckRow("release_status_overall", "PASS" if overall == "PASS" else "FAIL", overall)


def check_submission_rc(root: Path) -> CheckRow:
    text = read_text(root / "docs" / "results" / "submission_rc_latest.md")
    status = parse_value(text, "- status:")
    ok = status.startswith("READY")
    return CheckRow("submission_rc_status", "PASS" if ok else "FAIL", status or "UNKNOWN")


def check_submission_ready(root: Path) -> CheckRow:
    text = read_text(root / "docs" / "results" / "submission_ready_latest.md")
    overall = parse_value(text, "- overall:")
    skip_gate = parse_value(text, "- skip_gate_strong:")
    skip_bundle = parse_value(text, "- skip_bundle:")
    ok = overall == "PASS"
    detail = f"overall={overall or 'UNKNOWN'}, skip_gate={skip_gate or '?'}, skip_bundle={skip_bundle or '?'}"
    return CheckRow("submission_ready", "PASS" if ok else "FAIL", detail)


def check_zip(root: Path) -> CheckRow:
    zip_path = root / "docs" / "results" / "submission_bundle_latest.zip"
    if not zip_path.exists():
        return CheckRow("submission_bundle_zip", "FAIL", "missing zip")
    try:
        with ZipFile(zip_path, "r") as zf:
            names = set(zf.namelist())
    except Exception as e:  # pragma: no cover
        return CheckRow("submission_bundle_zip", "FAIL", f"open_error={e}")
    missing = [p for p in REQUIRED_IN_ZIP if p not in names]
    if missing:
        return CheckRow("submission_bundle_zip", "FAIL", f"missing_entries={len(missing)}")
    return CheckRow("submission_bundle_zip", "PASS", f"entries_checked={len(REQUIRED_IN_ZIP)}")


def render(rows: List[CheckRow]) -> str:
    now = datetime.now(timezone.utc).astimezone()
    overall = "PASS" if all(r.status == "PASS" for r in rows) else "FAIL"
    out: List[str] = []
    out.append("# Submission Package Check")
    out.append("")
    out.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    out.append(f"- overall: {overall}")
    out.append("")
    out.append("| Check | Status | Detail |")
    out.append("|---|---|---|")
    for r in rows:
        out.append(f"| `{r.name}` | {r.status} | {r.detail} |")
    out.append("")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    rows = [
        check_files(root),
        check_release_status(root),
        check_submission_rc(root),
        check_submission_ready(root),
        check_zip(root),
    ]
    text = render(rows)
    args.out.write_text(text, encoding="utf-8")
    ok = all(r.status == "PASS" for r in rows)
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
