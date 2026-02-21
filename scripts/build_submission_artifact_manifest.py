#!/usr/bin/env python3
"""Build a reviewer-facing submission artifact manifest with integrity hashes."""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Tuple


@dataclass(frozen=True)
class Artifact:
    path: str
    required: bool
    purpose: str


def sha256_short(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()[:16]


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def parse_line(text: str, prefix: str) -> str:
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(prefix):
            return s[len(prefix) :].strip()
    return ""


def parse_summary_signals(root: Path) -> Tuple[str, str, str]:
    release = read_text(root / "docs" / "results" / "release_status_latest.md")
    rc = read_text(root / "docs" / "results" / "submission_rc_latest.md")
    ready = read_text(root / "docs" / "results" / "submission_ready_latest.md")
    release_overall = parse_line(release, "- overall:")
    rc_status = parse_line(rc, "- status:")
    ready_overall = parse_line(ready, "- overall:")
    return release_overall or "UNKNOWN", rc_status or "UNKNOWN", ready_overall or "UNKNOWN"


def build_list() -> List[Artifact]:
    return [
        Artifact("README.md", True, "Top-level reproducibility entry point."),
        Artifact("docs/claim_boundary.md", True, "Normative claim boundary."),
        Artifact("docs/proof_roadmap.md", True, "Proof-obligation roadmap."),
        Artifact("docs/assumption_to_evidence_map.md", True, "Assumption-to-evidence traceability."),
        Artifact("docs/reviewer_checklist.md", True, "Reviewer challenge and rebuttal checklist."),
        Artifact("docs/submission_guide.md", True, "Submission handoff and upload checklist."),
        Artifact("docs/paper_claim_text.tex", True, "Safe claim text snippet for paper."),
        Artifact("docs/formal_figures.tex", True, "Formal specification appendix section."),
        Artifact("docs/verification_tables.tex", True, "Verification settings/results tables."),
        Artifact("docs/results/release_status_latest.md", True, "Release dashboard."),
        Artifact("docs/results/submission_rc_latest.md", True, "Submission RC summary."),
        Artifact("docs/results/submission_ready_latest.md", True, "One-command campaign summary."),
        Artifact("docs/results/strong_claim_bundle_latest.md", True, "Bundle campaign summary."),
        Artifact("docs/results/fastlane_release_latest.md", True, "Fastlane campaign summary."),
        Artifact("docs/results/proof_snapshot_latest.md", True, "Theorem-track machine-check summary."),
        Artifact("docs/results/concrete_tlaps_probe_latest.md", True, "Concrete TLAPS diagnostics."),
        Artifact("docs/results/wrapper_projection_latest.md", True, "Wrapper transfer/property checks."),
        Artifact("docs/results/mv5_suite_latest.md", True, "Deep bounded model-checking snapshot."),
        Artifact("AdaptiveBFT_MainFlow.pdf", True, "Appendix figure: main flow."),
        Artifact("AdaptiveBFT_Types.pdf", True, "Appendix figure: type system."),
        Artifact("modules/AVC_RVS.pdf", True, "Appendix figure: AVC+RVS support."),
        Artifact("modules/APS_Mempool.pdf", True, "Appendix figure: APS+mempool support."),
        Artifact("AdaptiveBFT_Properties.pdf", True, "Appendix figure: correctness properties."),
        Artifact("docs/results/scale_n7_attack_latest.md", False, "Optional scale sanity snapshot."),
        Artifact("docs/results/scale_n7lite_suite_latest.md", False, "Optional quick scale snapshot."),
        Artifact("docs/results/scale_n7lite_full_suite_latest.md", False, "Optional quick full-suite scale snapshot."),
    ]


def render(root: Path, artifacts: List[Artifact]) -> str:
    now = datetime.now(timezone.utc).astimezone()
    release_overall, rc_status, ready_overall = parse_summary_signals(root)
    required_missing = 0

    lines: List[str] = []
    lines.append("# Submission Artifact Manifest")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append("- purpose: upload/review integrity manifest for submission package")
    lines.append(f"- release_overall: {release_overall}")
    lines.append(f"- submission_rc_status: {rc_status}")
    lines.append(f"- submission_ready_overall: {ready_overall}")
    lines.append("")

    lines.append("| Artifact | Required | Exists | Size (KB) | SHA256 (16) | Purpose |")
    lines.append("|---|---|---|---:|---|---|")
    for a in artifacts:
        p = root / a.path
        exists = p.exists()
        if a.required and not exists:
            required_missing += 1
        size_kb = f"{(p.stat().st_size / 1024.0):.1f}" if exists else "-"
        digest = sha256_short(p) if exists else "-"
        lines.append(
            f"| `{a.path}` | {'yes' if a.required else 'no'} | {'yes' if exists else 'no'} | {size_kb} | `{digest}` | {a.purpose} |"
        )
    lines.append("")

    lines.append("## Decision")
    lines.append("")
    if required_missing == 0:
        lines.append("- required artifacts: COMPLETE")
    else:
        lines.append(f"- required artifacts: INCOMPLETE (missing={required_missing})")
    lines.append("- interpretation: this is a bounded-verification release package, not an unbounded full-concrete closure proof.")
    lines.append("")

    lines.append("## Reproduction")
    lines.append("")
    lines.append("```bash")
    lines.append("make submission-ready")
    lines.append("make submission-manifest")
    lines.append("make submission-bundle")
    lines.append("```")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    out = args.out.resolve()
    out.write_text(render(root, build_list()), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
