#!/usr/bin/env python3
"""Build a submission-ready RC summary from latest verification artifacts."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import List


@dataclass(frozen=True)
class ArtifactRow:
    path: str
    required: bool
    exists: bool
    note: str


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="replace")


def parse_line_value(md: str, prefix: str) -> str:
    for line in md.splitlines():
        if line.strip().startswith(prefix):
            return line.strip()[len(prefix) :].strip()
    return ""


def parse_overall_pass(release_md: str) -> str:
    m = re.search(r"- overall:\s*(PASS|FAIL)", release_md)
    return m.group(1) if m else "UNKNOWN"


def parse_fastlane_status(fastlane_md: str) -> str:
    if not fastlane_md.strip():
        return "UNKNOWN"
    statuses: List[str] = []
    for line in fastlane_md.splitlines():
        line = line.strip()
        if not line.startswith("|") or line.startswith("|---") or line.startswith("| Step |"):
            continue
        parts = [p.strip() for p in line.strip("|").split("|")]
        if len(parts) < 5:
            continue
        statuses.append(parts[2])
    if not statuses:
        return "UNKNOWN"
    if any(s == "FAIL" for s in statuses):
        return "FAIL"
    if any(s == "PASS" for s in statuses):
        return "PASS"
    return "UNKNOWN"


def build_rows(root: Path) -> List[ArtifactRow]:
    req = [
        ("README.md", True, "Top-level narrative and reproducibility commands."),
        ("docs/claim_boundary.md", True, "Normative claim boundary."),
        ("docs/proof_roadmap.md", True, "Proof-obligation roadmap and closure criteria."),
        ("docs/assumption_to_evidence_map.md", True, "Assumption-to-evidence traceability."),
        ("docs/reviewer_checklist.md", True, "Reviewer challenge/repro checklist."),
        ("docs/submission_guide.md", True, "Submission handoff and upload checklist."),
        ("docs/formal_figures.tex", True, "Paper appendix formal-spec section."),
        ("docs/verification_tables.tex", True, "Paper tables for settings/results."),
        ("docs/paper_claim_text.tex", True, "Safe paper claim/repro paragraph snippet."),
        ("docs/results/release_status_latest.md", True, "Release dashboard."),
        ("docs/results/submission_artifact_manifest_latest.md", True, "Integrity manifest with hashes."),
        ("docs/results/submission_bundle_latest.zip", True, "Upload-ready artifact bundle."),
        ("docs/results/strong_claim_bundle_latest.md", True, "Bundle campaign summary."),
        ("docs/results/fastlane_release_latest.md", True, "One-command release campaign summary."),
        ("docs/results/proof_snapshot_latest.md", True, "Theorem-track snapshot."),
        ("docs/results/concrete_tlaps_probe_latest.md", True, "Concrete TLAPS diagnostics."),
        ("docs/results/mv5_suite_latest.md", True, "Deep bounded suite snapshot."),
        ("docs/results/wrapper_projection_latest.md", True, "Wrapper transfer checks."),
        ("docs/results/scale_n7_attack_latest.md", False, "Optional scale sanity artifact."),
        ("docs/results/scale_n7lite_suite_latest.md", False, "Optional quick scale artifact."),
        ("docs/results/scale_n7lite_full_suite_latest.md", False, "Optional quick full-suite scale artifact."),
    ]
    rows: List[ArtifactRow] = []
    for rel, required, note in req:
        p = root / rel
        rows.append(ArtifactRow(path=rel, required=required, exists=p.exists(), note=note))
    return rows


def render(args: argparse.Namespace, rows: List[ArtifactRow], release_md: str, fastlane_md: str) -> str:
    now = datetime.now(timezone.utc).astimezone()
    overall = parse_overall_pass(release_md)
    scope = parse_line_value(release_md, "- scope:")
    boundary = parse_line_value(release_md, "- claim boundary:")
    fastlane_status = parse_fastlane_status(fastlane_md)

    req_ok = all(r.exists for r in rows if r.required)
    artifact_gate = "PASS" if req_ok else "FAIL"

    lines: List[str] = []
    lines.append("# Submission RC Summary")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append("- intent: reviewer-defensible strongest bounded-verification release")
    lines.append(f"- release status: {overall}")
    lines.append(f"- fastlane status: {fastlane_status}")
    lines.append(f"- artifact completeness gate: {artifact_gate}")
    if scope:
        lines.append(f"- scope: {scope}")
    if boundary:
        lines.append(f"- claim boundary: {boundary}")
    lines.append("")

    lines.append("## Paper Claim Text (Safe)")
    lines.append("")
    lines.append(
        "Under explicit assumptions (bounded domain, symbolic cryptography, bounded adaptive adversary, "
        "and eventual-synchrony/fairness envelope), AdaptiveBFT safety and liveness properties are systematically "
        "validated by reproducible bounded model checking and machine-checked theorem-track artifacts."
    )
    lines.append("")

    lines.append("## Repro Commands (Submission Path)")
    lines.append("")
    lines.append("```bash")
    lines.append("make gate-strong")
    lines.append("make bundle")
    lines.append("make release-status")
    lines.append("make fastlane FASTLANE_SKIP_BUNDLE=1")
    lines.append("make claim-check")
    lines.append("make check-sync")
    lines.append("```")
    lines.append("")

    lines.append("## Artifact Manifest")
    lines.append("")
    lines.append("| Artifact | Required | Exists | Notes |")
    lines.append("|---|---|---|---|")
    for r in rows:
        req = "yes" if r.required else "no"
        ex = "yes" if r.exists else "no"
        lines.append(f"| `{r.path}` | {req} | {ex} | {r.note} |")
    lines.append("")

    lines.append("## Reviewer-Facing Evidence Entry Points")
    lines.append("")
    lines.append("1. Claim scope and non-claims: `docs/claim_boundary.md`")
    lines.append("2. Release dashboard: `docs/results/release_status_latest.md`")
    lines.append("3. Proof-track snapshot: `docs/results/proof_snapshot_latest.md`")
    lines.append("4. Concrete TLAPS probe: `docs/results/concrete_tlaps_probe_latest.md`")
    lines.append("5. Wrapper transfer checks: `docs/results/wrapper_projection_latest.md`")
    lines.append("6. Assumption traceability: `docs/assumption_to_evidence_map.md`")
    lines.append("7. Rebuttal checklist: `docs/reviewer_checklist.md`")
    lines.append("8. Integrity manifest: `docs/results/submission_artifact_manifest_latest.md`")
    lines.append("9. Upload bundle: `docs/results/submission_bundle_latest.zip`")
    lines.append("")

    lines.append("## RC Decision")
    lines.append("")
    if overall == "PASS" and fastlane_status == "PASS" and artifact_gate == "PASS":
        lines.append("- status: READY (bounded-verification submission RC)")
        lines.append("- caution: do not claim closed full-concrete unbounded proof.")
    else:
        lines.append("- status: NOT READY")
        lines.append("- action: rerun failed gates and regenerate this RC summary.")
    lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    release_path = root / "docs" / "results" / "release_status_latest.md"
    fastlane_path = root / "docs" / "results" / "fastlane_release_latest.md"
    release_md = read_text(release_path)
    fastlane_md = read_text(fastlane_path)
    rows = build_rows(root)

    out_text = render(args, rows, release_md, fastlane_md)
    args.out.write_text(out_text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
