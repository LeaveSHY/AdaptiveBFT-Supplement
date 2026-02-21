#!/usr/bin/env python3
"""Validate reviewer-facing claim artifacts are present and structurally sane."""

from __future__ import annotations

import re
import sys
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
CLAIM_BOUNDARY = ROOT / "docs" / "claim_boundary.md"
RESULTS_DIR = ROOT / "docs" / "results"
PROOF_SNAPSHOT = RESULTS_DIR / "proof_snapshot_latest.md"
CAMPAIGN_SNAPSHOT = RESULTS_DIR / "campaign_snapshot_latest.md"
BUNDLE_SUMMARY = RESULTS_DIR / "strong_claim_bundle_latest.md"
RELEASE_STATUS = RESULTS_DIR / "release_status_latest.md"
PROOF_BLOCKERS = RESULTS_DIR / "proof_blockers_latest.md"
CONCRETE_TLAPS_PROBE = RESULTS_DIR / "concrete_tlaps_probe_latest.md"
CLOSURE_ATTEMPT = RESULTS_DIR / "safety_transfer_closure_attempt_latest.md"
FAILURE_TAXONOMY = RESULTS_DIR / "safety_transfer_failure_taxonomy_latest.md"
CLOSURE_TREND = RESULTS_DIR / "safety_transfer_closure_trend_latest.md"
GOALPACK = RESULTS_DIR / "safety_transfer_goalpack_latest.md"


def extract_result_paths(text: str) -> list[Path]:
    rels = sorted(set(re.findall(r"`(docs/results/[^`]+)`", text)))
    return [ROOT / rel for rel in rels]


def check_file_exists_nonempty(path: Path) -> list[str]:
    errs: list[str] = []
    if not path.exists():
        errs.append(f"missing artifact: {path.relative_to(ROOT)}")
        return errs
    if path.stat().st_size == 0:
        errs.append(f"empty artifact: {path.relative_to(ROOT)}")
    return errs


def check_bundle_all_pass(bundle_path: Path) -> tuple[list[str], list[str]]:
    errs: list[str] = []
    warns: list[str] = []
    text = bundle_path.read_text(encoding="utf-8", errors="replace")
    rows = re.findall(r"^\|\s*[^|]+\|\s*`[^`]+`\s*\|\s*(PASS|FAIL)\s*\|", text, re.MULTILINE)
    if not rows:
        errs.append("bundle summary has no step rows")
        return errs, warns
    if any(r != "PASS" for r in rows):
        warns.append("bundle summary contains non-PASS step (latest run may have been interrupted)")
    return errs, warns


def check_campaign_has_boundary_note(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    needle = "bounded model-checking evidence under explicit assumptions; not an unbounded closed theorem"
    if needle not in text:
        errs.append("campaign snapshot is missing claim-boundary interpretation line")
    return errs


def check_proof_snapshot(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    required_modules = [
        "AdaptiveBFT_Invariant_Theorems",
        "AdaptiveBFT_Theorems",
        "AdaptiveBFT_Refinement_Theorems",
        "AdaptiveBFT_Refinement_Kernel",
        "AdaptiveBFT_Transfer_Kernel",
        "AdaptiveBFT_MainClaim_Theorems",
        "AdaptiveBFT_Liveness_Theorems",
        "AdaptiveBFT_ConcreteBridge_Theorems",
    ]
    for module in required_modules:
        if f"`{module}`" not in text:
            errs.append(f"proof snapshot missing module row: {module}")
    return errs


def check_readme_claim_scope(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")

    boundary_markers = [
        "not an unbounded theorem proof",
        "not a closed full-concrete unbounded proof",
    ]
    if not any(marker in text for marker in boundary_markers):
        errs.append("README is missing explicit non-claim boundary wording for unbounded full-concrete proof")

    guarded_tokens = ("not", "only when", "blocked", "future-work", "roadmap")
    for raw_line in text.splitlines():
        line = raw_line.strip().lower()
        if "full protocol unbounded correctness" in line:
            if not any(token in line for token in guarded_tokens):
                errs.append("README contains an unqualified 'full protocol unbounded correctness' statement")
    return errs


def load_coverage_allowlist() -> set[str]:
    coverage_path = ROOT / "scripts" / "check_theorem_coverage.py"
    spec = importlib.util.spec_from_file_location("check_theorem_coverage", coverage_path)
    if spec is None or spec.loader is None:
        return set()
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return set(getattr(module, "ALLOWED_UNPROVED", set()))


def check_proof_blockers(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "Open Theorem Blockers" in text:
        return errs
    row_count = len(re.findall(r"^\|\s*`[^`]+`\s*\|", text, re.MULTILINE))
    allowlist = load_coverage_allowlist()
    if allowlist and row_count == 0:
        errs.append("proof blocker snapshot is missing theorem rows while allowlist is non-empty")
    for key in sorted(allowlist):
        theorem = key.split(":", 1)[1]
        if f"`{theorem}`" not in text:
            errs.append(f"proof blocker snapshot missing allowlisted theorem: {theorem}")
    return errs


def check_release_has_blockers(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "## Open Theorem Blockers" not in text:
        errs.append("release status is missing 'Open Theorem Blockers' section")
    if "`docs/results/proof_blockers_latest.md`" not in text:
        errs.append("release status is missing link to proof blocker snapshot")
    if CONCRETE_TLAPS_PROBE.exists() and "`docs/results/concrete_tlaps_probe_latest.md`" not in text:
        errs.append("release status is missing link to concrete TLAPS probe artifact")
    if CLOSURE_ATTEMPT.exists() and "`docs/results/safety_transfer_closure_attempt_latest.md`" not in text:
        errs.append("release status is missing link to safety-transfer closure-attempt artifact")
    if FAILURE_TAXONOMY.exists() and "`docs/results/safety_transfer_failure_taxonomy_latest.md`" not in text:
        errs.append("release status is missing link to safety-transfer failure-taxonomy artifact")
    if CLOSURE_TREND.exists() and "`docs/results/safety_transfer_closure_trend_latest.md`" not in text:
        errs.append("release status is missing link to safety-transfer closure-trend artifact")
    if GOALPACK.exists() and "`docs/results/safety_transfer_goalpack_latest.md`" not in text:
        errs.append("release status is missing link to safety-transfer goalpack artifact")
    return errs


def check_closure_attempt(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "## Candidate Proof Attempts" not in text:
        errs.append("closure-attempt artifact is missing 'Candidate Proof Attempts' section")
    if "| Strategy | Status | Exit | Duration | Signature | Log |" not in text:
        errs.append("closure-attempt artifact is missing expected attempts table header")
    return errs


def check_failure_taxonomy(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "## Grouped Goal Signatures" not in text:
        errs.append("failure-taxonomy artifact is missing 'Grouped Goal Signatures' section")
    if "| Goal Signature | Strategies | Hits |" not in text:
        errs.append("failure-taxonomy artifact is missing expected grouped-signature table header")
    return errs


def check_closure_trend(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "## Strategy Aggregates" not in text:
        errs.append("closure-trend artifact is missing 'Strategy Aggregates' section")
    if "| Strategy | Runs | Pass | Fail | Last Status | Last Signature |" not in text:
        errs.append("closure-trend artifact is missing expected aggregate table header")
    return errs


def check_goalpack(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "## Ranked Unproved Goals" not in text:
        errs.append("goalpack artifact is missing 'Ranked Unproved Goals' section")
    if "| Rank | Goal line | Hits | Strategies | Goal formula |" not in text:
        errs.append("goalpack artifact is missing expected ranked-goals table header")
    return errs


def check_concrete_probe(path: Path) -> list[str]:
    errs: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    if "Concrete TLAPS Probe" not in text:
        errs.append("concrete probe artifact is missing title")
    expected_headers = [
        "| Module | Status | Duration | Exit | Obligations Proved (max) | Failed Obligations | Signature | Log |",
        "| Module | Status | Timeout | Duration | Exit | Obligations Proved (max) | Failed Obligations | Signature | Log |",
    ]
    if not any(header in text for header in expected_headers):
        errs.append("concrete probe artifact is missing expected table header")
    return errs


def main() -> int:
    errors: list[str] = []
    warnings: list[str] = []

    claim_text = CLAIM_BOUNDARY.read_text(encoding="utf-8", errors="replace")
    referenced = extract_result_paths(claim_text)
    for path in referenced:
        errors.extend(check_file_exists_nonempty(path))

    errors.extend(check_file_exists_nonempty(PROOF_SNAPSHOT))
    errors.extend(check_file_exists_nonempty(CAMPAIGN_SNAPSHOT))
    errors.extend(check_file_exists_nonempty(BUNDLE_SUMMARY))
    errors.extend(check_file_exists_nonempty(RELEASE_STATUS))
    errors.extend(check_file_exists_nonempty(PROOF_BLOCKERS))
    if CONCRETE_TLAPS_PROBE.exists():
        errors.extend(check_file_exists_nonempty(CONCRETE_TLAPS_PROBE))

    if BUNDLE_SUMMARY.exists():
        err, warn = check_bundle_all_pass(BUNDLE_SUMMARY)
        errors.extend(err)
        warnings.extend(warn)
    if CAMPAIGN_SNAPSHOT.exists():
        errors.extend(check_campaign_has_boundary_note(CAMPAIGN_SNAPSHOT))
    if PROOF_SNAPSHOT.exists():
        errors.extend(check_proof_snapshot(PROOF_SNAPSHOT))
    if PROOF_BLOCKERS.exists():
        errors.extend(check_proof_blockers(PROOF_BLOCKERS))
    if CLOSURE_ATTEMPT.exists():
        errors.extend(check_closure_attempt(CLOSURE_ATTEMPT))
    if FAILURE_TAXONOMY.exists():
        errors.extend(check_failure_taxonomy(FAILURE_TAXONOMY))
    if CLOSURE_TREND.exists():
        errors.extend(check_closure_trend(CLOSURE_TREND))
    if GOALPACK.exists():
        errors.extend(check_goalpack(GOALPACK))
    if CONCRETE_TLAPS_PROBE.exists():
        errors.extend(check_concrete_probe(CONCRETE_TLAPS_PROBE))
    if RELEASE_STATUS.exists():
        errors.extend(check_release_has_blockers(RELEASE_STATUS))
    errors.extend(check_readme_claim_scope(README))

    if errors:
        for e in errors:
            print(f"[ERROR] {e}")
        for w in warnings:
            print(f"[WARN] {w}")
        print(f"\nFAILED: {len(errors)} claim-artifact issue(s).")
        return 1

    for w in warnings:
        print(f"[WARN] {w}")
    print("OK: claim-boundary artifacts are present and structurally consistent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
