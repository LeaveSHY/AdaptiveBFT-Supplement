# Submission Guide (Bounded Verification Release)

Last updated: 2026-02-21

This guide is the final handoff for paper submission and artifact upload.

## 1) One-command build

Quick (reuse latest heavy artifacts):

```bash
make submission-ready
```

Strict (rerun gate + bundle without reuse):

```bash
make submission-ready-full
```

## 2) Final files to upload

- `docs/results/submission_bundle_latest.zip`
- `docs/results/submission_artifact_manifest_latest.md`
- `docs/results/submission_package_check_latest.md`
- `docs/results/submission_rc_latest.md`

## 3) Core evidence files

- `docs/results/release_status_latest.md`
- `docs/results/strong_claim_bundle_latest.md`
- `docs/results/proof_snapshot_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`
- `docs/results/wrapper_projection_latest.md`
- `docs/results/mv5_suite_latest.md`

## 4) Claim-boundary files

- `docs/claim_boundary.md`
- `docs/assumption_to_evidence_map.md`
- `docs/reviewer_checklist.md`
- `docs/paper_claim_text.tex`

## 5) Reviewer-safe wording

Use bounded/assumption-explicit wording only.

- Allowed: bounded exhaustive TLC checks + machine-checked theorem-track evidence under explicit assumptions.
- Not allowed: closed full-concrete unbounded correctness claim.

## 6) Environment note

If `pdflatex` is unavailable, fastlane reuses existing appendix PDFs and marks
`appendix_five_figs` as PASS (`reused-existing-pdfs`) when those PDFs exist.
