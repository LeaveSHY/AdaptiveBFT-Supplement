# Submission-Ready Campaign (20260221-021701)

One-command campaign to produce submission RC artifacts and run final gates.
Defaults reuse latest heavy artifacts for speed; set skip vars to 0 for full rerun.

| Step | Command | Status | Duration | Log |
|---|---|---|---:|---|
| artifact_sync | `make sync-wrapper-table && make sync-snapshot-rows` | PASS | 1s | `_submission_ready_20260221-021701_artifact_sync.out` |
| gate_strong | `make gate-strong` | SKIP | 0s | `reused-latest-gate-strong` |
| bundle | `make bundle` | SKIP | 0s | `reused-latest-bundle` |
| release_status | `make release-status` | PASS | 0s | `_submission_ready_20260221-021701_release_status.out` |
| fastlane | `make fastlane FASTLANE_SKIP_BUNDLE=1` | PASS | 1s | `_submission_ready_20260221-021701_fastlane.out` |
| submission_rc | `make submission-rc` | PASS | 0s | `_submission_ready_20260221-021701_submission_rc.out` |
| submission_manifest | `make submission-manifest` | PASS | 0s | `_submission_ready_20260221-021701_submission_manifest.out` |
| submission_bundle | `make submission-bundle` | PASS | 0s | `_submission_ready_20260221-021701_submission_bundle.out` |
| check_submission | `make check-submission` | PASS | 1s | `_submission_ready_20260221-021701_check_submission.out` |
| claim_check | `make claim-check` | PASS | 0s | `_submission_ready_20260221-021701_claim_check.out` |
| sync_check | `make check-sync` | PASS | 0s | `_submission_ready_20260221-021701_sync_check.out` |
| theorem_coverage | `make check-theorem-coverage` | PASS | 0s | `_submission_ready_20260221-021701_theorem_coverage.out` |
| bridge_check | `make check-bridge` | PASS | 0s | `_submission_ready_20260221-021701_bridge_check.out` |

- overall: PASS
- skip_gate_strong: 1
- skip_bundle: 1

## Produced Artifacts

- `docs/results/release_status_latest.md`
- `docs/results/submission_rc_latest.md`
- `docs/results/submission_artifact_manifest_latest.md`
- `docs/results/submission_bundle_latest.zip`
- `docs/results/submission_package_check_latest.md`
- `docs/results/fastlane_release_latest.md`
- `docs/results/strong_claim_bundle_latest.md`
- `docs/results/proof_snapshot_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`
- `docs/claim_boundary.md`
- `docs/reviewer_checklist.md`
- `docs/assumption_to_evidence_map.md`
- `docs/paper_claim_text.tex`
