# Fastlane Release Campaign (20260221-021702)

This campaign executes the reviewer-facing high-value stack in one command.
It reuses `make bundle` as the heavy core and avoids redundant reruns.

| Step | Command | Status | Duration | Log |
|---|---|---|---:|---|
| pre_artifact_sync | `make sync-wrapper-table && make sync-snapshot-rows` | PASS | 0s | `_fastlane_20260221-021702_pre_artifact_sync.out` |
| bundle | `make bundle` | SKIP | 0s | `reused-latest-bundle` |

Note: reused existing `docs/results/strong_claim_bundle_latest.md` (`FASTLANE_SKIP_BUNDLE=1`).
| appendix_five_figs | `make appendix-five-figs` | PASS | 0s | `reused-existing-pdfs` |

Note: `pdflatex` unavailable; reused existing 5 appendix PDFs from repository workspace.
| theorem_coverage | `make check-theorem-coverage` | PASS | 0s | `_fastlane_20260221-021702_theorem_coverage.out` |
| claim_check | `make claim-check` | PASS | 0s | `_fastlane_20260221-021702_claim_check.out` |
| release_status | `make release-status` | PASS | 1s | `_fastlane_20260221-021702_release_status.out` |

## Produced Artifacts

- `docs/results/strong_claim_bundle_latest.md`
- `docs/results/release_status_latest.md`
- `docs/results/proof_snapshot_latest.md`
- `docs/results/proof_blockers_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`
- `docs/results/campaign_snapshot_latest.md`
- `docs/results/safety_transfer_closure_attempt_latest.md`
- `docs/results/safety_transfer_failure_taxonomy_latest.md`
- `docs/results/safety_transfer_closure_trend_latest.md`
- `docs/results/safety_transfer_goalpack_latest.md`
- `docs/results/mv5_suite_latest.md`
- `docs/results/scale_n7_attack_latest.md`
- `docs/results/scale_n7lite_suite_latest.md`
- `docs/results/scale_n7lite_full_suite_latest.md`
- `docs/results/wrapper_projection_latest.md`
- `AdaptiveBFT_MainFlow.pdf`
- `AdaptiveBFT_Types.pdf`
- `modules/AVC_RVS.pdf`
- `modules/APS_Mempool.pdf`
- `AdaptiveBFT_Properties.pdf`
