# Strong-Claim Bundle (20260221-003535)

This bundle runs the core executable evidence stack used by reviewer-facing claims.

| Step | Command | Status | Duration | Log |
|---|---|---|---:|---|
| pre_artifact_sync | `make sync-wrapper-table && make sync-snapshot-rows` | PASS | 0s | `_bundle_20260221-003535_pre_artifact_sync.out` |
| gate | `TLAPS_RETRY=8 make gate` | PASS | 291s | `_bundle_20260221-003535_gate.out` |
| concrete_tlaps_probe | `PROBE_TIMEOUT_SEC=300 PROBE_TRANSFER_TIMEOUT_SEC=1200 make concrete-tlaps-probe-full` | PASS | 877s | `_bundle_20260221-003535_concrete_tlaps_probe.out` |
| closure_attempt_safety | `make closure-attempt-safety` | PASS | 568s | `_bundle_20260221-003535_closure_attempt_safety.out` |
| closure_failure_taxonomy | `make closure-failure-taxonomy` | PASS | 0s | `_bundle_20260221-003535_closure_failure_taxonomy.out` |
| closure_trend | `make closure-trend` | PASS | 0s | `_bundle_20260221-003535_closure_trend.out` |
| transfer_baseline | `make test-transfer` | PASS | 71s | `_bundle_20260221-003535_transfer_baseline.out` |
| transfer_mv3 | `make test-transfer-mv3` | PASS | 82s | `_bundle_20260221-003535_transfer_mv3.out` |
| transfer_mv4 | `make test-transfer-mv4` | PASS | 83s | `_bundle_20260221-003535_transfer_mv4.out` |
| scale_n7_attack | `make scale-n7` | PASS | 291s | `_bundle_20260221-003535_scale_n7_attack.out` |
| scale_n7lite_suite | `make scale-n7lite` | PASS | 200s | `_bundle_20260221-003535_scale_n7lite_suite.out` |
| scale_n7lite_full_suite | `MODE_TIMEOUT_SEC=900 make scale-n7lite-full` | PASS | 2737s | `_bundle_20260221-003535_scale_n7lite_full_suite.out` |
| wrapper_projection | `make wrapper-projection` | PASS | 195s | `_bundle_20260221-003535_wrapper_projection.out` |
| suite_mv5 | `make suite-mv5` | PASS | 367s | `_bundle_20260221-003535_suite_mv5.out` |
| snapshot_row_sync | `make sync-snapshot-rows` | PASS | 0s | `_bundle_20260221-003535_snapshot_row_sync.out` |
| wrapper_table_sync | `make sync-wrapper-table` | PASS | 0s | `_bundle_20260221-003535_wrapper_table_sync.out` |
| post_sync_check | `make check-sync` | PASS | 0s | `_bundle_20260221-003535_post_sync_check.out` |

## Produced Artifacts

- `docs/results/transfer_snapshot_20260221-003535.md`
- `docs/results/transfer_snapshot_latest.md`
- `docs/results/proof_snapshot_latest.md`
- `docs/results/proof_blockers_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`
- `docs/results/safety_transfer_closure_attempt_latest.md`
- `docs/results/safety_transfer_failure_taxonomy_latest.md`
- `docs/results/safety_transfer_closure_trend_latest.md`
- `docs/results/safety_transfer_goalpack_latest.md`
- `docs/results/wrapper_projection_latest.md`
- `docs/results/wrapper_projection_snapshot_20260221.md`
- `docs/results/scale_n7_attack_latest.md`
- `docs/results/scale_n7lite_suite_latest.md`
- `docs/results/scale_n7lite_full_suite_latest.md`
- `docs/results/mv5_suite_latest.md`
- `docs/results/campaign_snapshot_20260221-003535.md`
- `docs/results/campaign_snapshot_latest.md`
