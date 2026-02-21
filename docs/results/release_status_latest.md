# Release Status Dashboard

- generated: 2026-02-21 02:17:03 +0800
- scope: bounded TLC evidence + assumption-explicit theorem track
- claim boundary: not a closed full-concrete unbounded proof

## Strong-Claim Bundle

- overall: PASS

| Step | Status | Duration |
|---|---|---:|
| `pre_artifact_sync` | PASS | 0s |
| `gate` | PASS | 291s |
| `concrete_tlaps_probe` | PASS | 877s |
| `closure_attempt_safety` | PASS | 568s |
| `closure_failure_taxonomy` | PASS | 0s |
| `closure_trend` | PASS | 0s |
| `transfer_baseline` | PASS | 71s |
| `transfer_mv3` | PASS | 82s |
| `transfer_mv4` | PASS | 83s |
| `scale_n7_attack` | PASS | 291s |
| `scale_n7lite_suite` | PASS | 200s |
| `scale_n7lite_full_suite` | PASS | 2737s |
| `wrapper_projection` | PASS | 195s |
| `suite_mv5` | PASS | 367s |
| `snapshot_row_sync` | PASS | 0s |
| `wrapper_table_sync` | PASS | 0s |
| `post_sync_check` | PASS | 0s |

## MaxView=5 Full Suite

| Model | Result | Wall-clock |
|---|---|---:|
| `MC_AdaptiveAttack` | PASS | 01min 42s |
| `MC_LivenessAPS` | PASS | 01min 14s |
| `MC_LivenessAPSAttack` | PASS | 01min 39s |
| `MC_RefinementTransfer` | PASS | 01min 27s |

## n=7 Quick Full-Suite (n7lite)

| Model | Result | Wall-clock |
|---|---|---:|
| `MC_AdaptiveAttack` | PASS | 03min 20s |
| `MC_LivenessAPS` | TIMEOUT | >900s (timeout) |
| `MC_LivenessAPSAttack` | TIMEOUT | >900s (timeout) |
| `MC_RefinementTransfer` | TIMEOUT | >900s (timeout) |

## Proof Track

| Module | Status | Detail |
|---|---|---|
| `AdaptiveBFT_Invariant_Theorems` | PASS | TLAPS, obligations=120 |
| `AdaptiveBFT_Theorems` | PASS | TLAPS, obligations=73 |
| `AdaptiveBFT_Refinement_Theorems` | PASS | TLAPS, obligations=54 |
| `AdaptiveBFT_Refinement_Kernel` | PASS | TLAPS, obligations=17 |
| `AdaptiveBFT_Transfer_Kernel` | PASS | TLAPS, obligations=22 |
| `AdaptiveBFT_MainClaim_Theorems` | PASS | TLAPS, obligations=11 |
| `AdaptiveBFT_Liveness_Theorems` | PASS | TLAPS, obligations=10 |
| `AdaptiveBFT_ConcreteBridge_Theorems` | PASS | TLAPS, obligations=6 |
| `AdaptiveBFT_AbstractBridge_Theorems` | PASS | SANY, obligations=N/A |
| `AdaptiveBFT_ConcreteBinding_Theorems` | PASS | TLAPS, obligations=14 |
| `AdaptiveBFT_ConcreteTransfer_Theorems` | PASS | TLAPS, obligations=10 |

## Concrete TLAPS Probe

| Module | Status | Detail |
|---|---|---|
| `AdaptiveBFT_ConcreteBridge_Theorems.tla` | PASS | timeout=300s, 7.5s, proved=6, failed=0 |
| `AdaptiveBFT_ConcreteBinding_Theorems.tla` | PASS | timeout=300s, 123.6s, proved=14, failed=0 |
| `AdaptiveBFT_ConcreteTransfer_Theorems.tla` | PASS | timeout=1200s, 744.9s, proved=10, failed=0 |

## Open Theorem Blockers

| Theorem | Status | Location |
|---|---|---|
| `(none)` | fully-closed | `-` |

## Safety-Transfer Closure Attempts

| Strategy | Status | Detail |
|---|---|---|
| `already_closed_skip` | PASS | exit=0, duration=0.0s |

## Safety-Transfer Failure Taxonomy

| Goal Signature | Hits | Strategies |
|---|---:|---|
| (none) | 0 | - |

## Safety-Transfer Closure Trend

| Strategy | Runs | Pass/Fail |
|---|---|---|
| `already_closed_skip` | runs=17 | pass=17, fail=0 |
| `instance_theorem_def` | runs=3 | pass=0, fail=3 |
| `instance_theorem_direct` | runs=3 | pass=0, fail=3 |
| `instance_theorem_ptl_lift` | runs=3 | pass=0, fail=3 |
| `instance_use_obvious` | runs=3 | pass=0, fail=3 |

## Safety-Transfer Goalpack

| Goal | Hits | Formula |
|---|---|---|
| rank=1, line=- | hits=0 | no parsed goals |

## Linked Artifacts

- `docs/results/strong_claim_bundle_latest.md`
- `docs/results/mv5_suite_latest.md`
- `docs/results/scale_n7lite_full_suite_latest.md`
- `docs/results/proof_snapshot_latest.md`
- `docs/results/proof_blockers_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`
- `docs/results/safety_transfer_closure_attempt_latest.md`
- `docs/results/safety_transfer_failure_taxonomy_latest.md`
- `docs/results/safety_transfer_closure_trend_latest.md`
- `docs/results/safety_transfer_goalpack_latest.md`
- `docs/results/campaign_snapshot_latest.md`
