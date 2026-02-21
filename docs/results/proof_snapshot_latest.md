# Proof Track Snapshot

- generated: 2026-02-21 00:40:26 +0800
- interpretation: assumption-explicit theorem-track evidence; not a closed full-concrete unbounded proof

| Module | Backend | Status | Obligations | Evidence |
|---|---|---|---:|---|
| `AdaptiveBFT_Invariant_Theorems` | TLAPS | PASS | 120 | `states/.tlaps_AdaptiveBFT_Invariant_Theorems.log` |
| `AdaptiveBFT_Theorems` | TLAPS | PASS | 73 | `states/.tlaps_AdaptiveBFT_Theorems.log` |
| `AdaptiveBFT_Refinement_Theorems` | TLAPS | PASS | 54 | `states/.tlaps_AdaptiveBFT_Refinement_Theorems.log` |
| `AdaptiveBFT_Refinement_Kernel` | TLAPS | PASS | 17 | `states/.tlaps_AdaptiveBFT_Refinement_Kernel.log` |
| `AdaptiveBFT_Transfer_Kernel` | TLAPS | PASS | 22 | `states/.tlaps_AdaptiveBFT_Transfer_Kernel.log` |
| `AdaptiveBFT_MainClaim_Theorems` | TLAPS | PASS | 11 | `states/.tlaps_AdaptiveBFT_MainClaim_Theorems.log` |
| `AdaptiveBFT_Liveness_Theorems` | TLAPS | PASS | 10 | `states/.tlaps_AdaptiveBFT_Liveness_Theorems.log` |
| `AdaptiveBFT_ConcreteBridge_Theorems` | TLAPS | PASS | 6 | `states/.tlaps_AdaptiveBFT_ConcreteBridge_Theorems.log` |
| `AdaptiveBFT_AbstractBridge_Theorems` | SANY | PASS | N/A | `scripts/check_proof_track.sh (SANY phase)` |
| `AdaptiveBFT_ConcreteBinding_Theorems` | TLAPS | PASS | 14 | `states/.tlaps_AdaptiveBFT_ConcreteBinding_Theorems.log` |
| `AdaptiveBFT_ConcreteTransfer_Theorems` | TLAPS | PASS | 10 | `states/.tlaps_AdaptiveBFT_ConcreteTransfer_Theorems.log` |

Notes:

- TLAPS rows are parsed from `states/.tlaps_*.log` produced by `make proofs`.
- SANY rows rely on the same proof gate (`make proofs`) and always cover `AdaptiveBFT_AbstractBridge_Theorems`.
- `AdaptiveBFT_ConcreteBinding_Theorems` / `AdaptiveBFT_ConcreteTransfer_Theorems` are shown as TLAPS rows when optional logs exist (`TLAPS_CONCRETE_BINDING=1`, `TLAPS_CONCRETE_TRANSFER=1`).
- `make concrete-tlaps-probe-full` runs the same concrete probe with transfer-timeout override for reproducible slow-module diagnostics.
