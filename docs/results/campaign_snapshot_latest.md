# Unified Campaign Snapshot (20260221-003535)

This snapshot consolidates matrix, transfer, wrapper, and n=7 scale evidence.

## Matrix (latest CSV)

- source: `docs/results/tlc_matrix_20260215-105849.csv`

| Profile | Model | States | Distinct | Diameter | Wall-clock | Result |
|---|---|---:|---:|---:|---:|---|
| baseline | attack | 15045 | 4366 | 49 | 05s | PASS |
| baseline | aps | 10087 | 3035 | 63 | 00s | PASS |
| baseline | joint | 45095 | 14737 | 73 | 20s | PASS |
| mv3 | attack | 5936703 | 1196611 | 69 | 07min 39s | PASS |
| mv3 | aps | 14762371 | 3405172 | 89 | 59min 13s | PASS |
| mv3 | joint | 56392041 | 14807882 | 98 | 03h 24min | PASS |
| mv4 | attack | 113041 | 32774 | 70 | 21s | PASS |
| mv4 | aps | 16791 | 5047 | 97 | 39s | PASS |
| mv4 | joint | 104191 | 33269 | 106 | 55s | PASS |

## Transfer (bundle run)

| Profile | States | Distinct | Diameter | Wall-clock | Result |
|---|---:|---:|---:|---:|---|
| baseline | 269339 | 47796 | 30 | 01min 10s | PASS |
| mv3 | 269339 | 47796 | 30 | 01min 21s | PASS |
| mv4 | 269339 | 47796 | 30 | 01min 21s | PASS |

## Wrapper Projection (latest snapshot)

| Profile | Model | States | Distinct | Diameter | Wall-clock | Result |
|---|---|---:|---:|---:|---:|---|
| baseline | MC_AdaptiveAttack | 15045 | 4366 | 49 | 11s | PASS |
| baseline | MC_LivenessAPS | 10087 | 3035 | 63 | 13s | PASS |
| baseline | MC_LivenessAPSAttack | 45095 | 14737 | 73 | 21s | PASS |
| mv4 | MC_AdaptiveAttack | 113041 | 32774 | 70 | 43s | PASS |
| mv4 | MC_LivenessAPS | 16791 | 5047 | 98 | 39s | PASS |
| mv4 | MC_LivenessAPSAttack | 104191 | 33269 | 107 | 01min 01s | PASS |

## n=7 Scale Snapshot

| Model | States | Distinct | Diameter | Wall-clock | Result |
|---|---:|---:|---:|---:|---|
| MC_AdaptiveAttack (n7) | 15045 | 4366 | 49 | 04min 50s | PASS |

## n=7 Quick Scale Snapshot (n7lite)

| Model | States | Distinct | Diameter | Wall-clock | Result |
|---|---:|---:|---:|---:|---|
| MC_AdaptiveAttack | 5009 | 1454 | 39 | 03min 19s | PASS |

## MaxView=5 Full-Suite Snapshot

| Model | States | Distinct | Diameter | Wall-clock | Result |
|---|---:|---:|---:|---:|---|
| MC_AdaptiveAttack | 299733 | 86886 | 80 | 01min 42s | PASS |
| MC_LivenessAPS | 20143 | 6053 | 115 | 01min 14s | PASS |
| MC_LivenessAPSAttack | 143795 | 45553 | 124 | 01min 39s | PASS |
| MC_RefinementTransfer | 269339 | 47796 | 30 | 01min 27s | PASS |

## Proof Track Snapshot (latest)

| Module | Backend | Status | Obligations |
|---|---|---|---:|
| `AdaptiveBFT_Invariant_Theorems` | TLAPS | PASS | 120 |
| `AdaptiveBFT_Theorems` | TLAPS | PASS | 73 |
| `AdaptiveBFT_Refinement_Theorems` | TLAPS | PASS | 54 |
| `AdaptiveBFT_Refinement_Kernel` | TLAPS | PASS | 17 |
| `AdaptiveBFT_Transfer_Kernel` | TLAPS | PASS | 22 |
| `AdaptiveBFT_MainClaim_Theorems` | TLAPS | PASS | 11 |
| `AdaptiveBFT_Liveness_Theorems` | TLAPS | PASS | 10 |
| `AdaptiveBFT_ConcreteBridge_Theorems` | TLAPS | PASS | 6 |
| `AdaptiveBFT_AbstractBridge_Theorems` | SANY | PASS | N/A |
| `AdaptiveBFT_ConcreteBinding_Theorems` | TLAPS | PASS | 14 |
| `AdaptiveBFT_ConcreteTransfer_Theorems` | TLAPS | PASS | 10 |

## Concrete TLAPS Probe (latest)

| Module | Status | Duration | Exit |
|---|---|---:|---:|
| `AdaptiveBFT_ConcreteBridge_Theorems.tla` | PASS | 300s | 7.5s |
| `AdaptiveBFT_ConcreteBinding_Theorems.tla` | PASS | 300s | 123.6s |
| `AdaptiveBFT_ConcreteTransfer_Theorems.tla` | PASS | 1200s | 744.9s |

Interpretation: bounded model-checking evidence under explicit assumptions; not an unbounded closed theorem.
