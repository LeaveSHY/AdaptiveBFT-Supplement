# n=7 Quick Scale Snapshot (n7lite)

- date: 2026-02-21 02:02:15 CST
- profile: `n7lite` (`n=7, f=2, q=5, MaxView=1`)
- modes: `attack,aps,joint,transfer`
- note: quick scale sanity (bounded, assumption-explicit); default mode is attack-only, full-suite is enabled via INCLUDE_APS/INCLUDE_JOINT/INCLUDE_TRANSFER
- per-mode timeout: `900s`

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| `MC_AdaptiveAttack` | 5009 | 1454 | 39 | 03min 20s | PASS |
| `MC_LivenessAPS` | - | - | - | >900s (timeout) | TIMEOUT |
| `MC_LivenessAPSAttack` | - | - | - | >900s (timeout) | TIMEOUT |
| `MC_RefinementTransfer` | - | - | - | >900s (timeout) | TIMEOUT |

Interpretation:

- This snapshot is bounded finite-domain evidence for quick scalability sanity.
- It does not replace unbounded theorem proofs.
