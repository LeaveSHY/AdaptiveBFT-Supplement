# n=7 Quick Scale Snapshot (n7lite)

- date: 2026-02-21 01:16:38 CST
- profile: `n7lite` (`n=7, f=2, q=5, MaxView=1`)
- modes: `attack`
- note: quick scale sanity (bounded, assumption-explicit); default mode is attack-only, full-suite is enabled via INCLUDE_APS/INCLUDE_JOINT/INCLUDE_TRANSFER

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| `MC_AdaptiveAttack` | 5009 | 1454 | 39 | 03min 19s | PASS |

Interpretation:

- This snapshot is bounded finite-domain evidence for quick scalability sanity.
- It does not replace unbounded theorem proofs.
