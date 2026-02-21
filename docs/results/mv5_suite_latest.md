# MaxView=5 Full-Suite Snapshot

- date: 2026-02-21 02:11:37 CST
- profile: `mv5` (`n=4, f=1, q=3, MaxView=5`)

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| `MC_AdaptiveAttack` | 299733 | 86886 | 80 | 01min 42s | PASS |
| `MC_LivenessAPS` | 20143 | 6053 | 115 | 01min 14s | PASS |
| `MC_LivenessAPSAttack` | 143795 | 45553 | 124 | 01min 39s | PASS |
| `MC_RefinementTransfer` | 269339 | 47796 | 30 | 01min 27s | PASS |

Interpretation:

- This snapshot strengthens bounded evidence by increasing view depth to MaxView=5.
- It remains bounded, assumption-explicit model-checking evidence.
- It does not replace unbounded theorem proofs.
