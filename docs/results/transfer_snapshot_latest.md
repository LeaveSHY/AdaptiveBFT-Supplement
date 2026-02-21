# Transfer Diagnostics Snapshot (20260221-003535)

Commands executed:

- `make test-transfer`
- `make test-transfer-mv3`
- `make test-transfer-mv4`

Model:

- `models/MC_RefinementTransfer.tla`
- properties: `InitProjectionChecked`, `StepProjectionChecked`, `StepBoxProjectionChecked`, `SpecProjectionChecked`, `SpecToAbstractSpecChecked`

Results:

| Profile | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| baseline (`MaxView=2`) | 269339 | 47796 | 30 | 01min 10s | Pass |
| `MaxView=3` | 269339 | 47796 | 30 | 01min 21s | Pass |
| `MaxView=4` | 269339 | 47796 | 30 | 01min 21s | Pass |

Constraint envelope:

- `TransferConstraint == /\ st.schedulerState = "Monitor"`
- `/\ st.networkCondition = "Stable"`
- `/\ st.view = 0`
- `/\ Len(st.chain) = 0`

Interpretation:

- This is bounded, constraint-scoped transfer diagnostics.
- It supports concrete-step to abstract-step/stutter alignment claims.
- It is not a closed unbounded refinement theorem by itself.
