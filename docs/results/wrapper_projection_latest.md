# Wrapper Projection Snapshot (20260221-020215)

Properties checked in wrappers:

- `InitProjectionCheckedAttack`, `StepProjectionCheckedAttack`, `StepBoxProjectionCheckedAttack`, `SpecProjectionCheckedAttack`
- `SpecToAbstractSpecCheckedAttack`
- `InitProjectionCheckedAPS`, `StepProjectionCheckedAPS`, `StepBoxProjectionCheckedAPS`, `SpecProjectionCheckedAPS`
- `SpecToAbstractSpecCheckedAPS`
- `InitProjectionCheckedJoint`, `StepProjectionCheckedJoint`, `StepBoxProjectionCheckedJoint`, `SpecProjectionCheckedJoint`
- `SpecToAbstractSpecCheckedJoint`

## baseline (MaxView=2)

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| `MC_AdaptiveAttack` | 15045 | 4366 | 49 | 11s | PASS |
| `MC_LivenessAPS` | 10087 | 3035 | 63 | 13s | PASS |
| `MC_LivenessAPSAttack` | 45095 | 14737 | 73 | 21s | PASS |

## mv4 (MaxView=4)

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| `MC_AdaptiveAttack` | 113041 | 32774 | 70 | 43s | PASS |
| `MC_LivenessAPS` | 16791 | 5047 | 98 | 39s | PASS |
| `MC_LivenessAPSAttack` | 104191 | 33269 | 107 | 01min 01s | PASS |
