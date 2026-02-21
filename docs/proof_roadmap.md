# AdaptiveBFT Unbounded-Proof Roadmap

Last updated: 2026-02-18

This document is the executable roadmap to upgrade from bounded TLC evidence to
submission-grade parameterized theorem evidence.

## 1) End Goal

Deliver a machine-checkable proof chain supporting:

- `Safety_main`: `SpecConcrete => []Safety`
- `Liveness_main`: `(SpecConcrete /\ Assumptions) => Liveness`

with `Assumptions` explicitly listed (partial synchrony/fairness/adversary bound/symbolic crypto model).

## 2) Proof Architecture

1. Concrete protocol model:
   - `specifications/AdaptiveBFT.tla`
2. Abstract proof model:
   - `specifications/AdaptiveBFT_Abstract.tla`
   - `specifications/AdaptiveBFT_Invariant_Theorems.tla`
   - `specifications/AdaptiveBFT_Theorems.tla`
3. Refinement bridge:
   - `specifications/AdaptiveBFT_Refinement.tla`
   - `specifications/AdaptiveBFT_Refinement_Theorems.tla`
   - `specifications/AdaptiveBFT_Refinement_Kernel.tla`
   - `specifications/AdaptiveBFT_Transfer_Kernel.tla`
   - `specifications/AdaptiveBFT_MainClaim_Theorems.tla`
   - `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla`
   - `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`
   - `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla`
4. Liveness theorem layer:
   - `specifications/AdaptiveBFT_Liveness_Theorems.tla`

## 3) Dependency Graph (Proof-Level)

1. Quorum arithmetic and intersection lemmas.
2. Abstract safety/liveness invariants.
3. Concrete->abstract projection invariants.
4. Refinement bridge (init + step/simulation).
5. Transfer theorems (concrete safety/liveness from abstract).

## 4) Obligation Backlog (Actionable)

| ID | Obligation | File | Status | Notes |
|---|---|---|---|---|
| O1 | Quorum majority/intersection lemmas | `specifications/AdaptiveBFT_Theorems.tla` | Completed | TLAPS discharge included in `make proofs`. |
| O2 | Abstract safety theorem closure | `specifications/AdaptiveBFT_Theorems.tla` | Completed | `AbstractSafetyTheorem` is TLAPS-discharged (73 obligations total in module after adding NoFork+lock closure and liveness-template closure step). |
| O3 | Abstract liveness theorem closure | `specifications/AdaptiveBFT_Theorems.tla` | Completed | `AbstractLivenessTheorem` is TLAPS-discharged under the explicit assumption envelope (`LivenessAssumptionsA`, including `ProgressWitnessA`). |
| O4 | Concrete projection invariant strengthening | `specifications/AdaptiveBFT_Refinement.tla`, `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla` | In progress | Added concrete-profile bridge lemmas and SANY gate; TLAPS over full concrete recursion remains blocked. |
| O5 | Refinement safety bridge closure | `specifications/AdaptiveBFT_Refinement_Theorems.tla`, `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`, `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla` | In progress | Mapped safety theorem discharged; transfer layer discharges concrete init-to-abstract-init bridge and now has TLC-backed step-projection diagnostics. |
| O6 | Refinement liveness bridge closure | `specifications/AdaptiveBFT_Refinement_Theorems.tla`, `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`, `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla` | In progress | Mapped liveness theorem discharged; concrete transfer/liveness closure templates SANY-gated; concrete assumption instantiation still pending. |
| O7 | Concrete liveness theorem track | `specifications/AdaptiveBFT_Liveness_Theorems.tla`, `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla` | In progress | Assumption decomposition + refinement template discharged; concrete closure checklist theorem added; full concrete `Spec` binding pending. |
| O8 | Claim/report synchronization checks | `scripts/check_tables_sync.py` | Completed | `make check-sync` enforces matrix/table consistency. |
| O9 | Concrete-to-abstract projection diagnostics | `models/MC_RefinementTransfer.tla`, `models/MC_RefinementTransfer*.cfg`, main wrapper models | Completed | Dedicated transfer properties (`InitProjectionChecked`, `StepProjectionChecked`, `StepBoxProjectionChecked`, `SpecProjectionChecked`, `SpecToAbstractSpecChecked`) pass in baseline/`MaxView=3`/`MaxView=4`; wrapper-integrated projection properties (`InitProjectionChecked*`, `StepProjectionChecked*`, `StepBoxProjectionChecked*`, `SpecProjectionChecked*`, `SpecToAbstractSpecChecked*`) pass in baseline and `MaxView=4`, and remain passing in the `MaxView=5` full-suite wrappers. |
| O10 | Explicit theorem coverage guard | `scripts/check_theorem_coverage.py` | Completed | Gate now fails if a new unproved theorem is added without allowlist entry or proof. |
| O11 | Proof-blocker dashboard artifact | `scripts/build_proof_blockers.py` | Completed | `make proof-blockers` emits `docs/results/proof_blockers_latest.md` with file/line anchors for allowlisted theorem blockers. |
| O12 | Safety-transfer closure-attempt campaign | `scripts/run_safety_transfer_closure_attempt.py` | Completed | `make closure-attempt-safety` emits `docs/results/safety_transfer_closure_attempt_latest.md` with reproducible candidate-proof failure signatures and restore checks. |
| O13 | Safety-transfer failure taxonomy artifact | `scripts/build_safety_transfer_failure_taxonomy.py` | Completed | `make closure-failure-taxonomy` emits `docs/results/safety_transfer_failure_taxonomy_latest.md` with grouped failing-goal signatures across strategies. |
| O14 | Safety-transfer trend artifact | `scripts/build_safety_transfer_closure_trend.py` | Completed | `make closure-trend` emits `docs/results/safety_transfer_closure_trend_latest.md` with per-strategy pass/fail history across campaigns. |
| O15 | Safety-transfer goalpack artifact | `scripts/run_safety_transfer_closure_attempt.py` | Completed | `make closure-attempt-safety` also emits `docs/results/safety_transfer_goalpack_latest.md` with ranked unproved goals and tactic worklist. |

## 5) Week-1 Deliverables (Current Sprint)

1. Freeze claim boundary (`docs/claim_boundary.md`).
2. Strengthen refinement obligations to simulation-friendly form.
3. Keep TLC matrix reproducible and synchronized with paper tables.
4. Keep theorem-track command stable:
   - `make proofs`
   - `TLAPS_REFINEMENT=1 make proofs`

## 6) Current Machine-Checked Snapshot

- `specifications/AdaptiveBFT_Theorems.tla`: 73 obligations discharged.
- `specifications/AdaptiveBFT_Invariant_Theorems.tla`: 120 obligations discharged.
- `specifications/AdaptiveBFT_Refinement_Theorems.tla`: 54 obligations discharged.
- `specifications/AdaptiveBFT_Refinement_Kernel.tla`: 17 obligations discharged (kernel checklist over mapped refinement bridge).
- `specifications/AdaptiveBFT_Transfer_Kernel.tla`: 22 obligations discharged for transfer-envelope closure subgoals.
- `specifications/AdaptiveBFT_MainClaim_Theorems.tla`: 11 obligations discharged for assumption-envelope split and top-level claim templates.
- `specifications/AdaptiveBFT_Liveness_Theorems.tla`: 10 obligations discharged.
- `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla`: SANY parse/lint gated in `make proofs` (TLAPS skipped by design).
- `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`: SANY parse/lint gated in `make proofs` (TLAPS skipped by design).
- `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla`: SANY parse/lint gated in `make proofs` (TLAPS skipped by design).
- theorem coverage gate (`make check-theorem-coverage`): `proved=91`, `allowlisted_unproved=0`.
- theorem blocker snapshot (`make proof-blockers`): `docs/results/proof_blockers_latest.md`.
- safety-transfer closure trend (`make closure-trend`): `docs/results/safety_transfer_closure_trend_latest.md`.
- safety-transfer goalpack (`make closure-attempt-safety`): `docs/results/safety_transfer_goalpack_latest.md`.
- `models/MC_RefinementTransfer.tla`: transfer properties pass with
  `269,339` generated / `47,796` distinct / diameter `30` in all three
  checked profiles (`baseline`, `mv3`, `mv4`), under `TransferConstraint`.
- Wrapper-integrated transfer checks pass in
  `MC_AdaptiveAttack`, `MC_LivenessAPS`, and `MC_LivenessAPSAttack`
  (see `docs/results/wrapper_projection_snapshot_20260218.md`).
- `docs/results/mv5_suite_latest.md`: deepened full-suite wrappers + transfer pass
  at `MaxView=5` (`MC_AdaptiveAttack`, `MC_LivenessAPS`,
  `MC_LivenessAPSAttack`, `MC_RefinementTransfer`).
- Wrapper-level finite bridge diagnostics
  (`RefinementInvariantCore*`, `SafetyBridgeFinite*`, `CommitProjectionShape*`)
  are wired into all wrapper/transfer cfg profiles and pass in baseline and
  `MaxView=4` wrapper campaigns.

These counts are validated by `bash ./scripts/check_proof_track.sh 1`
and TLAPS module runs on 2026-02-18, and should be treated
as CI-style guardrails; a drop indicates theorem-track regression.

Note on `TLAPS_REFINEMENT=1`:
- direct TLAPS on `AdaptiveBFT_Refinement.tla` remains experimental and can fail
  because TLAPS 1.5.0 does not support recursive operators in the imported
  concrete dependency graph;
- this does not bypass proof checking: `AdaptiveBFT_Refinement_Kernel.tla`
  stays TLAPS-checked in the default theorem track.

## 7) Acceptance Criteria For "Strong" Claim

The repository may state "full protocol unbounded correctness (assumption-explicit)"
only when all hold:

1. Refinement obligations cover init + next (or stuttering simulation) end-to-end.
2. Safety transfer theorem from concrete to abstract is fully machine-checked.
3. Liveness transfer theorem from concrete to abstract is fully machine-checked.
4. Claim wording in README/paper matches `docs/claim_boundary.md` exactly.

## 8) Reproducibility Commands

1. `make proofs`
2. `TLAPS_REFINEMENT=1 make proofs`
3. `SKIP_TLAPS=1 make proofs`
4. `make proof-snapshot`
5. `make matrix`
6. `make test-transfer`
7. `make test-transfer-mv3`
8. `make test-transfer-mv4`
9. `make wrapper-projection`
10. `make sync-wrapper-table`
11. `make sync-snapshot-rows`
12. `make scale-n7lite`
13. `python scripts/check_tables_sync.py`
14. `make claim-check`
15. `make check-bridge`
16. `make gate`
17. `make check-theorem-coverage`
18. `make bundle`
19. `make release-status`
20. `make fastlane`
21. `make closure-attempt-safety`
22. `make gate-strong`
23. `make closure-failure-taxonomy`
24. `make closure-trend`

If any command fails, strong claims are blocked until fixed.
