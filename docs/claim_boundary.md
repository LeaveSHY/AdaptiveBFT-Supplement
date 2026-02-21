# AdaptiveBFT Formal-Verification Claim Boundary

Last updated: 2026-02-20

This document defines the exact boundary of what the repository **does** and **does not** prove.
It is the source of truth for paper wording, README wording, and artifact claims.

## 1) Claim Classes

We separate claims into three classes.

1. `C1` Machine-checked bounded model-checking claims (TLC).
2. `C2` Machine-checked theorem claims on abstract/refinement bridge modules (TLAPS/SANY).
3. `C3` Out-of-scope or future-work claims (must not be presented as proven).

## 2) Proven Claims (Current)

### C1: TLC bounded claims (proven)

Under finite configurations in `models/*.cfg`, TLC checks:

- Safety invariants `I1..I13` (`TypeOK`, `Consistency`, `NoForkPerView`, `PipelineBounded`, `QCLocked`, `QCViewSafety`, `MempoolSoundness`, `ProposalFlowSafety`, `ViewChangeMessageSafety`, `ChainParentSafety`, `PrimaryEligibilitySafety`, `ReconfigurationSafety`, `DecoupledPipelineSafety`).
  - For the `n7` scalability profile, `TypeOK` is replaced by `TypeOKLite`
    (field-level scalable typing) to avoid TLC extensional set-construction
    limits in large constructor domains.
- Liveness targets in wrappers:
  - `ConsensusLiveness == <> (Len(st.chain) >= 2)`
  - `JointConsensusLiveness == <> (Len(st.chain) >= 2)`
- Wrapper-integrated transfer diagnostics:
  - `InitProjectionCheckedAttack`, `StepProjectionCheckedAttack`, `StepBoxProjectionCheckedAttack`, `SpecProjectionCheckedAttack`, `SpecToAbstractSpecCheckedAttack`
  - `InitProjectionCheckedAPS`, `StepProjectionCheckedAPS`, `StepBoxProjectionCheckedAPS`, `SpecProjectionCheckedAPS`, `SpecToAbstractSpecCheckedAPS`
  - `InitProjectionCheckedJoint`, `StepProjectionCheckedJoint`, `StepBoxProjectionCheckedJoint`, `SpecProjectionCheckedJoint`, `SpecToAbstractSpecCheckedJoint`
- Wrapper-level finite bridge diagnostics:
  - `RefinementInvariantCoreAttack`, `SafetyBridgeFiniteAttack`, `CommitProjectionShapeAttack`
  - `RefinementInvariantCoreAPS`, `SafetyBridgeFiniteAPS`, `CommitProjectionShapeAPS`
  - `RefinementInvariantCoreJoint`, `SafetyBridgeFiniteJoint`, `CommitProjectionShapeJoint`
  - `RefinementInvariantCoreTransfer`, `SafetyBridgeFiniteTransfer`, `CommitProjectionShapeTransfer`
- Concrete-to-abstract step-transfer diagnostics:
  - `InitProjectionChecked == InitProjectionOK`
  - `StepProjectionChecked == [][StepProjectionOK]_vars`
  - `StepBoxProjectionChecked == [][StepBoxProjectionOK]_vars`
  - `SpecProjectionChecked == InitProjectionOK /\ StepBoxProjectionChecked`
  - `SpecToAbstractSpecChecked == SpecProjectionChecked` (TLC-safe proxy)

Evidence location:

- TLC wrappers: `models/MC_AdaptiveAttack.tla`, `models/MC_LivenessAPS.tla`, `models/MC_LivenessAPSAttack.tla`
- Transfer wrapper: `models/MC_RefinementTransfer.tla` with `models/MC_RefinementTransfer*.cfg`
- Latest matrix: `docs/results/tlc_matrix_20260215-105849.csv`
- Latest transfer snapshot: `docs/results/transfer_snapshot_latest.md`
- Paper tables: `docs/verification_tables.tex`
- Wrapper transfer snapshot: `docs/results/wrapper_projection_snapshot_20260218.md`
- Latest wrapper transfer snapshot: `docs/results/wrapper_projection_latest.md`
- Bridge-wiring gate: `scripts/check_bridge_invariants.py`
- Proof-track snapshot: `docs/results/proof_snapshot_latest.md`
- n=7 scalability sanity snapshot: `docs/results/scale_n7_attack_latest.md`
- n=7 quick-profile snapshot (`MaxView=1`): `docs/results/scale_n7lite_suite_latest.md`
- MaxView=5 deepened full-suite snapshot: `docs/results/mv5_suite_latest.md`
- Unified campaign snapshot: `docs/results/campaign_snapshot_latest.md`
- Strong-claim campaign bundle summary: `docs/results/strong_claim_bundle_latest.md`
- Release dashboard: `docs/results/release_status_latest.md`
- Transfer snapshot and run commands: `README.md` ("Latest TLC Results Snapshot")

### C2: theorem-track claims (partially proven, assumption-explicit)

Machine-checked (TLAPS/SANY) theorem modules currently provide:

- Abstract theorem statements:
  - `AbstractSafetyTheorem`: `(SpecA => []SafetyA)` (TLAPS-discharged)
  - `AbstractLivenessTheorem`: `((SpecA /\ LivenessAssumptionsA) => LivenessA)` (TLAPS-discharged under explicit `ProgressWitnessA` assumption in the abstract liveness envelope)
- Quorum lemmas, including intersection.
- Refinement bridge templates with explicit init/step mapping obligations.
- Inductive invariant safety kernel over the abstract lock discipline (`AbstractLockSafetyByInduction` in `AdaptiveBFT_Invariant_Theorems.tla`), TLAPS-discharged.
- Mapped bridge pipeline theorems combining abstract transfer with projected
  safety/liveness goals (`MappedSafetyPipeline`, `MappedLivenessPipeline`).
- Refinement-kernel checklist theorems over the mapped bridge
  (`KernelInitToAbstractInit`, `KernelStepToAbstractStepOrStutter`,
  `KernelEndToEndChecklist`).
- Assumption-explicit liveness theorem templates over the refinement layer.
- Concrete-profile bridge lemmas over the projection layer
  (`ConcreteSafetyToAbstractSafetyA`, `ConcreteTwoCommitsToAbstractLiveness`,
  `ConcreteProfileToRefinementInvariant`), TLAPS-checked.
- Concrete-to-mapped binding templates over `st`-projected state
  (`ConcreteSafetyToMappedPipeline`, `ConcreteLivenessToMappedPipeline`,
  `ConcreteProfilePipelineSummary`), SANY-checked in default gate and
  TLAPS-probe checked (`docs/results/concrete_tlaps_probe_latest.md`).
- Concrete-spec transfer closure templates
  (`InitToConcreteStateType`, `InitToAbstractInitEstablished`,
  `MappedStepToAbstractStepOrStutter`,
  `ConcreteSpecTransferDecompositionChecklist`,
  `ConcreteSafetyClosureTemplate`, `ConcreteClosureChecklist`), SANY-checked in default gate;
  TLAPS-probe checked in the extended-timeout concrete profile
  (`make concrete-tlaps-probe-full`).

Evidence location:

- `specifications/AdaptiveBFT_Theorems.tla`
- `specifications/AdaptiveBFT_Invariant_Theorems.tla`
- `specifications/AdaptiveBFT_Refinement_Theorems.tla`
- `specifications/AdaptiveBFT_Refinement_Kernel.tla`
- `specifications/AdaptiveBFT_Transfer_Kernel.tla`
- `specifications/AdaptiveBFT_MainClaim_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla`
- `specifications/AdaptiveBFT_Liveness_Theorems.tla`
- `scripts/check_proof_track.sh`
- `scripts/run_concrete_tlaps_probe.py`
- `scripts/check_theorem_coverage.py`
- `scripts/build_proof_blockers.py`
- `docs/results/proof_blockers_latest.md`
- `docs/results/concrete_tlaps_probe_latest.md`

## 3) Assumption Envelope (Must Be Explicit)

All liveness claims are assumption-explicit.

- Eventual stability / partial synchrony abstraction (`<>[] Stable`).
- Fairness assumptions (`WF`/`SF`) in liveness wrappers.
- Bounded adaptive corruption in attack wrappers (`MaxAttackCount`).
- Symbolic cryptographic abstraction for RVS/VRF.
- Finite-domain abstraction for TLC campaigns.

Representative definitions:

- `models/MC_LivenessAPS.tla` (`AssumptionsAPS`, `AssumptionsAPSForTLC`)
- `models/MC_LivenessAPSAttack.tla` (`AssumptionsJoint`, `AssumptionsJointForTLC`)
- `specifications/modules/RVS_CryptoAbstraction.tla`

## 4) Non-Claims (Must Not Be Stated As Proven Yet)

The repository does **not yet** establish the following as completed machine proofs:

1. Full unbounded end-to-end concrete proof `SpecConcrete => []Safety` for all protocol detail layers in one closed TLAPS chain.
2. Full unbounded end-to-end concrete liveness proof without explicit environment assumptions.
3. Cryptographic hardness proofs for VRF/NIZK primitives (only symbolic abstraction is modeled).
4. Performance/scalability theorem proofs (throughput/latency are empirical, not theorem obligations).

## 5) Paper Wording Policy

Use these wording templates:

- Allowed:
  - "We prove safety/liveness in an assumption-explicit abstract/refinement theorem track and validate bounded concrete executions with TLC."
  - "TLC exhaustively checks all reachable states under finite configurations."
  - "Concrete-to-abstract step-transfer conditions are additionally checked by a bounded transfer wrapper."
- Not allowed:
  - "We unconditionally prove the full concrete protocol for all network schedules."
  - "We cryptographically prove VRF/NIZK security in this model."

## 6) Decision Rule For Strong Claims

A strong claim "full protocol unbounded correctness" is allowed only when all three conditions hold:

1. Concrete-to-abstract refinement proof is closed (init + next/simulation + property transfer).
2. Safety theorem over concrete spec is machine-checked end-to-end.
3. Liveness theorem over concrete spec is machine-checked end-to-end under explicitly stated assumptions.

Until then, the strongest valid statement is:

"bounded concrete model-checking + assumption-explicit theorem track evidence."
