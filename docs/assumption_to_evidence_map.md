# AdaptiveBFT Assumption-to-Evidence Map

Last updated: 2026-02-20

This document maps each reviewer-relevant assumption to machine-checked artifacts.

## A1. Finite-domain bounded checking

- Assumption: TLC campaigns are finite (`n=3f+1`, bounded `MaxView`, bounded tx domain).
- Formal location: `models/*.cfg` (e.g., `models/MC_LivenessAPS.cfg`).
- Evidence:
  - `docs/results/release_status_latest.md` (bundle and model outcomes).
  - `docs/verification_tables.tex` (paper-facing summary table).

## A2. Eventual synchrony and fairness for liveness

- Assumption: liveness is checked under explicit fairness/eventual-stability envelope.
- Formal location:
  - `models/MC_LivenessAPS.tla` (`AssumptionsAPS`, `AssumptionsAPSForTLC`).
  - `models/MC_LivenessAPSAttack.tla` (`AssumptionsJoint`, `AssumptionsJointForTLC`).
  - `specifications/AdaptiveBFT_Liveness_Theorems.tla`.
- Evidence:
  - TLC liveness properties in wrapper configs (`PROPERTY ConsensusLiveness`, `PROPERTY JointConsensusLiveness`).
  - theorem-track liveness obligations in `docs/results/proof_snapshot_latest.md`.

## A3. Bounded adaptive adversary

- Assumption: adaptive corruption is bounded (`MaxAttackCount`).
- Formal location: attack wrappers/configs (`models/MC_AdaptiveAttack*.tla`, `models/MC_*Attack*.cfg`).
- Evidence:
  - safety/liveness under attack profiles in `docs/results/release_status_latest.md`.
  - bundle step status in `docs/results/strong_claim_bundle_latest.md`.

## A4. Symbolic cryptographic abstraction (RVS/VRF)

- Assumption: cryptographic hardness is abstracted symbolically.
- Formal location:
  - `specifications/modules/RVS_CryptoAbstraction.tla`.
  - `specifications/modules/AVC_RVS.tla`.
- Evidence:
  - typed/symbolic checks via SANY/TLAPS in `docs/results/proof_snapshot_latest.md`.
  - bounded protocol executions in TLC wrappers (no invariant/liveness violations reported).

## A5. Reputation-game abstraction

- Assumption: reputation game/PageRank/payoff are finite-domain abstractions.
- Formal location: `specifications/modules/Reputation_Game.tla`.
- Evidence:
  - theorem-track parse/proof checks in `docs/results/proof_snapshot_latest.md`.
  - integration evidence through wrapper-level invariants and transfer diagnostics in `docs/results/wrapper_projection_latest.md`.

## A6. APS control-plane finite abstraction

- Assumption: APS control loop is finite and tractable.
- Formal location:
  - `specifications/modules/APS_Scheduler.tla`.
  - `specifications/modules/APS_DecoupledPipeline.tla`.
- Evidence:
  - `DecoupledPipelineSafety` and liveness wrappers pass in release dashboard.
  - `docs/results/release_status_latest.md`, `docs/results/mv5_suite_latest.md`.

## A7. Concrete-to-abstract transfer envelope

- Assumption: transfer chain is modeled as explicit theorem obligations/templates.
- Formal location:
  - `specifications/AdaptiveBFT_Refinement_Theorems.tla`.
  - `specifications/AdaptiveBFT_Transfer_Kernel.tla`.
  - `specifications/AdaptiveBFT_MainClaim_Theorems.tla`.
  - `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`.
  - `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla`.
- Evidence:
  - TLAPS/SANY status in `docs/results/proof_snapshot_latest.md`.
  - concrete probe status in `docs/results/concrete_tlaps_probe_latest.md`.
  - wrapper transfer checks in `docs/results/wrapper_projection_latest.md`.

## A8. Claim boundary (what is not claimed as fully closed)

- Assumption boundary: not a closed full-concrete unbounded proof yet.
- Formal location: `docs/claim_boundary.md`.
- Evidence:
  - release dashboard scope line in `docs/results/release_status_latest.md`.
  - explicit non-claims in `docs/claim_boundary.md`.

## Reviewer Guidance

- Run `make gate-strong` and `make bundle` for full campaign.
- Run `make claim-check` and `make check-sync` for wording/table consistency gates.
- Treat `docs/claim_boundary.md` as the authoritative interpretation boundary.
