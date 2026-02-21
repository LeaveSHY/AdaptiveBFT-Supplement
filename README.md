# AdaptiveBFT Formal Verification (TLA+)

This repository contains the complete security analysis and TLA+ formal verification of AdaptiveBFT protocol.

Paper appendices included in this repository:

- `APPENDIX A.pdf`: cryptographic security proof appendix for AdaptiveBFT.
- `APPENDIX B.pdf`: TLA+ Formal Specification and Verification appendix.

This repository is a reproducible AdaptiveBFT verification suite with:

- a feature-level executable TLA+ model for AVC + RVS + APS + pipelined consensus,
- explicit safety/liveness model-checking campaigns with TLC,
- an abstract theorem layer prepared for unbounded safety/liveness proof obligations.

Rendered TLA+ PDFs (e.g., `AdaptiveBFT_MainFlow.pdf`, `AdaptiveBFT_Types.pdf`,
`modules/AVC_RVS.pdf`, `modules/APS_Mempool.pdf`,
`AdaptiveBFT_Properties.pdf`, `modules/APS_Scheduler.pdf`, `AdaptiveBFT.pdf`)
are generated without page numbers by the Makefile typesetting pipeline.

The project is organized to support paper-grade claims with clear assumption boundaries.

For GitHub submission packaging and a final keep-file manifest, see:

- `docs/github_submission_manifest.md`
- `docs/final_repo_tree.txt`

## Claim Boundary and Roadmap

Before using any \"full correctness\" wording in a paper, read:

- `docs/claim_boundary.md` (what is currently proven vs not yet proven)
- `docs/proof_roadmap.md` (proof-obligation backlog and closure criteria)
- `docs/assumption_to_evidence_map.md` (assumption-by-assumption evidence map)
- `docs/reviewer_checklist.md` (reviewer-facing reproducibility and challenge checklist)
- `docs/submission_guide.md` (final submission handoff and upload checklist)

These files are the normative source for reviewer-facing claim scope and evidence interpretation.

## Formal Specification Layout

Core model:

- `specifications/AdaptiveBFT.tla`

Supporting modules:

- `specifications/AdaptiveBFT_Types.tla` (message/proposal/state typing)
- `specifications/modules/AVC_RVS.tla` (AVC control + RVS selection + decay update)
- `specifications/modules/RVS_CryptoAbstraction.tla` (weighted sortition strikes + verifiable witness abstraction)
- `specifications/modules/Reputation_Game.tla` (report aggregation and reputation game abstraction)
- `specifications/modules/APS_Scheduler.tla` (APS control-plane config/search)
- `specifications/modules/APS_DecoupledPipeline.tla` (dissemination/ordering/execution decoupling semantics)
- `specifications/modules/Mempool.tla` (pre-validation, recovery, queue abstraction)
- `specifications/modules/TLAPS.tla` (proof-backend pragmas used by theorem-track modules)
- `specifications/modules/FiniteSetTheorems.tla` (finite-set/cardinality lemmas used by quorum proofs)
- `specifications/modules/Functions.tla` (support dependency for finite-set theorem module)
- `specifications/modules/WellFoundedInduction.tla` (support dependency for finite-set theorem module)
- `specifications/modules/NaturalsInduction.tla` (support dependency for finite-set theorem module)

Property modules:

- `specifications/AdaptiveBFT_Properties.tla` (paper-facing safety/liveness property set)
- `specifications/AdaptiveBFT_Abstract.tla` (parameterized abstract protocol skeleton)
- `specifications/AdaptiveBFT_Invariant_Theorems.tla` (inductive invariant proof kernel for lock monotonicity)
- `specifications/AdaptiveBFT_Theorems.tla` (unbounded theorem statements and key lemmas)
- `specifications/AdaptiveBFT_Refinement.tla` (concrete-to-abstract projection/refinement bridge)
- `specifications/AdaptiveBFT_Refinement_Theorems.tla` (TLAPS-friendly refinement bridge theorems)
- `specifications/AdaptiveBFT_Refinement_Kernel.tla` (TLAPS-checked kernel summary over mapped refinement bridge)
- `specifications/AdaptiveBFT_Transfer_Kernel.tla` (TLAPS-checked transfer-closure subgoals over mapped spec envelope)
- `specifications/AdaptiveBFT_MainClaim_Theorems.tla` (TLAPS-checked top-level assumption-explicit correctness claim templates)
- `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla` (concrete-profile bridge lemmas over the projection layer)
- `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla` (concrete-state to mapped-theorem binding templates)
- `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla` (concrete-spec transfer closure templates)
- `specifications/AdaptiveBFT_Liveness_Theorems.tla` (assumption-explicit liveness theorem templates)

Model-checking wrappers:

- `models/MC_AdaptiveAttack.tla`
- `models/MC_LivenessAPS.tla`
- `models/MC_LivenessAPSAttack.tla`
- `models/MC_RefinementTransfer.tla` (concrete-step to abstract-step/stutter transfer diagnostics)

Configuration profiles:

- baseline (`MaxView=2`)
- mid-depth richer domain (`MaxView=3`): `*_MV3.cfg`
- strengthened depth (`MaxView=4`): `*_MV4.cfg`
- deepened depth (`MaxView=5`): `*_MV5.cfg`
- quick n=7 profile (`MaxView=1`): `*_N7LITE.cfg`

## Coverage: Protocol-to-Model Mapping

| AdaptiveBFT design element | Formalization location |
|---|---|
| `MinorMessage` / `FullMessage` / `TeProposal` / `VProposal` | `specifications/AdaptiveBFT_Types.tla` |
| TeProposal generation + full proposal recovery | `GenerateTentativeProposal`, `RecoverFullProposal` in `specifications/AdaptiveBFT.tla` |
| Pipeline stages `Prepare -> PreCommit -> Commit -> Decide` | `PrepareVote/PrepareQC`, `PreCommitVote/PreCommitQC`, `CommitVote/DecideBlock` in `specifications/AdaptiveBFT.tla` |
| AVC timeout trigger and synchronization | `Tick`, `CastTimeoutVote`, `StartViewChange`, `BroadcastNP`, `BroadcastSyn`, `CompleteViewChange` |
| RVS weighted sortition + witness validation | `RVSSelectPrimary`, `RVSPrimaryEvidence`, `RVSVerifyPrimary` in `specifications/modules/AVC_RVS.tla` + `specifications/modules/RVS_CryptoAbstraction.tla` |
| Reputation-game abstraction (report normalization / finite PageRank update / payoff-cost truthful utility) | `specifications/modules/Reputation_Game.tla` |
| APS control loop | `DetectAnomaly`, `SampleGrid`, `EstimateGrid`, `ExploreGrid`, `DeployConfig` |
| APS triple decoupling (dissemination/ordering/execution) | `DispatchToDissemination`, `PromoteToOrdering`, `PromoteToExecution` + `DecoupledPipelineSafety` |
| Mempool pre-validation + priority aging | `specifications/modules/Mempool.tla` |

## Checked Properties

Safety invariants checked by TLC (all three wrapper models):

1. `TypeOK`
2. `Consistency`
3. `NoForkPerView`
4. `PipelineBounded`
5. `QCLocked`
6. `QCViewSafety`
7. `MempoolSoundness`
8. `ProposalFlowSafety`
9. `ViewChangeMessageSafety`
10. `ChainParentSafety`
11. `PrimaryEligibilitySafety`
12. `ReconfigurationSafety`
13. `DecoupledPipelineSafety`

Aggregated paper-level safety:

- `Safety == SafetyProfile` in `specifications/AdaptiveBFT_Properties.tla`.

Temporal goals:

- `ConsensusLiveness == <> (Len(st.chain) >= 2)` in `models/MC_LivenessAPS.tla`
- `JointConsensusLiveness == <> (Len(st.chain) >= 2)` in `models/MC_LivenessAPSAttack.tla`
- `Liveness == <> (Len(st.chain) >= 2)` in `specifications/AdaptiveBFT_Properties.tla`

Wrapper-integrated transfer checks:

- `InitProjectionCheckedAttack`, `StepProjectionCheckedAttack`, `StepBoxProjectionCheckedAttack`, `SpecProjectionCheckedAttack`, `SpecToAbstractSpecCheckedAttack` in `models/MC_AdaptiveAttack.tla`
- `InitProjectionCheckedAPS`, `StepProjectionCheckedAPS`, `StepBoxProjectionCheckedAPS`, `SpecProjectionCheckedAPS`, `SpecToAbstractSpecCheckedAPS` in `models/MC_LivenessAPS.tla`
- `InitProjectionCheckedJoint`, `StepProjectionCheckedJoint`, `StepBoxProjectionCheckedJoint`, `SpecProjectionCheckedJoint`, `SpecToAbstractSpecCheckedJoint` in `models/MC_LivenessAPSAttack.tla`

Wrapper-level finite bridge diagnostics:

- `RefinementInvariantCoreAttack`, `SafetyBridgeFiniteAttack`, `CommitProjectionShapeAttack` in `models/MC_AdaptiveAttack.tla`
- `RefinementInvariantCoreAPS`, `SafetyBridgeFiniteAPS`, `CommitProjectionShapeAPS` in `models/MC_LivenessAPS.tla`
- `RefinementInvariantCoreJoint`, `SafetyBridgeFiniteJoint`, `CommitProjectionShapeJoint` in `models/MC_LivenessAPSAttack.tla`
- `RefinementInvariantCoreTransfer`, `SafetyBridgeFiniteTransfer`, `CommitProjectionShapeTransfer` in `models/MC_RefinementTransfer.tla`

Assumption structuring:

- fairness assumptions are explicit in `AssumptionsAPS` / `AssumptionsJoint`,
- TLC-executable assumptions are separated in `AssumptionsAPSForTLC` / `AssumptionsJointForTLC`,
- eventual-stability statements are documented as environment assumptions for liveness interpretation.

## Modeling Assumptions

1. Finite-domain bounded checking for executable TLC campaigns (`n=3f+1`, bounded views, bounded tx domain).
2. Cryptographic semantics are abstracted as weighted strike sortition over finite tickets with explicit witness verification.
3. Reputation game is abstracted to bounded report normalization, finite PageRank-style iteration, and payoff/cost-based truthful-report utilities.
4. APS search is finite and control-plane based.
5. Network and timer behavior is abstracted to symbolic conditions and stage timers.
6. Byzantine adaptation is bounded by `MaxAttackCount`.
7. Liveness claims are assumption-explicit (eventual stability + fairness), not assumption-free.
8. `MC_AdaptiveAttack` uses quorum-completion steps to collapse per-replica vote/ack interleavings (safety-preserving abstraction for tractable attack exploration).
9. The `n7` profile uses `TypeOKLite` (field-level scalable typing) instead of extensional `TypeOK` to avoid TLC set-construction blowups in large constructor domains.

## Reproducibility

Preconditions:

- Java 11+
- `tla2tools.jar` in repo root
- `bash`
- `pdflatex` for spec typesetting

Run baseline:

```bash
make all
```

Override runtime knobs (optional):

```bash
JAVA_OPTS="-Xmx10G -XX:+UseParallelGC" TLC_WORKERS=8 make test-attack
```

Resume an interrupted TLC run from checkpoint (optional):

```bash
bash ./run.sh joint mv3 models/states/<checkpoint-dir>
```

Run `MaxView=3` richer-domain profile:

```bash
make all-mv3
```

Run `MaxView=4` strengthened profile:

```bash
make all-mv4
```

Run `MaxView=5` deepened profile:

```bash
make all-mv5
```

Run scalable bounded sanity profile (`n=7`, `f=2`, `q=5`):

```bash
make all-n7
make all-n7-full    # optional, expensive
make all-n7lite     # quick MaxView=1 profile
```

Run n=7 scale snapshot export:

```bash
make scale-n7
make scale-n7lite
make scale-n7lite-full
```

Run refinement-transfer diagnostics:

```bash
make test-transfer
make test-transfer-mv3
make test-transfer-mv4
make test-transfer-mv5
```

Run one-shot `MaxView=5` full-suite snapshot (attack + APS + joint + transfer):

```bash
make suite-mv5
```

Run matrix and emit CSV:

```bash
make matrix
```

Run timeout-bounded matrix progress campaign (safe for long runs; records timeout rows to progress CSV without replacing synced matrix source):

```bash
make matrix-progress MODE_TIMEOUT_SEC=600
```

PowerShell equivalent:

```powershell
$env:MODE_TIMEOUT_SEC='600'; make matrix-progress
```

Run wrapper-integrated projection campaign and emit Markdown snapshot:

```bash
make wrapper-projection
```

Synchronize wrapper-projection LaTeX table rows with latest wrapper snapshot:

```bash
make sync-wrapper-table
```

Synchronize README/LaTeX n7/n7lite+transfer rows with latest snapshot artifacts:

```bash
make sync-snapshot-rows
```

Run wrapper campaign + table sync in one command:

```bash
make refresh-wrapper
```

Run the bundled reviewer-facing campaign in one shot:

```bash
make bundle
```

`make bundle` currently includes: gate, transfer (`baseline/mv3/mv4`), n=7 and
n=7lite scale snapshots, wrapper projection, a MaxView=5 full-suite run, the
automated safety-transfer closure-attempt campaign, and derived closure
taxonomy/trend artifacts.
By default it runs the full concrete TLAPS probe profile
(`PROBE_TIMEOUT_SEC=300`, `PROBE_TRANSFER_TIMEOUT_SEC=1200`);
override via `BUNDLE_CONCRETE_TLAPS_TIMEOUT_SEC` and
`BUNDLE_CONCRETE_TRANSFER_TIMEOUT_SEC`.

Run the one-command fastlane campaign (bundle core + appendix 5 figures + release dashboard):

```bash
make fastlane
make all-in-one
```

Check that README/LaTeX tables and wrapper+n7/n7lite+transfer snapshot artifacts are synchronized:

```bash
make check-sync
make check-bridge
make claim-check
```

Run the lightweight reviewer-facing quality gate (proofs + theorem coverage + artifact sync):

```bash
make gate
make gate-strong
```

`make gate-strong` extends `make gate` by also running
`make closure-attempt-safety`, `make closure-failure-taxonomy`,
`make closure-trend`, and `make release-status`.

Run theorem-track sanity checks (SANY for abstract/theorem/refinement modules):

```bash
make proofs
make proof-snapshot
make proof-blockers
make closure-attempt-safety
make closure-failure-taxonomy
make closure-trend
make check-theorem-coverage
```

Build a compact release dashboard from latest artifacts:

```bash
make release-status
```

Build a reviewer-facing submission RC summary from latest artifacts:

```bash
make submission-rc
```

Run the one-command submission-ready campaign (final sync + gates + RC summary):

```bash
make submission-ready
```

Build the upload manifest and zip package for artifact submission:

```bash
make submission-manifest
make submission-bundle
make check-submission
```

Run strict full submission-ready campaign (no gate/bundle reuse):

```bash
make submission-ready-full
```

Optional TLAPS refinement attempt (off by default):

```bash
TLAPS_REFINEMENT=1 make proofs
```

Optional fast SANY-only theorem gate (skip TLAPS backends):

```bash
SKIP_TLAPS=1 make proofs
```

Optional flaky-backend mitigation (retry TLAPS module checks):

```bash
TLAPS_RETRY=3 make proofs
```

Optional concrete-binding TLAPS check in the default proof track:

```bash
TLAPS_CONCRETE_BINDING=1 make proofs
```

Optional concrete-transfer TLAPS check in the default proof track (slow; default timeout 1200s):

```bash
TLAPS_CONCRETE_TRANSFER=1 make proofs
```

Concrete-track TLAPS diagnostics:

```bash
make concrete-tlaps-probe        # quick diagnostics (default per-module timeout 300s)
make concrete-tlaps-probe-full   # transfer-timeout override (default 1200s)
```

Typeset specs:

```bash
make list-pdf
make appendix-five-figs
```

## Latest TLC Results Snapshot (Measured/Rerun on 2026-02-19)

Machine:

- AMD Ryzen 7 7840H, 16 vCPUs, 15 GiB RAM, Linux (WSL2 Ubuntu), Java heap `-Xmx8G`.
- Worker policy: attack model uses 4 workers by default; liveness models use `-workers auto`.

Baseline (`MaxView=2`, `n=4`, `f=1`, `q=3`, `Tx={t1}`):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` | Safety under adaptive corruption | 15,045 | 4,366 | 49 | 5s |
| `MC_LivenessAPS` | APS liveness | 10,087 | 3,035 | 63 | <1s |
| `MC_LivenessAPSAttack` | Joint APS + adaptive attack liveness | 45,095 | 14,737 | 73 | 20s |

Deeper profile (`MaxView=3`, richer finite domain):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` | Safety under adaptive corruption | 5,936,703 | 1,196,611 | 69 | 7m39s |
| `MC_LivenessAPS` | APS liveness | 14,762,371 | 3,405,172 | 89 | 59m13s |
| `MC_LivenessAPSAttack` | Joint APS + adaptive attack liveness | 56,392,041 | 14,807,882 | 98 | 3h24m |

Strengthened profile (`MaxView=4`, other constants fixed):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` | Safety under adaptive corruption | 113,041 | 32,774 | 70 | 21s |
| `MC_LivenessAPS` | APS liveness | 16,791 | 5,047 | 97 | 39s |
| `MC_LivenessAPSAttack` | Joint APS + adaptive attack liveness | 104,191 | 33,269 | 106 | 55s |

n=7 scalability sanity snapshot (`MaxView=2`, `n=7`, `f=2`, `q=5`, bounded):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` (`n7`) | bounded scale sanity under adaptive corruption | 15,045 | 4,366 | 49 | 04min 50s |

n=7 quick-profile snapshot (`MaxView=1`, `n=7`, `f=2`, `q=5`, bounded):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` (`n7lite`) | quick bounded scale sanity under adaptive corruption | 5,009 | 1,454 | 39 | 03min 19s |

Notes for `n7`:

- this profile checks `TypeOKLite` plus the remaining safety invariants and projection diagnostics;
- `TypeOKLite` is a scalable field-level type check that avoids extensional membership in very large constructor sets (e.g., full `NPMessageType`).

Notes for `n7lite`:

- this quick profile keeps `n=7` and `q=5` but lowers `MaxView` to 1 for faster sanity runs;
- default `make scale-n7lite` executes attack-wrapper checks;
- `make scale-n7lite-full` executes attack + APS + joint + transfer in one snapshot (can be expensive);
- optional runtime bound (bash): `make scale-n7lite-full MODE_TIMEOUT_SEC=300`;
- optional runtime bound (PowerShell): `$env:MODE_TIMEOUT_SEC='300'; make scale-n7lite-full`;
- timed-out modes are recorded as `TIMEOUT`.

Refinement-transfer diagnostics (`InitProjectionChecked`, `StepProjectionChecked`,
`StepBoxProjectionChecked`, `SpecProjectionChecked`, `SpecToAbstractSpecChecked`,
with `TransferConstraint` enabled):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_RefinementTransfer` (baseline) | concrete `Next` projects to abstract `NextA` or stutter | 269,339 | 47,796 | 30 | 01min 10s |
| `MC_RefinementTransfer` (`MaxView=3`) | same transfer check, deeper bound | 269,339 | 47,796 | 30 | 01min 21s |
| `MC_RefinementTransfer` (`MaxView=4`) | same transfer check, strengthened bound | 269,339 | 47,796 | 30 | 01min 21s |

MaxView=5 deepened full-suite snapshot (`n=4`, `f=1`, `q=3`, bounded):

| Model | Purpose | States generated | Distinct states | Diameter | Wall-clock |
|---|---|---:|---:|---:|---:|
| `MC_AdaptiveAttack` (`MaxView=5`) | deeper bounded safety exploration | 299,733 | 86,886 | 80 | 01min 42s |
| `MC_LivenessAPS` (`MaxView=5`) | deeper bounded APS liveness wrapper | 20,143 | 6,053 | 115 | 01min 14s |
| `MC_LivenessAPSAttack` (`MaxView=5`) | deeper bounded joint liveness wrapper | 143,795 | 45,553 | 124 | 01min 39s |
| `MC_RefinementTransfer` (`MaxView=5`) | deeper bounded transfer diagnostics | 269,339 | 47,796 | 30 | 01min 27s |

Timeout-bounded matrix-progress snapshot (`MODE_TIMEOUT_SEC=600`, run date 2026-02-19):

| Profile | Attack | APS | Joint |
|---|---|---|---|
| `baseline` | `PASS (08s)` | `PASS (11s)` | `PASS (29s)` |
| `mv3` | `TIMEOUT (>600s)` | `TIMEOUT (>600s)` | `TIMEOUT (>600s)` |
| `mv4` | `PASS (54s)` | `PASS (40s)` | `PASS (01min 06s)` |

Matrix-progress source artifact:

- `docs/results/tlc_matrix_progress_latest.csv`

Observed outcome:

- No TLC-reported invariant violation.
- No TLC-reported temporal-property violation in liveness wrappers.
- No TLC-reported wrapper-level transfer-property violation
  (`InitProjectionChecked*` / `StepProjectionChecked*` / `StepBoxProjectionChecked*` / `SpecProjectionChecked*` / `SpecToAbstractSpecChecked*`).
- No TLC-reported transfer-property violation for
  `InitProjectionChecked`, `StepProjectionChecked`, `StepBoxProjectionChecked`, `SpecProjectionChecked`, and `SpecToAbstractSpecChecked`.

Interpretation boundary:

- These are bounded finite-domain model-checking results under explicit assumptions.
- This is not, by itself, a full unbounded theorem proof over all network sizes and adversary schedules.
- Reviewer-facing claim scope is frozen in `docs/claim_boundary.md`.

## Matrix Artifacts

Matrix runs generate:

- logs: `models/_matrix_<profile>_<model>.out`
- complete CSV summary (all PASS): `docs/results/tlc_matrix_<timestamp>.csv`
- timeout/incomplete progress CSV: `docs/results/tlc_matrix_progress_<timestamp>.csv`

Matrix summaries are written under:

- `docs/results/`
- latest matrix progress (if incomplete/timeout run): `docs/results/tlc_matrix_progress_latest.csv`
- wrapper transfer snapshot: `docs/results/wrapper_projection_snapshot_20260219.md`
- latest wrapper transfer snapshot: `docs/results/wrapper_projection_latest.md`
- proof-track snapshot: `docs/results/proof_snapshot_latest.md`
- theorem blocker snapshot: `docs/results/proof_blockers_latest.md`
- safety-transfer closure-attempt snapshot: `docs/results/safety_transfer_closure_attempt_latest.md`
- safety-transfer failure-taxonomy snapshot: `docs/results/safety_transfer_failure_taxonomy_latest.md`
- safety-transfer trend snapshot: `docs/results/safety_transfer_closure_trend_latest.md`
- safety-transfer goalpack snapshot: `docs/results/safety_transfer_goalpack_latest.md`
- wrapper table sync command: `make sync-wrapper-table` (updates `docs/verification_tables.tex` wrapper-projection rows from latest snapshot)
- latest transfer snapshot: `docs/results/transfer_snapshot_latest.md`
- MaxView=5 full-suite snapshot: `docs/results/mv5_suite_latest.md`
- n=7 scale snapshot: `docs/results/scale_n7_attack_latest.md`
- n=7 quick-profile snapshot: `docs/results/scale_n7lite_suite_latest.md`
- unified campaign snapshot: `docs/results/campaign_snapshot_latest.md`
- strong-claim campaign summary: `docs/results/strong_claim_bundle_latest.md`
- release dashboard: `docs/results/release_status_latest.md`
- submission RC summary: `docs/results/submission_rc_latest.md`
- submission artifact manifest: `docs/results/submission_artifact_manifest_latest.md`
- submission artifact bundle: `docs/results/submission_bundle_latest.zip`
- submission package check: `docs/results/submission_package_check_latest.md`
- submission-ready campaign summary: `docs/results/submission_ready_latest.md`
- fastlane campaign summary: `docs/results/fastlane_release_latest.md`
- day-1 sprint execution snapshot: `docs/results/day1_execution_latest.md`

## Paper Appendix Assets

- Formal-spec section template: `docs/formal_figures.tex`
- Verification tables: `docs/verification_tables.tex`
- Safe claim/repro paragraph snippet: `docs/paper_claim_text.tex`
- Five-figure split PDFs:
  - `AdaptiveBFT_MainFlow.pdf`
  - `AdaptiveBFT_Types.pdf`
  - `modules/AVC_RVS.pdf`
  - `modules/APS_Mempool.pdf`
  - `AdaptiveBFT_Properties.pdf`

## Unbounded-Theorem Track

Unbounded proof-facing artifacts are staged in:

- `specifications/AdaptiveBFT_Abstract.tla`
- `specifications/AdaptiveBFT_Invariant_Theorems.tla`
- `specifications/AdaptiveBFT_Theorems.tla`
- `specifications/AdaptiveBFT_Refinement.tla`
- `specifications/AdaptiveBFT_Refinement_Theorems.tla`
- `specifications/AdaptiveBFT_Refinement_Kernel.tla`
- `specifications/AdaptiveBFT_Transfer_Kernel.tla`
- `specifications/AdaptiveBFT_MainClaim_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteBridge_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteBinding_Theorems.tla`
- `specifications/AdaptiveBFT_ConcreteTransfer_Theorems.tla`
- `specifications/AdaptiveBFT_Liveness_Theorems.tla`

They provide:

- abstract protocol transitions and invariants (`SafetyA`, `LivenessA`),
- theorem statements (`AbstractSafetyTheorem`, `AbstractLivenessTheorem`),
- foundational lemmas (`QuorumMajority`, `QuorumIntersection`),
- a concrete-to-abstract projection (`ABSTRACT == INSTANCE AdaptiveBFT_Abstract WITH ...`),
- a TLAPS-friendly refinement bridge (`RefinementSafetyBridge`, `RefinementLivenessBridge`),
- concrete-profile bridge lemmas (`ConcreteSafetyToAbstractSafetyA`, `ConcreteProfileToRefinementInvariant`),
- concrete-binding pipeline templates (`ConcreteSafetyToMappedPipeline`, `ConcreteLivenessToMappedPipeline`),
- concrete-spec transfer templates (`InitToConcreteStateType`, `InitToAbstractInitEstablished`, `MappedStepToAbstractStepOrStutter`, `ConcreteSpecTransferDecompositionChecklist`, `ConcreteClosureChecklist`),
- mapped bridge pipeline theorems (`MappedSafetyPipeline`, `MappedLivenessPipeline`).

Executable check:

- `make proofs` (SANY parsing/linting + TLAPS proof checks for default theorem-track modules when `tlapm` is available).
- `make check-theorem-coverage` (enforces explicit allowlist tracking for intentionally unproved theorem declarations).
- `make proof-blockers` (materializes the currently allowlisted theorem blockers with file/line anchors).
- `make closure-attempt-safety` (runs automated proof-closure attempts for `AbstractSafetyTransferTemplate` and emits reproducible failure signatures).
- `make closure-attempt-safety` also emits a ranked goalpack (`docs/results/safety_transfer_goalpack_latest.md`) for targeted proof closure.
- `make closure-failure-taxonomy` (builds grouped failure signatures from the latest closure-attempt logs).
- `make closure-trend` (builds multi-campaign closure-attempt trend aggregates by strategy).
- If `tlapm` is installed, the same target runs TLAPS for `AdaptiveBFT_Invariant_Theorems.tla`.
- If `tlapm` is installed, the same target runs TLAPS for `AdaptiveBFT_Theorems.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_Refinement_Theorems.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_Refinement_Kernel.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_Transfer_Kernel.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_MainClaim_Theorems.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_Liveness_Theorems.tla`.
- The same target also runs TLAPS for `AdaptiveBFT_ConcreteBridge_Theorems.tla`.
- The same target runs SANY for `AdaptiveBFT_AbstractBridge_Theorems.tla`.
- The same target runs SANY for `AdaptiveBFT_ConcreteBinding_Theorems.tla`.
- The same target runs SANY for `AdaptiveBFT_ConcreteTransfer_Theorems.tla`.
- `make concrete-tlaps-probe` runs a non-blocking concrete TLAPS diagnostic campaign (`ConcreteBridge` + `ConcreteBinding` + `ConcreteTransfer`) with a quick timeout profile.
- `make concrete-tlaps-probe-full` runs the same campaign with a transfer-timeout override (`PROBE_TRANSFER_TIMEOUT_SEC`, default `1200`) and emits `docs/results/concrete_tlaps_probe_latest.md`.
- Set `SKIP_TLAPS=1` to run the same proof target in SANY-only mode (`make proofs SKIP_TLAPS=1`).
- Cross-shell fallback: `bash ./scripts/check_proof_track.sh 1`.
- Current TLAPS status in `AdaptiveBFT_Theorems.tla`:
  73 obligations discharged (including quorum-majority/intersection and arithmetic bridge lemmas `NatPlusOnePositive`, `GEAndGTImpliesGT`, `GTAndEqImpliesGT`, `QuorumCardLowerBound`, plus abstract safety closure over `NoForkA` and `LockMonotonicityA`, and liveness-template closure under `ProgressWitnessA`).
- Current TLAPS status in `AdaptiveBFT_Refinement_Theorems.tla`:
  54 obligations discharged (including mapped safety/liveness pipeline theorems and precommit-bridge obligations).
- Current TLAPS status in `AdaptiveBFT_Transfer_Kernel.tla`:
  22 obligations discharged (transfer-envelope closure subgoals and kernel checklist composition).
- Current TLAPS status in `AdaptiveBFT_MainClaim_Theorems.tla`:
  11 obligations discharged (assumption-envelope split and top-level safety/liveness claim templates).
- Current TLAPS status in `AdaptiveBFT_ConcreteBridge_Theorems.tla`:
  6 obligations discharged (concrete safety/liveness bridge reuse over the mapped abstract interface).
- Current SANY status in `AdaptiveBFT_AbstractBridge_Theorems.tla`:
  abstract-instance transfer templates parse/lint cleanly and remain tracked in the proof gate.
- Current SANY status in `AdaptiveBFT_ConcreteBinding_Theorems.tla`:
  concrete-to-mapped binding templates parse/lint cleanly over the full protocol model.
  In optional TLAPS mode (`TLAPS_CONCRETE_BINDING=1 make proofs`) and in the concrete probe,
  this module discharges 14 obligations (`docs/results/concrete_tlaps_probe_latest.md`).
- Current SANY status in `AdaptiveBFT_ConcreteTransfer_Theorems.tla`:
  concrete-spec transfer decomposition/closure templates parse/lint cleanly over the full protocol model.
  In optional TLAPS mode (`TLAPS_CONCRETE_TRANSFER=1 make proofs`) and in the full concrete probe profile
  (`make concrete-tlaps-probe-full`), this module discharges 10 obligations; in quick probe profile
  (`make concrete-tlaps-probe`) it may timeout due the reduced cap.
- Current TLAPS status in `AdaptiveBFT_Liveness_Theorems.tla`:
  10 obligations discharged (liveness-assumption decomposition and refinement-liveness transfer templates).
- Current TLAPS status in `AdaptiveBFT_Invariant_Theorems.tla`:
  120 obligations discharged (no-fork + lock-monotonicity induction kernel over `SpecA`).
- Current theorem coverage gate status (`make check-theorem-coverage`):
  `proved=91`, `allowlisted_unproved=0`; any new unproved theorem must be explicitly allowlisted (or proved) for gate pass.
- TLAPS on `AdaptiveBFT_Refinement.tla` is disabled by default because TLAPS 1.5.0
  does not robustly handle recursive operators imported from the full concrete model.
  Use `TLAPS_REFINEMENT=1 make proofs` for an experimental direct attempt.
  If that direct attempt fails, the proof command still reports the recursive-operator
  blocker and keeps the kernel refinement track machine-checked.

This separates executable TLC evidence from theorem-level proof obligations for TLAPS refinement.
Claim boundary: the current repository evidence is bounded model checking plus assumption-explicit theorem-track proof artifacts, and is not a closed full-concrete unbounded proof.

## Citation

```bibtex
@misc{AdaptiveBFT2026,
      title={AdaptiveBFT: Achieving Dual-Adaptability for Pipelined Consensus in Large-Scale Networks}, 
      author={Liang Wang and Liangmin Wang and Xia Feng and Haiqin Wu and Boris D?dder and Lu Liu},
      year={2026},
      publisher = {GitHub},
      howpublished = {\url{https://anonymous.4open.science/r/AdaptiveBFT-Supplement-TON}},
}
```
