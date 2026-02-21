# AdaptiveBFT Reviewer Checklist (Submission RC)

Last updated: 2026-02-20

This checklist is designed for artifact evaluation and security-review rebuttal prep.

## 1) Scope Integrity

- [ ] Claim boundary matches repository evidence (`docs/claim_boundary.md`).
- [ ] README wording does not exceed bounded + assumption-explicit scope.
- [ ] Paper tables (`docs/verification_tables.tex`) and README snapshots are synchronized.

Run:

```bash
make claim-check
make check-sync
```

Expected: both commands return PASS.

## 2) Proof/Model Gate

- [ ] Theorem-track gate passes.
- [ ] Concrete TLAPS probe passes.
- [ ] Closure taxonomy/trend artifacts are regenerated.

Run:

```bash
make gate-strong
```

Expected: PASS, and latest artifacts are refreshed under `docs/results/`.

## 3) Full Campaign Reproducibility

- [ ] End-to-end bundle succeeds.
- [ ] Release dashboard summarizes all required outputs.
- [ ] Fastlane campaign succeeds (with graceful PDF skip if `pdflatex` absent).
- [ ] Submission manifest and upload bundle are generated.

Run:

```bash
make bundle
make release-status
make fastlane FASTLANE_SKIP_BUNDLE=1
make submission-manifest
make submission-bundle
make check-submission
```

Expected:

- `docs/results/strong_claim_bundle_latest.md`: overall PASS.
- `docs/results/release_status_latest.md`: scope + table + proof summary present.
- `docs/results/fastlane_release_latest.md`: PASS.
- `docs/results/submission_artifact_manifest_latest.md`: required artifacts complete.
- `docs/results/submission_bundle_latest.zip`: upload-ready package.
- `docs/results/submission_package_check_latest.md`: package integrity checks pass.

## 4) Core Safety/Liveness Checks

- [ ] Safety invariants (I1-I13) pass in wrapper models.
- [ ] Liveness wrappers pass under explicit assumptions.
- [ ] Wrapper-integrated transfer properties pass.

Primary evidence:

- `docs/results/release_status_latest.md`
- `docs/results/wrapper_projection_latest.md`
- `docs/results/mv5_suite_latest.md`

## 5) Scale/Depth Sanity

- [ ] MaxView=5 suite exists and passes.
- [ ] n=7/n7lite bounded scale artifacts are present and correctly interpreted.

Primary evidence:

- `docs/results/mv5_suite_latest.md`
- `docs/results/scale_n7_attack_latest.md`
- `docs/results/scale_n7lite_suite_latest.md`
- `docs/results/scale_n7lite_full_suite_latest.md`

Note: n7lite timeout rows are acceptable and must be labeled as TIMEOUT, not PASS.

## 6) Assumption Traceability

- [ ] Each assumption has a formal definition location.
- [ ] Each assumption has at least one machine-checkable artifact.

Reference:

- `docs/assumption_to_evidence_map.md`

## 7) Reviewer Challenge Matrix

1. Challenge: "You over-claim full unbounded concrete proof."
Answer path: `docs/claim_boundary.md` + scope line in `docs/results/release_status_latest.md`.

2. Challenge: "Liveness assumptions are hidden."
Answer path: `models/MC_LivenessAPS.tla`, `models/MC_LivenessAPSAttack.tla`, `specifications/AdaptiveBFT_Liveness_Theorems.tla`.

3. Challenge: "Concrete/abstract link is not machine-checked."
Answer path: `docs/results/wrapper_projection_latest.md`, `docs/results/concrete_tlaps_probe_latest.md`, `docs/results/proof_snapshot_latest.md`.

4. Challenge: "Results table is stale/inconsistent."
Answer path: run `make check-sync` and show PASS.

## 8) Release Candidate Exit Criteria

- [ ] `make gate-strong` PASS
- [ ] `make bundle` PASS
- [ ] `make release-status` PASS
- [ ] `make fastlane FASTLANE_SKIP_BUNDLE=1` PASS
- [ ] `make check-submission` PASS
- [ ] `make claim-check` PASS
- [ ] `make check-sync` PASS

If all six are green, this repository is at the strongest submission-ready bounded-verification state.
