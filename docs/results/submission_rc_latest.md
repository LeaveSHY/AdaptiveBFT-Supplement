# Submission RC Summary

- generated: 2026-02-21 02:17:03 +0800
- intent: reviewer-defensible strongest bounded-verification release
- release status: PASS
- fastlane status: PASS
- artifact completeness gate: PASS
- scope: bounded TLC evidence + assumption-explicit theorem track
- claim boundary: not a closed full-concrete unbounded proof

## Paper Claim Text (Safe)

Under explicit assumptions (bounded domain, symbolic cryptography, bounded adaptive adversary, and eventual-synchrony/fairness envelope), AdaptiveBFT safety and liveness properties are systematically validated by reproducible bounded model checking and machine-checked theorem-track artifacts.

## Repro Commands (Submission Path)

```bash
make gate-strong
make bundle
make release-status
make fastlane FASTLANE_SKIP_BUNDLE=1
make claim-check
make check-sync
```

## Artifact Manifest

| Artifact | Required | Exists | Notes |
|---|---|---|---|
| `README.md` | yes | yes | Top-level narrative and reproducibility commands. |
| `docs/claim_boundary.md` | yes | yes | Normative claim boundary. |
| `docs/proof_roadmap.md` | yes | yes | Proof-obligation roadmap and closure criteria. |
| `docs/assumption_to_evidence_map.md` | yes | yes | Assumption-to-evidence traceability. |
| `docs/reviewer_checklist.md` | yes | yes | Reviewer challenge/repro checklist. |
| `docs/submission_guide.md` | yes | yes | Submission handoff and upload checklist. |
| `docs/formal_figures.tex` | yes | yes | Paper appendix formal-spec section. |
| `docs/verification_tables.tex` | yes | yes | Paper tables for settings/results. |
| `docs/paper_claim_text.tex` | yes | yes | Safe paper claim/repro paragraph snippet. |
| `docs/results/release_status_latest.md` | yes | yes | Release dashboard. |
| `docs/results/submission_artifact_manifest_latest.md` | yes | yes | Integrity manifest with hashes. |
| `docs/results/submission_bundle_latest.zip` | yes | yes | Upload-ready artifact bundle. |
| `docs/results/strong_claim_bundle_latest.md` | yes | yes | Bundle campaign summary. |
| `docs/results/fastlane_release_latest.md` | yes | yes | One-command release campaign summary. |
| `docs/results/proof_snapshot_latest.md` | yes | yes | Theorem-track snapshot. |
| `docs/results/concrete_tlaps_probe_latest.md` | yes | yes | Concrete TLAPS diagnostics. |
| `docs/results/mv5_suite_latest.md` | yes | yes | Deep bounded suite snapshot. |
| `docs/results/wrapper_projection_latest.md` | yes | yes | Wrapper transfer checks. |
| `docs/results/scale_n7_attack_latest.md` | no | yes | Optional scale sanity artifact. |
| `docs/results/scale_n7lite_suite_latest.md` | no | yes | Optional quick scale artifact. |
| `docs/results/scale_n7lite_full_suite_latest.md` | no | yes | Optional quick full-suite scale artifact. |

## Reviewer-Facing Evidence Entry Points

1. Claim scope and non-claims: `docs/claim_boundary.md`
2. Release dashboard: `docs/results/release_status_latest.md`
3. Proof-track snapshot: `docs/results/proof_snapshot_latest.md`
4. Concrete TLAPS probe: `docs/results/concrete_tlaps_probe_latest.md`
5. Wrapper transfer checks: `docs/results/wrapper_projection_latest.md`
6. Assumption traceability: `docs/assumption_to_evidence_map.md`
7. Rebuttal checklist: `docs/reviewer_checklist.md`
8. Integrity manifest: `docs/results/submission_artifact_manifest_latest.md`
9. Upload bundle: `docs/results/submission_bundle_latest.zip`

## RC Decision

- status: READY (bounded-verification submission RC)
- caution: do not claim closed full-concrete unbounded proof.
