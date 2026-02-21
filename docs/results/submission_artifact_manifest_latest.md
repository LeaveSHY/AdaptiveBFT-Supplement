# Submission Artifact Manifest

- generated: 2026-02-21 02:17:03 +0800
- purpose: upload/review integrity manifest for submission package
- release_overall: PASS
- submission_rc_status: READY (bounded-verification submission RC)
- submission_ready_overall: PASS

| Artifact | Required | Exists | Size (KB) | SHA256 (16) | Purpose |
|---|---|---|---:|---|---|
| `README.md` | yes | yes | 28.0 | `acc00823449a1964` | Top-level reproducibility entry point. |
| `docs/claim_boundary.md` | yes | yes | 8.7 | `9022ffcd5a4428b1` | Normative claim boundary. |
| `docs/proof_roadmap.md` | yes | yes | 10.1 | `14c01f5776ee36d5` | Proof-obligation roadmap. |
| `docs/assumption_to_evidence_map.md` | yes | yes | 3.8 | `49655cd0c5e8ce30` | Assumption-to-evidence traceability. |
| `docs/reviewer_checklist.md` | yes | yes | 3.6 | `465612cdd2eefa3f` | Reviewer challenge and rebuttal checklist. |
| `docs/submission_guide.md` | yes | yes | 1.4 | `0d03f905fc254c28` | Submission handoff and upload checklist. |
| `docs/paper_claim_text.tex` | yes | yes | 1.2 | `d7da516d05a1a238` | Safe claim text snippet for paper. |
| `docs/formal_figures.tex` | yes | yes | 7.5 | `299d084a64d7dfed` | Formal specification appendix section. |
| `docs/verification_tables.tex` | yes | yes | 11.9 | `0355e5e06668964c` | Verification settings/results tables. |
| `docs/results/release_status_latest.md` | yes | yes | 3.9 | `d6170a3486dedc96` | Release dashboard. |
| `docs/results/submission_rc_latest.md` | yes | yes | 3.4 | `8547536ff0b536f6` | Submission RC summary. |
| `docs/results/submission_ready_latest.md` | yes | yes | 2.3 | `9683a665bf39610f` | One-command campaign summary. |
| `docs/results/strong_claim_bundle_latest.md` | yes | yes | 3.0 | `356c9777002dc9b4` | Bundle campaign summary. |
| `docs/results/fastlane_release_latest.md` | yes | yes | 1.9 | `43c1f272bb10fe78` | Fastlane campaign summary. |
| `docs/results/proof_snapshot_latest.md` | yes | yes | 1.9 | `625c27c1089d329f` | Theorem-track machine-check summary. |
| `docs/results/concrete_tlaps_probe_latest.md` | yes | yes | 1.1 | `7adb2a3ecefd530b` | Concrete TLAPS diagnostics. |
| `docs/results/wrapper_projection_latest.md` | yes | yes | 1.2 | `385986403781dcc5` | Wrapper transfer/property checks. |
| `docs/results/mv5_suite_latest.md` | yes | yes | 0.7 | `315e7a4866c306d7` | Deep bounded model-checking snapshot. |
| `AdaptiveBFT_MainFlow.pdf` | yes | yes | 76.7 | `b34020c91d42ad78` | Appendix figure: main flow. |
| `AdaptiveBFT_Types.pdf` | yes | yes | 78.3 | `f5c364e40c7d4732` | Appendix figure: type system. |
| `modules/AVC_RVS.pdf` | yes | yes | 81.7 | `410cccb8bb69d04d` | Appendix figure: AVC+RVS support. |
| `modules/APS_Mempool.pdf` | yes | yes | 111.2 | `3f8cfb9105db0e65` | Appendix figure: APS+mempool support. |
| `AdaptiveBFT_Properties.pdf` | yes | yes | 71.1 | `3b0165b9f0ba5728` | Appendix figure: correctness properties. |
| `docs/results/scale_n7_attack_latest.md` | no | yes | 0.4 | `d2e475e575a8b3f3` | Optional scale sanity snapshot. |
| `docs/results/scale_n7lite_suite_latest.md` | no | yes | 0.6 | `fea630209ad1a55e` | Optional quick scale snapshot. |
| `docs/results/scale_n7lite_full_suite_latest.md` | no | yes | 0.8 | `366c464dd0e16447` | Optional quick full-suite scale snapshot. |

## Decision

- required artifacts: COMPLETE
- interpretation: this is a bounded-verification release package, not an unbounded full-concrete closure proof.

## Reproduction

```bash
make submission-ready
make submission-manifest
make submission-bundle
```
