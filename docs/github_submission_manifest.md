# GitHub Submission Manifest (AdaptiveBFT-Formal-Verification)

## Scope

This repository submission keeps:

- `APPENDIX A.pdf` (cryptographic proof appendix)
- `APPENDIX B.pdf` (TLA+ formal specification and verification appendix)

The LaTeX source file `APPENDIX_B_source.tex` is intentionally removed.

## Keep (Core Files)

- `README.md`
- `Makefile`
- `run.sh`
- `tla2tools.jar`
- `APPENDIX A.pdf`
- `APPENDIX B.pdf`
- `AdaptiveBFT.pdf`
- `AdaptiveBFT_MainFlow.pdf`
- `AdaptiveBFT_Types.pdf`
- `AdaptiveBFT_Properties.pdf`
- `modules/AVC_RVS.pdf`
- `modules/APS_Mempool.pdf`
- `modules/APS_Scheduler.pdf`
- `specifications/**`
- `models/**`
- `scripts/**`
- `docs/formal_figures.tex`
- `docs/verification_tables.tex`
- `docs/claim_boundary.md`
- `docs/proof_roadmap.md`
- `docs/reviewer_checklist.md`
- `docs/assumption_to_evidence_map.md`
- `docs/submission_guide.md`
- `docs/results/*latest*`
- `docs/final_repo_tree.txt`
- `docs/github_submission_manifest.md`

## Drop (Do Not Commit)

- TLC runtime state and checkpoints:
  - `states/`
  - `models/states/`
  - `models/*_TTrace_*`
  - `models/*.chkpt`
  - `models/*.st`
  - `models/*.fp`
- Build artifacts:
  - `*.aux`
  - `*.log`
  - `*.out`
  - `*.dvi`
  - `*.ps`
  - `*.synctex.gz`
  - `*.tlatex.tla`
  - `modules/*.tex`
- Temporary bundles:
  - `docs/results/*.zip`

## Final Pre-Push Checklist

1. `git status` is clean.
2. `APPENDIX A.pdf` and `APPENDIX B.pdf` exist at repository root.
3. `APPENDIX_B_source.tex` does not exist.
4. `docs/final_repo_tree.txt` reflects current tracked files.
5. `docs/results/*latest*` snapshots are present.
