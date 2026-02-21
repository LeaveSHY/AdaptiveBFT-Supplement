.PHONY: all all-mv3 all-mv4 all-mv5 all-n7 all-n7-full all-n7lite all-n7lite-full scale-n7 scale-n7lite scale-n7lite-full suite-mv5 test-attack test-aps test-joint test-transfer test-attack-mv3 test-aps-mv3 test-joint-mv3 test-transfer-mv3 test-attack-mv4 test-aps-mv4 test-joint-mv4 test-transfer-mv4 test-attack-mv5 test-aps-mv5 test-joint-mv5 test-transfer-mv5 test-attack-n7 test-aps-n7 test-joint-n7 test-transfer-n7 test-attack-n7lite test-aps-n7lite test-joint-n7lite test-transfer-n7lite wrapper-projection sync-wrapper-table sync-snapshot-rows refresh-wrapper matrix matrix-progress proofs proof-snapshot proof-blockers concrete-tlaps-probe concrete-tlaps-probe-full closure-attempt-safety closure-failure-taxonomy closure-trend release-status submission-rc submission-manifest submission-bundle check-submission submission-ready submission-ready-full fastlane all-in-one check-sync check-bridge check-theorem-coverage claim-check gate gate-strong bundle pdf list-pdf appendix-five-figs clean help

RUN := bash ./run.sh
JAR := tla2tools.jar
SPEC_DIR := specifications
DEFAULT_PDF := AdaptiveBFT.pdf
TLA_SPECS := $(shell find $(SPEC_DIR) -path '$(SPEC_DIR)/.tlacache' -prune -o -name '*.tla' -type f -print | sed 's#^$(SPEC_DIR)/##')
PDF_TARGETS := $(patsubst %.tla,%.pdf,$(TLA_SPECS))
TYPESET_ROOTS := $(patsubst %.pdf,%,$(PDF_TARGETS))
FIVE_FIG_PDFS := AdaptiveBFT_MainFlow.pdf AdaptiveBFT_Types.pdf modules/AVC_RVS.pdf modules/APS_Mempool.pdf AdaptiveBFT_Properties.pdf

all: test-attack test-aps test-joint

all-mv3: test-attack-mv3 test-aps-mv3 test-joint-mv3

all-mv4: test-attack-mv4 test-aps-mv4 test-joint-mv4

all-mv5: test-attack-mv5 test-aps-mv5 test-joint-mv5

all-n7: test-attack-n7

all-n7-full: test-attack-n7 test-aps-n7 test-joint-n7 test-transfer-n7

all-n7lite: test-attack-n7lite

all-n7lite-full: test-attack-n7lite test-aps-n7lite test-joint-n7lite test-transfer-n7lite

test-attack:
	@echo ">>> Starting AVC Security Verification (Adaptive Attack)..."
	@$(RUN) attack

test-aps:
	@echo ">>> Starting APS Liveness Verification (Progress & Reconfiguration)..."
	@$(RUN) aps

test-joint:
	@echo ">>> Starting Joint Liveness Verification (APS + Adaptive Attack)..."
	@$(RUN) joint

test-transfer:
	@echo ">>> Starting Refinement Transfer Verification (Concrete -> Abstract)..."
	@$(RUN) transfer

test-attack-mv3:
	@echo ">>> Starting AVC Security Verification (Adaptive Attack, MaxView=3)..."
	@$(RUN) attack mv3

test-aps-mv3:
	@echo ">>> Starting APS Liveness Verification (MaxView=3)..."
	@$(RUN) aps mv3

test-joint-mv3:
	@echo ">>> Starting Joint Liveness Verification (APS + Adaptive Attack, MaxView=3)..."
	@$(RUN) joint mv3

test-transfer-mv3:
	@echo ">>> Starting Refinement Transfer Verification (MaxView=3)..."
	@$(RUN) transfer mv3

test-attack-mv4:
	@echo ">>> Starting AVC Security Verification (Adaptive Attack, MaxView=4)..."
	@$(RUN) attack mv4

test-aps-mv4:
	@echo ">>> Starting APS Liveness Verification (MaxView=4)..."
	@$(RUN) aps mv4

test-joint-mv4:
	@echo ">>> Starting Joint Liveness Verification (APS + Adaptive Attack, MaxView=4)..."
	@$(RUN) joint mv4

test-transfer-mv4:
	@echo ">>> Starting Refinement Transfer Verification (MaxView=4)..."
	@$(RUN) transfer mv4

test-attack-mv5:
	@echo ">>> Starting AVC Security Verification (Adaptive Attack, MaxView=5)..."
	@$(RUN) attack mv5

test-aps-mv5:
	@echo ">>> Starting APS Liveness Verification (MaxView=5)..."
	@$(RUN) aps mv5

test-joint-mv5:
	@echo ">>> Starting Joint Liveness Verification (APS + Adaptive Attack, MaxView=5)..."
	@$(RUN) joint mv5

test-transfer-mv5:
	@echo ">>> Starting Refinement Transfer Verification (MaxView=5)..."
	@$(RUN) transfer mv5

test-attack-n7:
	@echo ">>> Starting AVC Security Verification (n=7,f=2,q=5)..."
	@$(RUN) attack n7

test-aps-n7:
	@echo ">>> Starting APS Liveness Verification (n=7,f=2,q=5)..."
	@$(RUN) aps n7

test-joint-n7:
	@echo ">>> Starting Joint Liveness Verification (n=7,f=2,q=5)..."
	@$(RUN) joint n7

test-transfer-n7:
	@echo ">>> Starting Refinement Transfer Verification (n=7,f=2,q=5)..."
	@$(RUN) transfer n7

test-attack-n7lite:
	@echo ">>> Starting AVC Security Verification (n=7,f=2,q=5, quick MaxView=1)..."
	@$(RUN) attack n7lite

test-aps-n7lite:
	@echo ">>> Starting APS Liveness Verification (n=7,f=2,q=5, quick MaxView=1)..."
	@$(RUN) aps n7lite

test-joint-n7lite:
	@echo ">>> Starting Joint Liveness Verification (n=7,f=2,q=5, quick MaxView=1)..."
	@$(RUN) joint n7lite

test-transfer-n7lite:
	@echo ">>> Starting Refinement Transfer Verification (n=7,f=2,q=5, quick MaxView=1)..."
	@$(RUN) transfer n7lite

scale-n7:
	@echo ">>> Running n=7 attack scale snapshot..."
	@bash ./scripts/run_scale_attack_n7.sh

scale-n7lite:
	@echo ">>> Running n=7 quick-scale snapshot (n7lite)..."
	@bash ./scripts/run_scale_n7lite_suite.sh

scale-n7lite-full:
	@echo ">>> Running n=7 quick-scale full-suite snapshot (attack + aps + joint + transfer)..."
	@bash -lc 'MODE_TIMEOUT_SEC="$(MODE_TIMEOUT_SEC)" SNAPSHOT_BASENAME=scale_n7lite_full_suite INCLUDE_APS=1 INCLUDE_JOINT=1 INCLUDE_TRANSFER=1 ./scripts/run_scale_n7lite_suite.sh'

suite-mv5:
	@echo ">>> Running MaxView=5 full-suite snapshot (attack + aps + joint + transfer)..."
	@bash ./scripts/run_mv5_suite.sh

matrix:
	@echo ">>> Running verification matrix (baseline, mv3, mv4)..."
	@bash ./scripts/run_matrix.sh baseline mv3 mv4

matrix-progress:
	@echo ">>> Running timeout-bounded matrix progress campaign (does not overwrite synced matrix table source)..."
	@bash -lc 'MODE_TIMEOUT_SEC="$${MODE_TIMEOUT_SEC:-600}" ./scripts/run_matrix.sh baseline mv3 mv4 || true'

wrapper-projection:
	@echo ">>> Running wrapper-integrated projection checks (baseline + mv4)..."
	@bash ./scripts/run_wrapper_projection.sh

sync-wrapper-table:
	@echo ">>> Synchronizing wrapper table with latest wrapper snapshot..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/sync_wrapper_table.py

sync-snapshot-rows:
	@echo ">>> Synchronizing README/LaTeX n7/n7lite+transfer rows from latest snapshots..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/sync_snapshot_rows.py

refresh-wrapper:
	@echo ">>> Running wrapper campaign + table sync..."
	@$(MAKE) wrapper-projection
	@$(MAKE) sync-wrapper-table

proofs:
	@echo ">>> Checking abstract/theorem/refinement track..."
	@bash ./scripts/check_proof_track.sh "$(SKIP_TLAPS)" "$(TLAPS_REFINEMENT)"

proof-snapshot:
	@echo ">>> Building proof-track snapshot..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/proof_snapshot_$${STAMP}.md; \
	"$$PY" ./scripts/build_proof_snapshot.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/proof_snapshot_latest.md; \
	echo "Proof snapshot written to: $$OUT"

proof-blockers:
	@echo ">>> Building proof blocker snapshot..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/proof_blockers_$${STAMP}.md; \
	"$$PY" ./scripts/build_proof_blockers.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/proof_blockers_latest.md; \
	echo "Proof blocker snapshot written to: $$OUT"

concrete-tlaps-probe:
	@echo ">>> Running concrete-track TLAPS probe (non-blocking diagnostics)..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/run_concrete_tlaps_probe.py --root . --timeout "$${PROBE_TIMEOUT_SEC:-300}"

concrete-tlaps-probe-full:
	@echo ">>> Running concrete-track TLAPS probe with transfer-timeout override..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/run_concrete_tlaps_probe.py --root . --timeout "$${PROBE_TIMEOUT_SEC:-300}" --timeout-transfer "$${PROBE_TRANSFER_TIMEOUT_SEC:-1200}"

closure-attempt-safety:
	@echo ">>> Running safety-transfer closure attempts..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/run_safety_transfer_closure_attempt.py

closure-failure-taxonomy:
	@echo ">>> Building safety-transfer failure taxonomy..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/build_safety_transfer_failure_taxonomy.py --root .

closure-trend:
	@echo ">>> Building safety-transfer closure trend..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/build_safety_transfer_closure_trend.py --root .

check-sync:
	@echo ">>> Checking matrix/table synchronization..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/check_tables_sync.py; \
	"$$PY" ./scripts/check_aux_sync.py; \
	"$$PY" ./scripts/check_snapshot_dates_sync.py

check-bridge:
	@echo ">>> Checking wrapper bridge invariant wiring..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/check_bridge_invariants.py

check-theorem-coverage:
	@echo ">>> Checking explicit theorem-proof coverage..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/check_theorem_coverage.py

claim-check:
	@echo ">>> Checking claim-boundary artifacts..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/check_claim_artifacts.py

gate:
	@echo ">>> Running proof + artifact gate..."
	@$(MAKE) proofs
	@$(MAKE) proof-snapshot
	@$(MAKE) proof-blockers
	@$(MAKE) check-theorem-coverage
	@$(MAKE) check-sync
	@$(MAKE) check-bridge
	@$(MAKE) claim-check
	@echo ">>> Gate passed."

gate-strong:
	@echo ">>> Running strong gate (gate + closure attempts + release dashboard)..."
	@$(MAKE) gate
	@$(MAKE) concrete-tlaps-probe-full
	@$(MAKE) closure-attempt-safety
	@$(MAKE) closure-failure-taxonomy
	@$(MAKE) closure-trend
	@$(MAKE) release-status
	@echo ">>> Strong gate passed."

bundle:
	@echo ">>> Running strong-claim verification bundle..."
	@bash ./scripts/run_strong_claim_bundle.sh

release-status:
	@echo ">>> Building release-status dashboard..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/release_status_$${STAMP}.md; \
	"$$PY" ./scripts/build_release_status.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/release_status_latest.md; \
	echo "Release status written to: $$OUT"

submission-rc:
	@echo ">>> Building submission RC summary..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/submission_rc_$${STAMP}.md; \
	"$$PY" ./scripts/build_submission_rc.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/submission_rc_latest.md; \
	echo "Submission RC summary written to: $$OUT"

submission-manifest:
	@echo ">>> Building submission artifact manifest..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/submission_artifact_manifest_$${STAMP}.md; \
	"$$PY" ./scripts/build_submission_artifact_manifest.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/submission_artifact_manifest_latest.md; \
	echo "Submission artifact manifest written to: $$OUT"

submission-bundle:
	@echo ">>> Building submission artifact bundle (.zip)..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/submission_bundle_$${STAMP}.zip; \
	"$$PY" ./scripts/build_submission_bundle.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/submission_bundle_latest.zip; \
	echo "Submission bundle written to: $$OUT"

check-submission:
	@echo ">>> Checking submission package integrity..."
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	STAMP=$$(date +%Y%m%d-%H%M%S); \
	OUT=docs/results/submission_package_check_$${STAMP}.md; \
	"$$PY" ./scripts/check_submission_package.py --root . --out "$$OUT"; \
	cp "$$OUT" docs/results/submission_package_check_latest.md; \
	echo "Submission package check written to: $$OUT"

submission-ready:
	@echo ">>> Running one-command submission-ready campaign..."
	@bash ./scripts/run_submission_ready.sh

submission-ready-full:
	@echo ">>> Running strict full submission-ready campaign (no skips)..."
	@bash -lc 'SUBMISSION_SKIP_GATE_STRONG=0 SUBMISSION_SKIP_BUNDLE=0 ./scripts/run_submission_ready.sh'
	@$(MAKE) check-submission

fastlane:
	@echo ">>> Running fastlane release campaign..."
	@bash -lc 'FASTLANE_SKIP_BUNDLE="$(FASTLANE_SKIP_BUNDLE)" ./scripts/run_fastlane_release.sh'

all-in-one: fastlane
	@echo ">>> One-step full campaign completed."

pdf: $(DEFAULT_PDF)

list-pdf:
	@echo "Available PDF targets:"
	@$(foreach p,$(PDF_TARGETS),echo "  make $(p)";)

appendix-five-figs: $(FIVE_FIG_PDFS)
	@echo "Generated 5 appendix figures:"
	@$(foreach p,$(FIVE_FIG_PDFS),echo "  $(p)";)

%.pdf: $(SPEC_DIR)/%.tla
	@if [ ! -f "$(JAR)" ]; then \
		echo "Error: $(JAR) not found in repository root."; \
		echo "Place tla2tools.jar at: $$(pwd)/$(JAR)"; \
		exit 1; \
	fi
	@if ! command -v pdflatex >/dev/null 2>&1; then \
		echo "Error: pdflatex is not installed."; \
		echo "Install TeX Live first, for example:"; \
		echo "  Ubuntu/WSL: sudo apt-get update && sudo apt-get install -y texlive-latex-base"; \
		exit 1; \
	fi
	@mkdir -p "$(dir $@)"
	@echo ">>> Typesetting $< -> $@"
	@java -cp "$(JAR)" tla2tex.TLA -nops -latexCommand pdflatex -latexOutputExt pdf -out "$*" "$<"
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/ensure_tex_no_page_numbers.py "$*.tex"; \
	pdflatex -interaction=nonstopmode -halt-on-error "$*.tex" >/dev/null

modules/%.pdf: $(SPEC_DIR)/modules/%.tla
	@if [ ! -f "$(JAR)" ]; then \
		echo "Error: $(JAR) not found in repository root."; \
		echo "Place tla2tools.jar at: $$(pwd)/$(JAR)"; \
		exit 1; \
	fi
	@if ! command -v pdflatex >/dev/null 2>&1; then \
		echo "Error: pdflatex is not installed."; \
		echo "Install TeX Live first, for example:"; \
		echo "  Ubuntu/WSL: sudo apt-get update && sudo apt-get install -y texlive-latex-base"; \
		exit 1; \
	fi
	@mkdir -p "$(dir $@)"
	@echo ">>> Typesetting $< -> $@"
	@java -cp "$(JAR)" tla2tex.TLA -nops -latexCommand pdflatex -latexOutputExt pdf -out "$*" "$<"
	@PY=$$(command -v python || command -v python3); \
	if [ -z "$$PY" ]; then \
		echo "Error: neither python nor python3 is available on PATH."; \
		exit 1; \
	fi; \
	"$$PY" ./scripts/ensure_tex_no_page_numbers.py "$*.tex"; \
	pdflatex -interaction=nonstopmode -halt-on-error "$*.tex" >/dev/null
	@mv "$*.pdf" "$@"
	@if [ -f "$*.tex" ]; then mv "$*.tex" "modules/$*.tex"; fi
	@if [ -f "$*.aux" ]; then mv "$*.aux" "modules/$*.aux"; fi
	@if [ -f "$*.log" ]; then mv "$*.log" "modules/$*.log"; fi

clean:
	@echo ">>> Cleaning up..."
	rm -rf states/
	rm -f *.out
	rm -f models/*.out
	rm -f models/_bench_*.out
	rm -f $(addsuffix .aux,$(TYPESET_ROOTS))
	rm -f $(addsuffix .log,$(TYPESET_ROOTS))
	rm -f $(addsuffix .dvi,$(TYPESET_ROOTS))
	rm -f $(addsuffix .ps,$(TYPESET_ROOTS))
	rm -f $(addsuffix .pdf,$(TYPESET_ROOTS))
	rm -f $(addsuffix .tex,$(TYPESET_ROOTS))
	@echo "Done."

help:
	@echo "AdaptiveBFT Makefile Guide:"
	@echo "  make all              - Run all verification tests (AVC + APS + Joint)"
	@echo "  make all-mv3          - Run all verification tests with MaxView=3 richer-domain profile"
	@echo "  make all-mv4          - Run all verification tests with MaxView=4 profile"
	@echo "  make all-mv5          - Run all verification tests with MaxView=5 profile"
	@echo "  make all-n7           - Run n=7,f=2,q=5 attack profile (fastest scale sanity run)"
	@echo "  make all-n7-full      - Run all n=7 profile checks (can be very expensive)"
	@echo "  make all-n7lite       - Run n=7,f=2,q=5 quick attack sanity (MaxView=1)"
	@echo "  make all-n7lite-full  - Run all n=7,f=2,q=5 quick-profile checks (can still be expensive)"
	@echo "  make scale-n7         - Run n=7 attack profile and write docs/results scale snapshot"
	@echo "  make scale-n7lite     - Run n=7 quick-profile attack snapshot and write docs/results artifact"
	@echo "  make scale-n7lite-full - Run n=7 quick-profile full-suite snapshot to scale_n7lite_full_suite_latest.md (optional MODE_TIMEOUT_SEC=<seconds>)"
	@echo "  make suite-mv5        - Run MaxView=5 full-suite snapshot and write docs/results artifact"
	@echo "  make test-attack      - Run AVC attack scenario"
	@echo "  make test-aps         - Run APS liveness scenario"
	@echo "  make test-joint       - Run APS + attack joint liveness scenario"
	@echo "  make test-transfer    - Run concrete-to-abstract transfer checks"
	@echo "  make test-attack-mv3  - Run AVC attack scenario with MaxView=3"
	@echo "  make test-aps-mv3     - Run APS liveness scenario with MaxView=3"
	@echo "  make test-joint-mv3   - Run APS + attack joint liveness with MaxView=3"
	@echo "  make test-transfer-mv3 - Run transfer checks with MaxView=3"
	@echo "  make test-attack-mv4  - Run AVC attack scenario with MaxView=4"
	@echo "  make test-aps-mv4     - Run APS liveness scenario with MaxView=4"
	@echo "  make test-joint-mv4   - Run APS + attack joint liveness with MaxView=4"
	@echo "  make test-transfer-mv4 - Run transfer checks with MaxView=4"
	@echo "  make test-attack-mv5  - Run AVC attack scenario with MaxView=5"
	@echo "  make test-aps-mv5     - Run APS liveness scenario with MaxView=5"
	@echo "  make test-joint-mv5   - Run APS + attack joint liveness with MaxView=5"
	@echo "  make test-transfer-mv5 - Run transfer checks with MaxView=5"
	@echo "  make test-attack-n7   - Run AVC attack scenario with n=7,f=2,q=5"
	@echo "  make test-aps-n7      - Run APS liveness scenario with n=7,f=2,q=5"
	@echo "  make test-joint-n7    - Run APS + attack joint liveness with n=7,f=2,q=5"
	@echo "  make test-transfer-n7 - Run transfer checks with n=7,f=2,q=5"
	@echo "  make test-attack-n7lite - Run AVC attack with n=7,f=2,q=5, MaxView=1"
	@echo "  make test-aps-n7lite  - Run APS liveness with n=7,f=2,q=5, MaxView=1"
	@echo "  make test-joint-n7lite - Run APS+attack liveness with n=7,f=2,q=5, MaxView=1"
	@echo "  make test-transfer-n7lite - Run transfer checks with n=7,f=2,q=5, MaxView=1"
	@echo "  make matrix           - Run baseline/mv3/mv4 matrix and write CSV summary"
	@echo "  make matrix-progress  - Run timeout-bounded matrix campaign (MODE_TIMEOUT_SEC=<sec>) and write progress CSV"
	@echo "  make wrapper-projection - Run baseline/mv4 wrapper projection checks and write Markdown snapshot"
	@echo "  make proof-blockers   - Build allowlisted theorem-blocker snapshot"
	@echo "  make concrete-tlaps-probe - Run concrete theorem TLAPS diagnostics (non-blocking, emits concrete_tlaps_probe_latest.md)"
	@echo "  make concrete-tlaps-probe-full - Run concrete TLAPS diagnostics with higher transfer timeout (default 1200s)"
	@echo "  make sync-wrapper-table - Sync wrapper-projection rows in docs/verification_tables.tex"
	@echo "  make sync-snapshot-rows - Sync README/LaTeX n7/n7lite+transfer rows from latest snapshot artifacts"
	@echo "  make refresh-wrapper  - Run wrapper projection campaign and sync wrapper table"
	@echo "  make proofs           - Run SANY (and TLAPS if installed) for theorem track"
	@echo "  make proof-snapshot   - Build docs/results/proof_snapshot_latest.md from TLAPS/SANY gate artifacts"
	@echo "  make closure-attempt-safety - Run automated closure attempts for AbstractSafetyTransferTemplate and emit a report"
	@echo "  make closure-failure-taxonomy - Build grouped failure taxonomy from latest closure-attempt logs"
	@echo "  make closure-trend   - Build multi-campaign closure-attempt trend report"
	@echo "  make check-theorem-coverage - Verify unproved theorems are explicitly allowlisted"
	@echo "  make check-sync       - Verify README/LaTeX rows + snapshot-date notes stay synchronized"
	@echo "  make check-bridge     - Verify bridge invariants are present in wrapper models and cfg profiles"
	@echo "  make claim-check      - Verify claim-boundary result artifacts exist and bundle status is PASS"
	@echo "  make gate             - Run theorem checks + matrix/table synchronization gate"
	@echo "  make gate-strong      - Run gate + full concrete probe + safety-transfer closure attempts + release dashboard"
	@echo "  make bundle           - Run gate + transfer profiles + wrapper projection + n7 scale + mv5 suite, then emit unified campaign snapshot"
	@echo "  make release-status   - Build docs/results/release_status_latest.md from latest bundle/mv5/proof artifacts"
	@echo "  make submission-rc    - Build docs/results/submission_rc_latest.md (reviewer-facing RC summary)"
	@echo "  make submission-manifest - Build docs/results/submission_artifact_manifest_latest.md (artifact integrity manifest)"
	@echo "  make submission-bundle - Build docs/results/submission_bundle_latest.zip (upload-ready package)"
	@echo "  make check-submission - Verify required artifacts, summaries, and zip contents"
	@echo "  make submission-ready - Run one-command submission-ready campaign and emit submission_ready_latest.md"
	@echo "  make submission-ready-full - Run strict submission-ready campaign (gate/bundle no skip) + package check"
	@echo "  make fastlane         - Run bundle + appendix figures + release dashboard in one command"
	@echo "  make all-in-one       - Alias of fastlane (single-command full campaign)"
	@echo "  make pdf              - Typeset default spec ($(DEFAULT_PDF))"
	@echo "  make <name>.pdf       - Typeset a specific spec, e.g. make AdaptiveBFT.pdf"
	@echo "  make list-pdf         - List all available PDF targets"
	@echo "  make appendix-five-figs - Build 5 Sailfish-style appendix figure PDFs"
	@echo "  make clean            - Clean TLC and typesetting artifacts"
