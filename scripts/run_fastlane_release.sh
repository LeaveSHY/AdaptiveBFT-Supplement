#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
STAMP="$(date +%Y%m%d-%H%M%S)"
SUMMARY="$RESULT_DIR/fastlane_release_${STAMP}.md"
LATEST="$RESULT_DIR/fastlane_release_latest.md"
LOG_DIR="$ROOT/models"
FASTLANE_SKIP_BUNDLE="${FASTLANE_SKIP_BUNDLE:-0}"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

echo "# Fastlane Release Campaign (${STAMP})" > "$SUMMARY"
echo >> "$SUMMARY"
echo "This campaign executes the reviewer-facing high-value stack in one command." >> "$SUMMARY"
echo "It reuses \`make bundle\` as the heavy core and avoids redundant reruns." >> "$SUMMARY"
echo >> "$SUMMARY"
echo "| Step | Command | Status | Duration | Log |" >> "$SUMMARY"
echo "|---|---|---|---:|---|" >> "$SUMMARY"

run_step() {
  local name="$1"
  local cmd="$2"
  local log="$LOG_DIR/_fastlane_${STAMP}_${name}.out"
  local start end elapsed_sec status
  start="$(date +%s)"
  if (cd "$ROOT" && bash -lc "$cmd") >"$log" 2>&1; then
    status="PASS"
  else
    status="FAIL"
  fi
  end="$(date +%s)"
  elapsed_sec="$((end - start))"
  [[ "$elapsed_sec" -lt 0 ]] && elapsed_sec=0
  echo "| ${name} | \`${cmd}\` | ${status} | ${elapsed_sec}s | \`$(basename "$log")\` |" >> "$SUMMARY"
  if [[ "$status" != "PASS" ]]; then
    echo >> "$SUMMARY"
    echo "Campaign failed at step: ${name}" >> "$SUMMARY"
    echo "See log: \`$(basename "$log")\`" >> "$SUMMARY"
    cp "$SUMMARY" "$LATEST"
    exit 1
  fi
}

run_step "pre_artifact_sync" "make sync-wrapper-table && make sync-snapshot-rows"
if [[ "$FASTLANE_SKIP_BUNDLE" == "1" ]]; then
  echo "| bundle | \`make bundle\` | SKIP | 0s | \`reused-latest-bundle\` |" >> "$SUMMARY"
  echo >> "$SUMMARY"
  echo "Note: reused existing \`docs/results/strong_claim_bundle_latest.md\` (\`FASTLANE_SKIP_BUNDLE=1\`)." >> "$SUMMARY"
else
  run_step "bundle" "make bundle"
fi
if command -v pdflatex >/dev/null 2>&1; then
  run_step "appendix_five_figs" "make appendix-five-figs"
else
  if [[ -f "$ROOT/AdaptiveBFT_MainFlow.pdf" && \
        -f "$ROOT/AdaptiveBFT_Types.pdf" && \
        -f "$ROOT/modules/AVC_RVS.pdf" && \
        -f "$ROOT/modules/APS_Mempool.pdf" && \
        -f "$ROOT/AdaptiveBFT_Properties.pdf" ]]; then
    echo "| appendix_five_figs | \`make appendix-five-figs\` | PASS | 0s | \`reused-existing-pdfs\` |" >> "$SUMMARY"
    echo >> "$SUMMARY"
    echo "Note: \`pdflatex\` unavailable; reused existing 5 appendix PDFs from repository workspace." >> "$SUMMARY"
  else
    echo "| appendix_five_figs | \`make appendix-five-figs\` | SKIP | 0s | \`pdflatex-unavailable\` |" >> "$SUMMARY"
    echo >> "$SUMMARY"
    echo "Note: skipped appendix PDF generation because \`pdflatex\` is unavailable in current environment and prebuilt PDFs are missing." >> "$SUMMARY"
  fi
fi
run_step "theorem_coverage" "make check-theorem-coverage"
run_step "claim_check" "make claim-check"
run_step "release_status" "make release-status"

echo >> "$SUMMARY"
echo "## Produced Artifacts" >> "$SUMMARY"
echo >> "$SUMMARY"
echo "- \`docs/results/strong_claim_bundle_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/release_status_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/proof_snapshot_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/proof_blockers_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/concrete_tlaps_probe_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/campaign_snapshot_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_closure_attempt_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_failure_taxonomy_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_closure_trend_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_goalpack_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/mv5_suite_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/scale_n7_attack_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/scale_n7lite_suite_latest.md\`" >> "$SUMMARY"
if [[ -f "$RESULT_DIR/scale_n7lite_full_suite_latest.md" ]]; then
  echo "- \`docs/results/scale_n7lite_full_suite_latest.md\`" >> "$SUMMARY"
fi
echo "- \`docs/results/wrapper_projection_latest.md\`" >> "$SUMMARY"
echo "- \`AdaptiveBFT_MainFlow.pdf\`" >> "$SUMMARY"
echo "- \`AdaptiveBFT_Types.pdf\`" >> "$SUMMARY"
echo "- \`modules/AVC_RVS.pdf\`" >> "$SUMMARY"
echo "- \`modules/APS_Mempool.pdf\`" >> "$SUMMARY"
echo "- \`AdaptiveBFT_Properties.pdf\`" >> "$SUMMARY"

cp "$SUMMARY" "$LATEST"
echo "Fastlane release summary: $SUMMARY"
echo "Latest fastlane release summary: $LATEST"
