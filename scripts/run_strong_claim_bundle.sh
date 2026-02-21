#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"
STAMP="$(date +%Y%m%d-%H%M%S)"
DAY_STAMP="$(date +%Y%m%d)"
SUMMARY="$RESULT_DIR/strong_claim_bundle_${STAMP}.md"
LATEST="$RESULT_DIR/strong_claim_bundle_latest.md"
WRAPPER_STABLE="$RESULT_DIR/wrapper_projection_snapshot_${DAY_STAMP}.md"
CAMPAIGN="$RESULT_DIR/campaign_snapshot_${STAMP}.md"
CAMPAIGN_LATEST="$RESULT_DIR/campaign_snapshot_latest.md"
TRANSFER_SNAPSHOT="$RESULT_DIR/transfer_snapshot_${STAMP}.md"
TRANSFER_LATEST="$RESULT_DIR/transfer_snapshot_latest.md"
BUNDLE_TLAPS_RETRY="${BUNDLE_TLAPS_RETRY:-8}"
BUNDLE_CONCRETE_TLAPS_TIMEOUT_SEC="${BUNDLE_CONCRETE_TLAPS_TIMEOUT_SEC:-300}"
BUNDLE_CONCRETE_TRANSFER_TIMEOUT_SEC="${BUNDLE_CONCRETE_TRANSFER_TIMEOUT_SEC:-1200}"
BUNDLE_INCLUDE_N7LITE_FULL="${BUNDLE_INCLUDE_N7LITE_FULL:-1}"
BUNDLE_N7LITE_FULL_TIMEOUT_SEC="${BUNDLE_N7LITE_FULL_TIMEOUT_SEC:-900}"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

echo "# Strong-Claim Bundle (${STAMP})" > "$SUMMARY"
echo >> "$SUMMARY"
echo "This bundle runs the core executable evidence stack used by reviewer-facing claims." >> "$SUMMARY"
echo >> "$SUMMARY"
echo "| Step | Command | Status | Duration | Log |" >> "$SUMMARY"
echo "|---|---|---|---:|---|" >> "$SUMMARY"

run_step() {
  local name="$1"
  local cmd="$2"
  local log="$LOG_DIR/_bundle_${STAMP}_${name}.out"
  local start end elapsed elapsed_sec status
  start="$(date +%s)"
  if (cd "$ROOT" && bash -lc "$cmd") >"$log" 2>&1; then
    status="PASS"
  else
    status="FAIL"
  fi
  end="$(date +%s)"
  elapsed_sec="$((end - start))"
  if [[ "$elapsed_sec" -lt 0 ]]; then
    elapsed_sec=0
  fi
  elapsed="${elapsed_sec}s"
  echo "| ${name} | \`${cmd}\` | ${status} | ${elapsed} | \`$(basename "$log")\` |" >> "$SUMMARY"
  if [[ "$status" != "PASS" ]]; then
    echo >> "$SUMMARY"
    echo "Bundle failed at step: ${name}" >> "$SUMMARY"
    cp "$SUMMARY" "$LATEST"
    exit 1
  fi
}

run_step "pre_artifact_sync" "make sync-wrapper-table && make sync-snapshot-rows"
run_step "gate" "TLAPS_RETRY=${BUNDLE_TLAPS_RETRY} make gate"
run_step "concrete_tlaps_probe" "PROBE_TIMEOUT_SEC=${BUNDLE_CONCRETE_TLAPS_TIMEOUT_SEC} PROBE_TRANSFER_TIMEOUT_SEC=${BUNDLE_CONCRETE_TRANSFER_TIMEOUT_SEC} make concrete-tlaps-probe-full"
run_step "closure_attempt_safety" "make closure-attempt-safety"
run_step "closure_failure_taxonomy" "make closure-failure-taxonomy"
run_step "closure_trend" "make closure-trend"
run_step "transfer_baseline" "make test-transfer"
run_step "transfer_mv3" "make test-transfer-mv3"
run_step "transfer_mv4" "make test-transfer-mv4"
run_step "scale_n7_attack" "make scale-n7"
run_step "scale_n7lite_suite" "make scale-n7lite"
if [[ "$BUNDLE_INCLUDE_N7LITE_FULL" == "1" ]]; then
  run_step "scale_n7lite_full_suite" "MODE_TIMEOUT_SEC=${BUNDLE_N7LITE_FULL_TIMEOUT_SEC} make scale-n7lite-full"
else
  echo >> "$SUMMARY"
  echo "Note: skipped optional step \`scale_n7lite_full_suite\` (set \`BUNDLE_INCLUDE_N7LITE_FULL=1\` to enable)." >> "$SUMMARY"
fi
run_step "wrapper_projection" "make wrapper-projection"
run_step "suite_mv5" "make suite-mv5"

PY="$(command -v python || command -v python3 || true)"
if [[ -z "$PY" ]]; then
  echo "Error: neither python nor python3 is available on PATH."
  cp "$SUMMARY" "$LATEST"
  exit 1
fi
"$PY" "$ROOT/scripts/build_transfer_snapshot.py" \
  --root "$ROOT" \
  --bundle-stamp "$STAMP" \
  --out "$TRANSFER_SNAPSHOT"
cp "$TRANSFER_SNAPSHOT" "$TRANSFER_LATEST"
run_step "snapshot_row_sync" "make sync-snapshot-rows"
run_step "wrapper_table_sync" "make sync-wrapper-table"
cp "$RESULT_DIR/wrapper_projection_latest.md" "$WRAPPER_STABLE"
run_step "post_sync_check" "make check-sync"
"$PY" "$ROOT/scripts/build_campaign_snapshot.py" \
  --root "$ROOT" \
  --bundle-stamp "$STAMP" \
  --out "$CAMPAIGN"
cp "$CAMPAIGN" "$CAMPAIGN_LATEST"

echo >> "$SUMMARY"
echo "## Produced Artifacts" >> "$SUMMARY"
echo >> "$SUMMARY"
echo "- \`docs/results/$(basename "$TRANSFER_SNAPSHOT")\`" >> "$SUMMARY"
echo "- \`docs/results/$(basename "$TRANSFER_LATEST")\`" >> "$SUMMARY"
echo "- \`docs/results/proof_snapshot_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/proof_blockers_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/concrete_tlaps_probe_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_closure_attempt_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_failure_taxonomy_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_closure_trend_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/safety_transfer_goalpack_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/wrapper_projection_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/$(basename "$WRAPPER_STABLE")\`" >> "$SUMMARY"
echo "- \`docs/results/scale_n7_attack_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/scale_n7lite_suite_latest.md\`" >> "$SUMMARY"
if [[ -f "$RESULT_DIR/scale_n7lite_full_suite_latest.md" ]]; then
  echo "- \`docs/results/scale_n7lite_full_suite_latest.md\`" >> "$SUMMARY"
fi
echo "- \`docs/results/mv5_suite_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/$(basename "$CAMPAIGN")\`" >> "$SUMMARY"
echo "- \`docs/results/$(basename "$CAMPAIGN_LATEST")\`" >> "$SUMMARY"

cp "$SUMMARY" "$LATEST"

echo "Strong-claim bundle summary: $SUMMARY"
echo "Latest strong-claim bundle summary: $LATEST"
