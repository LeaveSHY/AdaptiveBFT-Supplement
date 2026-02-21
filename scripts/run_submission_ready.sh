#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"
STAMP="$(date +%Y%m%d-%H%M%S)"
SUMMARY="$RESULT_DIR/submission_ready_${STAMP}.md"
LATEST="$RESULT_DIR/submission_ready_latest.md"

SUBMISSION_SKIP_GATE_STRONG="${SUBMISSION_SKIP_GATE_STRONG:-1}"
SUBMISSION_SKIP_BUNDLE="${SUBMISSION_SKIP_BUNDLE:-1}"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

echo "# Submission-Ready Campaign (${STAMP})" > "$SUMMARY"
echo >> "$SUMMARY"
echo "One-command campaign to produce submission RC artifacts and run final gates." >> "$SUMMARY"
echo "Defaults reuse latest heavy artifacts for speed; set skip vars to 0 for full rerun." >> "$SUMMARY"
echo >> "$SUMMARY"
echo "| Step | Command | Status | Duration | Log |" >> "$SUMMARY"
echo "|---|---|---|---:|---|" >> "$SUMMARY"
OVERALL_STATUS="PASS"

run_step() {
  local name="$1"
  local cmd="$2"
  local log="$LOG_DIR/_submission_ready_${STAMP}_${name}.out"
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
    OVERALL_STATUS="FAIL"
    echo >> "$SUMMARY"
    echo "Campaign failed at step: ${name}" >> "$SUMMARY"
    echo "See log: \`$(basename "$log")\`" >> "$SUMMARY"
    cp "$SUMMARY" "$LATEST"
    exit 1
  fi
}

run_step "artifact_sync" "make sync-wrapper-table && make sync-snapshot-rows"

if [[ "$SUBMISSION_SKIP_GATE_STRONG" == "1" ]]; then
  echo "| gate_strong | \`make gate-strong\` | SKIP | 0s | \`reused-latest-gate-strong\` |" >> "$SUMMARY"
else
  run_step "gate_strong" "make gate-strong"
fi

if [[ "$SUBMISSION_SKIP_BUNDLE" == "1" ]]; then
  echo "| bundle | \`make bundle\` | SKIP | 0s | \`reused-latest-bundle\` |" >> "$SUMMARY"
else
  run_step "bundle" "make bundle"
fi

run_step "release_status" "make release-status"
run_step "fastlane" "make fastlane FASTLANE_SKIP_BUNDLE=1"
run_step "submission_rc" "make submission-rc"
run_step "submission_manifest" "make submission-manifest"
run_step "submission_bundle" "make submission-bundle"
run_step "check_submission" "make check-submission"
run_step "claim_check" "make claim-check"
run_step "sync_check" "make check-sync"
run_step "theorem_coverage" "make check-theorem-coverage"
run_step "bridge_check" "make check-bridge"

echo >> "$SUMMARY"
echo "- overall: ${OVERALL_STATUS}" >> "$SUMMARY"
echo "- skip_gate_strong: ${SUBMISSION_SKIP_GATE_STRONG}" >> "$SUMMARY"
echo "- skip_bundle: ${SUBMISSION_SKIP_BUNDLE}" >> "$SUMMARY"

echo >> "$SUMMARY"
echo "## Produced Artifacts" >> "$SUMMARY"
echo >> "$SUMMARY"
echo "- \`docs/results/release_status_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/submission_rc_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/submission_artifact_manifest_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/submission_bundle_latest.zip\`" >> "$SUMMARY"
echo "- \`docs/results/submission_package_check_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/fastlane_release_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/strong_claim_bundle_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/proof_snapshot_latest.md\`" >> "$SUMMARY"
echo "- \`docs/results/concrete_tlaps_probe_latest.md\`" >> "$SUMMARY"
echo "- \`docs/claim_boundary.md\`" >> "$SUMMARY"
echo "- \`docs/reviewer_checklist.md\`" >> "$SUMMARY"
echo "- \`docs/assumption_to_evidence_map.md\`" >> "$SUMMARY"
echo "- \`docs/paper_claim_text.tex\`" >> "$SUMMARY"

cp "$SUMMARY" "$LATEST"
echo "Submission-ready summary: $SUMMARY"
echo "Latest submission-ready summary: $LATEST"
