#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"
STAMP_DAY="$(date +%Y%m%d)"
SNAPSHOT_BASENAME="${SNAPSHOT_BASENAME:-scale_n7lite_suite}"
OUT="$RESULT_DIR/${SNAPSHOT_BASENAME}_snapshot_${STAMP_DAY}.md"
LATEST="$RESULT_DIR/${SNAPSHOT_BASENAME}_latest.md"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

modes=(attack)
if [[ "${INCLUDE_APS:-0}" = "1" ]]; then
  modes+=(aps)
fi
if [[ "${INCLUDE_JOINT:-0}" = "1" ]]; then
  modes+=(joint)
fi
if [[ "${INCLUDE_TRANSFER:-0}" = "1" ]]; then
  modes+=(transfer)
fi

mode_desc="$(IFS=,; echo "${modes[*]}")"

declare -A model_map=(
  [attack]="MC_AdaptiveAttack"
  [aps]="MC_LivenessAPS"
  [joint]="MC_LivenessAPSAttack"
  [transfer]="MC_RefinementTransfer"
)

declare -A states_map
declare -A distinct_map
declare -A depth_map
declare -A wall_map
declare -A result_map

run_mode() {
  local mode="$1"
  local timeout_sec="${MODE_TIMEOUT_SEC:-0}"
  if [[ "$timeout_sec" =~ ^[0-9]+$ ]] && [[ "$timeout_sec" -gt 0 ]]; then
    timeout "$timeout_sec" bash ./run.sh "$mode" n7lite
    return $?
  fi
  bash ./run.sh "$mode" n7lite
}

for mode in "${modes[@]}"; do
  log="$LOG_DIR/_scale_n7lite_${mode}.out"
  echo "=== n7lite scale suite: mode=${mode} ===" | tee "$log"
  set +e
  (
    cd "$ROOT"
    run_mode "$mode"
  ) | tee -a "$log"
  rc=${PIPESTATUS[0]}
  set -e

  result_map["$mode"]="FAIL"
  if [[ "$rc" -eq 124 || "$rc" -eq 137 || "$rc" -eq 143 ]]; then
    # Ensure timed-out TLC children are not left running in background.
    pkill -f "tlc2.TLC" >/dev/null 2>&1 || true
    pkill -f "tla2tools.jar" >/dev/null 2>&1 || true
    if command -v powershell.exe >/dev/null 2>&1; then
      powershell.exe -NoProfile -Command 'Get-Process java -ErrorAction SilentlyContinue | Stop-Process -Force' >/dev/null 2>&1 || true
    fi
    result_map["$mode"]="TIMEOUT"
  elif grep -q "No error has been found." "$log"; then
    result_map["$mode"]="PASS"
  fi

  states_line="$(grep -E '^[0-9,]+ states generated, [0-9,]+ distinct states found' "$log" | tail -1 || true)"
  if [[ -n "$states_line" ]]; then
    states_map["$mode"]="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\1/')"
    distinct_map["$mode"]="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\2/')"
  else
    states_map["$mode"]="-"
    distinct_map["$mode"]="-"
  fi

  depth_line="$(grep -E '^The depth of the complete state graph search is ' "$log" | tail -1 || true)"
  if [[ -n "$depth_line" ]]; then
    depth_map["$mode"]="$(echo "$depth_line" | sed -E 's/.* is ([0-9]+).*/\1/')"
  else
    depth_map["$mode"]="-"
  fi

  wall_line="$(grep -E '^Finished in ' "$log" | tail -1 || true)"
  if [[ -n "$wall_line" ]]; then
    wall_map["$mode"]="$(echo "$wall_line" | sed -E 's/^Finished in (.*) at .*/\1/')"
  elif [[ "$rc" -eq 124 || "$rc" -eq 137 || "$rc" -eq 143 ]]; then
    wall_map["$mode"]=">${MODE_TIMEOUT_SEC}s (timeout)"
  else
    wall_map["$mode"]="-"
  fi
done

{
  echo "# n=7 Quick Scale Snapshot (n7lite)"
  echo
  echo "- date: $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo "- profile: \`n7lite\` (\`n=7, f=2, q=5, MaxView=1\`)"
  echo "- modes: \`${mode_desc}\`"
  echo "- note: quick scale sanity (bounded, assumption-explicit); default mode is attack-only, full-suite is enabled via INCLUDE_APS/INCLUDE_JOINT/INCLUDE_TRANSFER"
  if [[ "${MODE_TIMEOUT_SEC:-0}" =~ ^[0-9]+$ ]] && [[ "${MODE_TIMEOUT_SEC:-0}" -gt 0 ]]; then
    echo "- per-mode timeout: \`${MODE_TIMEOUT_SEC}s\`"
  fi
  echo
  echo "| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |"
  echo "|---|---:|---:|---:|---:|---|"
  for mode in "${modes[@]}"; do
    model="${model_map[$mode]}"
    echo "| \`${model}\` | ${states_map[$mode]} | ${distinct_map[$mode]} | ${depth_map[$mode]} | ${wall_map[$mode]} | ${result_map[$mode]} |"
  done
  echo
  echo "Interpretation:"
  echo
  echo "- This snapshot is bounded finite-domain evidence for quick scalability sanity."
  echo "- It does not replace unbounded theorem proofs."
} > "$OUT"

cp "$OUT" "$LATEST"

echo "n7lite quick-scale snapshot written to: $OUT"
echo "Latest n7lite quick-scale snapshot: $LATEST"
