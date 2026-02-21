#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"
STAMP_DAY="$(date +%Y%m%d)"
OUT="$RESULT_DIR/mv5_suite_snapshot_${STAMP_DAY}.md"
LATEST="$RESULT_DIR/mv5_suite_latest.md"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

modes=(attack aps joint transfer)

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
    timeout "$timeout_sec" bash ./run.sh "$mode" mv5
    return $?
  fi
  bash ./run.sh "$mode" mv5
}

for mode in "${modes[@]}"; do
  log="$LOG_DIR/_mv5_suite_${mode}.out"
  echo "=== mv5 suite: mode=${mode} ===" | tee "$log"
  set +e
  (
    cd "$ROOT"
    run_mode "$mode"
  ) | tee -a "$log"
  rc=${PIPESTATUS[0]}
  set -e

  result_map["$mode"]="FAIL"
  if [[ "$rc" -eq 124 ]]; then
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
  elif [[ "$rc" -eq 124 ]]; then
    wall_map["$mode"]=">${MODE_TIMEOUT_SEC}s (timeout)"
  else
    wall_map["$mode"]="-"
  fi
done

{
  echo "# MaxView=5 Full-Suite Snapshot"
  echo
  echo "- date: $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo "- profile: \`mv5\` (\`n=4, f=1, q=3, MaxView=5\`)"
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
  echo "- This snapshot strengthens bounded evidence by increasing view depth to MaxView=5."
  echo "- It remains bounded, assumption-explicit model-checking evidence."
  echo "- It does not replace unbounded theorem proofs."
} > "$OUT"

cp "$OUT" "$LATEST"

echo "mv5 full-suite snapshot written to: $OUT"
echo "Latest mv5 full-suite snapshot: $LATEST"
