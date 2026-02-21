#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG="$ROOT/models/_scale_n7_attack.out"

mkdir -p "$RESULT_DIR"

(
  cd "$ROOT"
  bash ./run.sh attack n7
) | tee "$LOG"

extract_metric() {
  local regex="$1"
  grep -E "$regex" "$LOG" | tail -1 || true
}

states_line="$(extract_metric '^[0-9,]+ states generated, [0-9,]+ distinct states found')"
states_generated=""
distinct_states=""
if [[ -n "$states_line" ]]; then
  states_generated="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\1/')"
  distinct_states="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\2/')"
fi

diameter_line="$(extract_metric '^The depth of the complete state graph search is ')"
diameter=""
if [[ -n "$diameter_line" ]]; then
  diameter="$(echo "$diameter_line" | sed -E 's/.* is ([0-9]+).*/\1/')"
fi

runtime_line="$(extract_metric '^Finished in ')"
wall_clock=""
if [[ -n "$runtime_line" ]]; then
  wall_clock="$(echo "$runtime_line" | sed -E 's/^Finished in (.*) at .*/\1/')"
fi

result="FAIL"
if grep -q "No error has been found." "$LOG"; then
  result="PASS"
fi

STAMP="$(date +%Y%m%d)"
OUT="$RESULT_DIR/scale_n7_attack_snapshot_${STAMP}.md"
cat > "$OUT" <<EOF
# n=7 Attack Snapshot

- date: $(date '+%Y-%m-%d %H:%M:%S %Z')
- model: \`MC_AdaptiveAttack\`
- profile: \`n7\` (\`n=7, f=2, q=5, MaxView=2\`)
- result: ${result}
- states generated: ${states_generated}
- distinct states: ${distinct_states}
- diameter: ${diameter}
- wall-clock: ${wall_clock}
- log: \`models/_scale_n7_attack.out\`

Notes:

- this profile is bounded and assumption-explicit.
- this snapshot is a scalability sanity check, not an unbounded proof.
EOF

cp "$OUT" "$RESULT_DIR/scale_n7_attack_latest.md"
echo "Scale snapshot written to: $OUT"
