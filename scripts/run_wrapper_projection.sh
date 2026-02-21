#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"
STAMP="$(date +%Y%m%d-%H%M%S)"
OUT_MD="$RESULT_DIR/wrapper_projection_${STAMP}.md"
LATEST_MD="$RESULT_DIR/wrapper_projection_latest.md"

mkdir -p "$RESULT_DIR"

modes=(attack aps joint)
profiles=(baseline mv4)

declare -A states_map
declare -A distinct_map
declare -A depth_map
declare -A wall_map
declare -A result_map

for profile in "${profiles[@]}"; do
  for mode in "${modes[@]}"; do
    key="${profile}_${mode}"
    log="$LOG_DIR/_wrapper_projection_${profile}_${mode}.out"

    echo "=== wrapper projection: profile=${profile}, mode=${mode} ===" | tee "$log"
    (
      cd "$ROOT"
      bash ./run.sh "$mode" "$profile"
    ) | tee -a "$log"

    result_map["$key"]="FAIL"
    if grep -q "No error has been found." "$log"; then
      result_map["$key"]="PASS"
    fi

    states_line="$(grep -E '^[0-9,]+ states generated, [0-9,]+ distinct states found' "$log" | tail -1 || true)"
    if [[ -n "$states_line" ]]; then
      states_map["$key"]="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\1/')"
      distinct_map["$key"]="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\2/')"
    else
      states_map["$key"]="-"
      distinct_map["$key"]="-"
    fi

    depth_line="$(grep -E '^The depth of the complete state graph search is ' "$log" | tail -1 || true)"
    if [[ -n "$depth_line" ]]; then
      depth_map["$key"]="$(echo "$depth_line" | sed -E 's/.* is ([0-9]+).*/\1/')"
    else
      depth_map["$key"]="-"
    fi

    wall_line="$(grep -E '^Finished in ' "$log" | tail -1 || true)"
    if [[ -n "$wall_line" ]]; then
      wall_map["$key"]="$(echo "$wall_line" | sed -E 's/^Finished in (.*) at .*/\1/')"
    else
      wall_map["$key"]="-"
    fi
  done
done

cat > "$OUT_MD" <<EOF
# Wrapper Projection Snapshot (${STAMP})

Properties checked in wrappers:

- \`InitProjectionCheckedAttack\`, \`StepProjectionCheckedAttack\`, \`StepBoxProjectionCheckedAttack\`, \`SpecProjectionCheckedAttack\`
- \`SpecToAbstractSpecCheckedAttack\`
- \`InitProjectionCheckedAPS\`, \`StepProjectionCheckedAPS\`, \`StepBoxProjectionCheckedAPS\`, \`SpecProjectionCheckedAPS\`
- \`SpecToAbstractSpecCheckedAPS\`
- \`InitProjectionCheckedJoint\`, \`StepProjectionCheckedJoint\`, \`StepBoxProjectionCheckedJoint\`, \`SpecProjectionCheckedJoint\`
- \`SpecToAbstractSpecCheckedJoint\`

## baseline (MaxView=2)

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| \`MC_AdaptiveAttack\` | ${states_map[baseline_attack]} | ${distinct_map[baseline_attack]} | ${depth_map[baseline_attack]} | ${wall_map[baseline_attack]} | ${result_map[baseline_attack]} |
| \`MC_LivenessAPS\` | ${states_map[baseline_aps]} | ${distinct_map[baseline_aps]} | ${depth_map[baseline_aps]} | ${wall_map[baseline_aps]} | ${result_map[baseline_aps]} |
| \`MC_LivenessAPSAttack\` | ${states_map[baseline_joint]} | ${distinct_map[baseline_joint]} | ${depth_map[baseline_joint]} | ${wall_map[baseline_joint]} | ${result_map[baseline_joint]} |

## mv4 (MaxView=4)

| Model | States generated | Distinct states | Diameter | Wall-clock | TLC result |
|---|---:|---:|---:|---:|---|
| \`MC_AdaptiveAttack\` | ${states_map[mv4_attack]} | ${distinct_map[mv4_attack]} | ${depth_map[mv4_attack]} | ${wall_map[mv4_attack]} | ${result_map[mv4_attack]} |
| \`MC_LivenessAPS\` | ${states_map[mv4_aps]} | ${distinct_map[mv4_aps]} | ${depth_map[mv4_aps]} | ${wall_map[mv4_aps]} | ${result_map[mv4_aps]} |
| \`MC_LivenessAPSAttack\` | ${states_map[mv4_joint]} | ${distinct_map[mv4_joint]} | ${depth_map[mv4_joint]} | ${wall_map[mv4_joint]} | ${result_map[mv4_joint]} |
EOF

cp "$OUT_MD" "$LATEST_MD"

echo "Wrapper projection snapshot written to: $OUT_MD"
echo "Latest wrapper projection snapshot: $LATEST_MD"
