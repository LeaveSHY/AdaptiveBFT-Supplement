#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="$ROOT/docs/results"
LOG_DIR="$ROOT/models"

mkdir -p "$RESULT_DIR"
mkdir -p "$LOG_DIR"

if [[ "$#" -gt 0 ]]; then
    PROFILES=("$@")
else
    PROFILES=("baseline" "mv3" "mv4")
fi

MODELS=("attack" "aps" "joint")
STAMP="$(date +%Y%m%d-%H%M%S)"
CSV="$RESULT_DIR/tlc_matrix_${STAMP}.csv"
TMP="$RESULT_DIR/tlc_matrix_${STAMP}.partial"
PROGRESS="$RESULT_DIR/tlc_matrix_progress_${STAMP}.csv"
PROGRESS_LATEST="$RESULT_DIR/tlc_matrix_progress_latest.csv"
MODE_TIMEOUT_SEC="${MODE_TIMEOUT_SEC:-0}"

echo "profile,model,result,states_generated,distinct_states,diameter,wall_clock,log_file" > "$TMP"

extract_metric() {
    local regex="$1"
    local file="$2"
    grep -E "$regex" "$file" | tail -1 || true
}

run_mode() {
    local model="$1"
    local profile="$2"
    if [[ "$MODE_TIMEOUT_SEC" =~ ^[0-9]+$ ]] && [[ "$MODE_TIMEOUT_SEC" -gt 0 ]]; then
        timeout "$MODE_TIMEOUT_SEC" bash ./run.sh "$model" "$profile"
        return $?
    fi
    bash ./run.sh "$model" "$profile"
}

timed_out=0
failed=0

for profile in "${PROFILES[@]}"; do
    for model in "${MODELS[@]}"; do
        log="$LOG_DIR/_matrix_${profile}_${model}.out"
        echo "=== profile=${profile}, model=${model} ===" | tee "$log"
        set +e
        (
            cd "$ROOT"
            run_mode "$model" "$profile"
        ) | tee -a "$log"
        rc=${PIPESTATUS[0]}
        set -e

        states_line="$(extract_metric '^[0-9,]+ states generated, [0-9,]+ distinct states found' "$log")"
        states_generated=""
        distinct_states=""
        if [[ -n "$states_line" ]]; then
            states_generated="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\1/')"
            distinct_states="$(echo "$states_line" | sed -E 's/^([0-9,]+) states generated, ([0-9,]+) distinct states found.*/\2/')"
        fi

        diameter_line="$(extract_metric '^The depth of the complete state graph search is ' "$log")"
        diameter=""
        if [[ -n "$diameter_line" ]]; then
            diameter="$(echo "$diameter_line" | sed -E 's/.* is ([0-9]+).*/\1/')"
        fi

        runtime_line="$(extract_metric '^Finished in ' "$log")"
        wall_clock=""
        if [[ -n "$runtime_line" ]]; then
            wall_clock="$(echo "$runtime_line" | sed -E 's/^Finished in (.*) at .*/\1/')"
        fi

        result="FAIL"
        if [[ "$rc" -eq 124 ]]; then
            timed_out=1
            result="TIMEOUT"
            wall_clock=">${MODE_TIMEOUT_SEC}s (timeout)"
            pkill -f "tlc2.TLC" >/dev/null 2>&1 || true
            pkill -f "tla2tools.jar" >/dev/null 2>&1 || true
            if command -v powershell.exe >/dev/null 2>&1; then
                powershell.exe -NoProfile -Command 'Get-Process java -ErrorAction SilentlyContinue | Stop-Process -Force' >/dev/null 2>&1 || true
            fi
        elif grep -q "No error has been found." "$log"; then
            result="PASS"
        else
            failed=1
        fi

        echo "${profile},${model},${result},${states_generated},${distinct_states},${diameter},\"${wall_clock}\",${log}" >> "$TMP"
    done
done

if [[ "$timed_out" -eq 1 ]] || [[ "$failed" -eq 1 ]]; then
    mv "$TMP" "$PROGRESS"
    cp "$PROGRESS" "$PROGRESS_LATEST"
    echo "Matrix run ended without full PASS coverage."
    echo "Progress artifact written to: $PROGRESS"
    echo "Latest progress artifact: $PROGRESS_LATEST"
    if [[ "$timed_out" -eq 1 ]]; then
        echo "At least one model timed out (MODE_TIMEOUT_SEC=$MODE_TIMEOUT_SEC)."
    fi
    exit 2
fi

mv "$TMP" "$CSV"
echo "Matrix results written to: $CSV"
