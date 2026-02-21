#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# AdaptiveBFT verification runner
# -----------------------------------------------------------------------------

# 1) Ensure Java is available
if ! command -v java >/dev/null 2>&1; then
    echo "Error: Java is not installed. Please install Java 11+."
    exit 1
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# 2) Resolve tla2tools.jar
if [[ -n "${TLA2TOOLS_JAR:-}" && -f "$TLA2TOOLS_JAR" ]]; then
    JAR="$TLA2TOOLS_JAR"
elif [[ -f "$ROOT/tla2tools.jar" ]]; then
    JAR="$ROOT/tla2tools.jar"
elif [[ -f "$ROOT/../tla2tools.jar" ]]; then
    JAR="$ROOT/../tla2tools.jar"
else
    echo "Error: tla2tools.jar not found. Set TLA2TOOLS_JAR or place it in $ROOT or its parent."
    exit 1
fi

# 3) Configure TLA+ module search path
PATH_SEP=":"
case "$(uname -s)" in
    CYGWIN*|MINGW*|MSYS*) PATH_SEP=";" ;;
esac
TLA_LIBRARY="$ROOT${PATH_SEP}$ROOT/specifications${PATH_SEP}$ROOT/specifications/modules"

# 4) Run selected model
MODE="${1:-}"
PROFILE="${2:-baseline}"
RECOVER_PATH="${3:-}"
JAVA_OPTS_STR="${JAVA_OPTS:-"-Xmx8G -XX:+UseParallelGC"}"
read -r -a JAVA_OPTS <<< "$JAVA_OPTS_STR"

if [[ -n "${TLC_WORKERS:-}" ]]; then
    WORKERS="$TLC_WORKERS"
elif [[ "$MODE" = "attack" || "$MODE" = "transfer" ]]; then
    # Attack model has the largest frontier; cap workers by default to reduce OOM risk.
    WORKERS=4
else
    WORKERS=auto
fi

RECOVER_ARGS=()
if [[ -n "$RECOVER_PATH" ]]; then
    RECOVER_ARGS=(-recover "$RECOVER_PATH")
elif [[ -n "${TLC_RECOVER:-}" ]]; then
    RECOVER_ARGS=(-recover "$TLC_RECOVER")
fi

case "$PROFILE" in
    baseline) CFG_SUFFIX="" ;;
    mv3) CFG_SUFFIX="_MV3" ;;
    mv4) CFG_SUFFIX="_MV4" ;;
    mv5) CFG_SUFFIX="_MV5" ;;
    n7) CFG_SUFFIX="_N7" ;;
    n7lite) CFG_SUFFIX="_N7LITE" ;;
    *)
        echo "Error: unknown profile '$PROFILE'. Use: baseline | mv3 | mv4 | mv5 | n7 | n7lite"
        exit 1
        ;;
esac

resolve_cfg() {
    local model="$1"
    local cfg="$ROOT/models/${model}${CFG_SUFFIX}.cfg"
    if [[ ! -f "$cfg" ]]; then
        echo "Error: config not found for model '$model' and profile '$PROFILE': $cfg"
        exit 1
    fi
    echo "$cfg"
}

if [ "$MODE" = "attack" ]; then
    echo "=================================================="
    echo ">>> Running AVC Security Test (Adaptive Attack, profile=$PROFILE)..."
    echo "=================================================="
    CFG="$(resolve_cfg MC_AdaptiveAttack)"
    java "${JAVA_OPTS[@]}" "-DTLA-Library=$TLA_LIBRARY" -jar "$JAR" "$ROOT/models/MC_AdaptiveAttack.tla" -config "$CFG" -workers "$WORKERS" "${RECOVER_ARGS[@]}" -deadlock

elif [ "$MODE" = "aps" ]; then
    echo "=================================================="
    echo ">>> Running APS Liveness Test (Scheduling, profile=$PROFILE)..."
    echo "=================================================="
    CFG="$(resolve_cfg MC_LivenessAPS)"
    java "${JAVA_OPTS[@]}" "-DTLA-Library=$TLA_LIBRARY" -jar "$JAR" "$ROOT/models/MC_LivenessAPS.tla" -config "$CFG" -workers "$WORKERS" "${RECOVER_ARGS[@]}" -deadlock

elif [ "$MODE" = "joint" ]; then
    echo "=================================================="
    echo ">>> Running Joint Liveness Test (APS + Adaptive Attack, profile=$PROFILE)..."
    echo "=================================================="
    CFG="$(resolve_cfg MC_LivenessAPSAttack)"
    java "${JAVA_OPTS[@]}" "-DTLA-Library=$TLA_LIBRARY" -jar "$JAR" "$ROOT/models/MC_LivenessAPSAttack.tla" -config "$CFG" -workers "$WORKERS" "${RECOVER_ARGS[@]}" -deadlock

elif [ "$MODE" = "transfer" ]; then
    echo "=================================================="
    echo ">>> Running Refinement Transfer Check (Concrete -> Abstract, profile=$PROFILE)..."
    echo "=================================================="
    CFG="$(resolve_cfg MC_RefinementTransfer)"
    java "${JAVA_OPTS[@]}" "-DTLA-Library=$TLA_LIBRARY" -jar "$JAR" "$ROOT/models/MC_RefinementTransfer.tla" -config "$CFG" -workers "$WORKERS" "${RECOVER_ARGS[@]}"

else
    echo "Usage: ./run.sh [attack|aps|joint|transfer] [baseline|mv3|mv4|mv5|n7|n7lite] [recoverPath(optional)]"
    echo "  attack : Run validation for Adaptive View-Change (Security)"
    echo "  aps    : Run validation for Adaptive Pipeline Scheduling (Liveness)"
    echo "  joint  : Run joint liveness for APS under adaptive attack"
    echo "  transfer: Run refinement transfer checks (projection init/step obligations)"
    echo "  profile baseline: use MaxView=2 configs"
    echo "  profile mv3     : use MaxView=3 / richer Tx configs"
    echo "  profile mv4     : use MaxView=4 configs"
    echo "  profile mv5     : use MaxView=5 configs"
    echo "  profile n7      : use n=7,f=2,q=5 scalability configs (bounded)"
    echo "  profile n7lite  : use n=7,f=2,q=5 quick full-suite configs (MaxView=1)"
    exit 1
fi
