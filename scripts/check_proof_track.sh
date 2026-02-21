#!/usr/bin/env sh
set -eu

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
SPEC_DIR="$ROOT/specifications"
JAR="$ROOT/tla2tools.jar"

if [ -n "${1:-}" ]; then
    SKIP_TLAPS="$1"
    export SKIP_TLAPS
fi
if [ -n "${2:-}" ]; then
    TLAPS_REFINEMENT="$2"
    export TLAPS_REFINEMENT
fi

if [ ! -f "$JAR" ]; then
    if [ -f "$PWD/tla2tools.jar" ]; then
        ROOT="$PWD"
        SPEC_DIR="$ROOT/specifications"
        JAR="$ROOT/tla2tools.jar"
    else
        echo "Error: tla2tools.jar not found at $JAR"
        exit 1
    fi
fi

PATH_SEP=":"
case "$(uname -s)" in
    CYGWIN*|MINGW*|MSYS*|Windows_NT*|WINDOWS_NT*) PATH_SEP=";" ;;
esac
TLA_LIB=".${PATH_SEP}./modules"

run_sany() {
    module="$1"
    echo "=== SANY check: $module ==="
    (
        cd "$SPEC_DIR"
        java -DTLA-Library="$TLA_LIB" -cp ../tla2tools.jar tla2sany.SANY "$module"
    )
}

resolve_tlapm() {
    if command -v tlapm >/dev/null 2>&1; then
        command -v tlapm
        return 0
    fi
    if [ -x "$HOME/.local/tlaps/bin/tlapm" ]; then
        echo "$HOME/.local/tlaps/bin/tlapm"
        return 0
    fi
    if [ -x "/root/.local/tlaps/bin/tlapm" ]; then
        echo "/root/.local/tlaps/bin/tlapm"
        return 0
    fi
    if command -v wsl >/dev/null 2>&1; then
        if wsl -e /root/.local/tlaps/bin/tlapm --version >/dev/null 2>&1; then
            echo "wsl:/root/.local/tlaps/bin/tlapm"
            return 0
        fi
    fi
    return 1
}

run_sany AdaptiveBFT_Abstract.tla
run_sany AdaptiveBFT_Invariant_Theorems.tla
run_sany AdaptiveBFT_Theorems.tla
run_sany AdaptiveBFT_AbstractBridge_Theorems.tla
run_sany AdaptiveBFT_Refinement.tla
run_sany AdaptiveBFT_Refinement_Theorems.tla
run_sany AdaptiveBFT_Refinement_Kernel.tla
run_sany AdaptiveBFT_Transfer_Kernel.tla
run_sany AdaptiveBFT_MainClaim_Theorems.tla
run_sany AdaptiveBFT_ConcreteBridge_Theorems.tla
run_sany AdaptiveBFT_ConcreteBinding_Theorems.tla
run_sany AdaptiveBFT_ConcreteTransfer_Theorems.tla
run_sany AdaptiveBFT_Liveness_Theorems.tla

if [ "${SKIP_TLAPS:-0}" = "1" ]; then
    echo "Info: SKIP_TLAPS=1; skipping TLAPS proof checking."
    exit 0
fi

if TLAPM_BIN="$(resolve_tlapm)"; then
    TLAPM_WSL=0
    WSL_SPEC_DIR=""
    case "$TLAPM_BIN" in
        wsl:*)
            TLAPM_WSL=1
            WSL_TLAPM_BIN="${TLAPM_BIN#wsl:}"
            WSL_SPEC_DIR="$(wsl -e wslpath -a "$SPEC_DIR" 2>/dev/null | tr -d '\r' | tail -n 1)"
            if [ -z "$WSL_SPEC_DIR" ]; then
                echo "Error: failed to convert SPEC_DIR to WSL path: $SPEC_DIR"
                exit 1
            fi
            ;;
    esac

    run_tlaps_module() {
        module="$1"
        module_timeout="${2:-0}"
        stem="${module%.tla}"
        log="$ROOT/states/.tlaps_${stem}.log"
        mkdir -p "$ROOT/states"
        retries="${TLAPS_RETRY:-2}"
        attempt=1
        while [ "$attempt" -le "$retries" ]; do
            if [ "$TLAPM_WSL" = "1" ]; then
                if [ "$module_timeout" -gt 0 ]; then
                    if wsl -e bash -lc "cd '$WSL_SPEC_DIR' && timeout ${module_timeout}s '$WSL_TLAPM_BIN' -I . -I ./modules '$module'" > "$log" 2>&1; then
                        grep -E "All [0-9]+ obligations? proved" "$log" | tail -n 5 || true
                        return 0
                    fi
                elif wsl -e bash -lc "cd '$WSL_SPEC_DIR' && '$WSL_TLAPM_BIN' -I . -I ./modules '$module'" > "$log" 2>&1; then
                    grep -E "All [0-9]+ obligations? proved" "$log" | tail -n 5 || true
                    return 0
                fi
            else
                if [ "$module_timeout" -gt 0 ] && command -v timeout >/dev/null 2>&1; then
                    if (
                        cd "$SPEC_DIR"
                        timeout "${module_timeout}s" "$TLAPM_BIN" -I . -I ./modules "$module" > "$log" 2>&1
                    ); then
                        grep -E "All [0-9]+ obligations? proved" "$log" | tail -n 5 || true
                        return 0
                    fi
                else
                    if (
                        cd "$SPEC_DIR"
                        "$TLAPM_BIN" -I . -I ./modules "$module" > "$log" 2>&1
                    ); then
                        grep -E "All [0-9]+ obligations? proved" "$log" | tail -n 5 || true
                        return 0
                    fi
                fi
            fi

            if [ "$attempt" -lt "$retries" ]; then
                echo "Warning: TLAPS attempt $attempt/$retries failed for $module; retrying..."
                sleep 1
            fi
            attempt=$((attempt + 1))
        done

        echo "Error: TLAPS failed for $module after $retries attempt(s)"
        cat "$log"
        return 1
    }

    echo "Info: using tlapm at $TLAPM_BIN"
    if [ "${TLAPS_INVARIANT:-1}" = "1" ]; then
        echo "=== TLAPS check: AdaptiveBFT_Invariant_Theorems.tla ==="
        run_tlaps_module AdaptiveBFT_Invariant_Theorems.tla
    else
        echo "Info: skipping TLAPS for AdaptiveBFT_Invariant_Theorems.tla (TLAPS_INVARIANT=0)."
    fi
    echo "=== TLAPS check: AdaptiveBFT_Theorems.tla ==="
    run_tlaps_module AdaptiveBFT_Theorems.tla
    echo "=== TLAPS check: AdaptiveBFT_Refinement_Theorems.tla ==="
    run_tlaps_module AdaptiveBFT_Refinement_Theorems.tla
    echo "=== TLAPS check: AdaptiveBFT_Refinement_Kernel.tla ==="
    run_tlaps_module AdaptiveBFT_Refinement_Kernel.tla
    echo "=== TLAPS check: AdaptiveBFT_Transfer_Kernel.tla ==="
    run_tlaps_module AdaptiveBFT_Transfer_Kernel.tla
    echo "=== TLAPS check: AdaptiveBFT_MainClaim_Theorems.tla ==="
    run_tlaps_module AdaptiveBFT_MainClaim_Theorems.tla
    echo "=== TLAPS check: AdaptiveBFT_Liveness_Theorems.tla ==="
    run_tlaps_module AdaptiveBFT_Liveness_Theorems.tla
    if [ "${TLAPS_CONCRETE_BRIDGE:-1}" = "1" ]; then
        echo "=== TLAPS check: AdaptiveBFT_ConcreteBridge_Theorems.tla ==="
        run_tlaps_module AdaptiveBFT_ConcreteBridge_Theorems.tla
    else
        echo "Info: skipping TLAPS for AdaptiveBFT_ConcreteBridge_Theorems.tla (TLAPS_CONCRETE_BRIDGE=0)."
    fi
    if [ "${TLAPS_CONCRETE_BINDING:-0}" = "1" ]; then
        echo "=== TLAPS check: AdaptiveBFT_ConcreteBinding_Theorems.tla (optional) ==="
        run_tlaps_module AdaptiveBFT_ConcreteBinding_Theorems.tla
    else
        echo "Info: skipping TLAPS for AdaptiveBFT_ConcreteBinding_Theorems.tla by default."
        echo "      Reason: this module is checked in the non-blocking concrete probe;"
        echo "      enable with TLAPS_CONCRETE_BINDING=1 for full proof-track runs."
    fi
    if [ "${TLAPS_CONCRETE_TRANSFER:-0}" = "1" ]; then
        echo "=== TLAPS check: AdaptiveBFT_ConcreteTransfer_Theorems.tla (optional, slow) ==="
        run_tlaps_module AdaptiveBFT_ConcreteTransfer_Theorems.tla "${TLAPS_CONCRETE_TRANSFER_TIMEOUT:-1200}"
    else
        echo "Info: skipping TLAPS for AdaptiveBFT_ConcreteTransfer_Theorems.tla by default."
        echo "      Reason: this module is significantly slower than the main theorem track;"
        echo "      SANY check is enforced in \`make proofs\`, and diagnostics run via"
        echo "      \`make concrete-tlaps-probe\` / \`make concrete-tlaps-probe-full\`."
        echo "      Enable with TLAPS_CONCRETE_TRANSFER=1 (default timeout: 1200s)."
    fi
    if [ "${TLAPS_REFINEMENT:-0}" = "1" ]; then
        echo "=== TLAPS check: AdaptiveBFT_Refinement.tla (experimental) ==="
        if run_tlaps_module AdaptiveBFT_Refinement.tla; then
            echo "Info: full refinement TLAPS check completed."
        else
            echo "Warning: full refinement TLAPS check failed."
            echo "         This path is currently blocked by TLAPS recursive-operator limits"
            echo "         in the concrete dependency graph (e.g., Reputation_Game recursion)."
            echo "         Kernel refinement module remains machine-checked."
        fi
    else
        echo "Info: skipping TLAPS for AdaptiveBFT_Refinement.tla by default."
        echo "      Reason: TLAPS has known limitations with recursive operators imported"
        echo "      from the full concrete model. SANY check is still enforced."
        echo "      Set TLAPS_REFINEMENT=1 to force a direct TLAPS attempt."
    fi
else
    echo "Info: tlapm not found on PATH; skipped TLAPS proof checking."
    echo "      Install TLAPS to discharge theorem obligations."
fi
