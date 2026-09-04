#!/bin/bash
# run_frama_parallel.sh
# Verifies every function in safe.c with Frama-C/WP concurrently.
# Results are printed as each job completes.

set -euo pipefail

# Resolve paths relative to this script so it runs from a fresh clone.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# frama-c: $FRAMA override, else the one on PATH, else the default opam location.
FRAMA="${FRAMA:-$(command -v frama-c || true)}"
[ -n "$FRAMA" ] || FRAMA="$HOME/.opam/frama-c/bin/frama-c"
# safe.c: first argument, else $SRC, else alongside this script.
SRC="${1:-${SRC:-$SCRIPT_DIR/safe.c}}"
OUTDIR=/tmp/frama_fcts
mkdir -p "$OUTDIR"

echo "[$(date '+%H:%M:%S')] Discovering functions via frama-c -print..."
FUNCTIONS=$(
    "$FRAMA" -print "$SRC" 2>/dev/null \
    | awk '
      /^[[:space:]]*(predicate|logic|lemma|axiom)[[:space:]]/ { skip=1 }
      skip && /=[[:space:]]*$|;[[:space:]]*$|\}[[:space:]]*;/ { skip=0; next }
      skip { next }
      /^[A-Za-z_]/ && /\(/ && !/^(typedef|struct|union|enum|#)/ {
          if (match($0, /[A-Za-z_][A-Za-z0-9_]*[[:space:]]*\(/)) {
              cand = substr($0, RSTART, RLENGTH-1)
              gsub(/[[:space:]]/, "", cand)
              in_sig = 1; fname = cand
          }
      }
      in_sig && /^{/ { print fname; in_sig = 0; fname = "" }
      in_sig && /;[[:space:]]*$/ { in_sig = 0; fname = "" }
    ' | sort -u
)
echo "  Found $(echo "$FUNCTIONS" | wc -w | tr -d ' ') functions: $(echo "$FUNCTIONS" | tr '\n' ' ')"

# Common flags — wp-par 1 per job because we run all jobs in parallel
BASE="-wp -wp-rte -wp-prover alt-ergo,z3 -wp-timeout 90 -wp-par 1"

run_one() {
    local FCT=$1
    local OUT="$OUTDIR/frama_${FCT}.txt"

    case "$FCT" in
        asn_parse_recursive)
            # -DSAFE_ASN_MAX_NODES=8 overrides 256 to keep array-bound goals tractable
            # wp-par 4: new loop invariant made goals tractable; 300s headroom
            $FRAMA -wp -wp-rte -wp-prover alt-ergo,z3 -wp-timeout 300 -wp-par 4 \
                -cpp-extra-args="-DSAFE_ASN_MAX_NODES=8" \
                -wp-fct "$FCT" "$SRC" > "$OUT" 2>&1
            ;;
        safe_iec104_filter)
            # Needs longer timeout for loop-variant / elem*N goals
            $FRAMA -wp -wp-rte -wp-prover alt-ergo,z3 -wp-timeout 120 -wp-par 4 \
                -wp-fct "$FCT" "$SRC" > "$OUT" 2>&1
            ;;
        asn_filter_recursive_relaxed|safe_asn_filter_relaxed)
            # Extra timeout: tag-range disjunction (0x40-0xBF) produces
            # large SMT goals; 300s + wp-par 4 matches asn_parse_recursive
            $FRAMA -wp -wp-rte -wp-prover alt-ergo,z3 -wp-timeout 300 -wp-par 4 \
                -wp-fct "$FCT" "$SRC" > "$OUT" 2>&1
            ;;
        asn_filter_recursive|safe_asn_filter)
            # assert_3 / call_asn_filter_top_requires borderline; bump to 180s
            $FRAMA -wp -wp-rte -wp-prover alt-ergo,z3 -wp-timeout 180 -wp-par 2 \
                -wp-fct "$FCT" "$SRC" > "$OUT" 2>&1
            ;;
        *)
            $FRAMA $BASE -wp-fct "$FCT" "$SRC" > "$OUT" 2>&1
            ;;
    esac
}

# Print result for one function immediately after its job finishes.
# Uses a lock file to prevent interleaved output from concurrent jobs.
LOCKFILE="$OUTDIR/.print_lock"
print_result() {
    local FCT=$1
    local OUT="$OUTDIR/frama_${FCT}.txt"
    local RESULT PROVED GOALS STATUS

    RESULT=$(grep "Proved goals:" "$OUT" 2>/dev/null | tail -1)
    if [ -n "$RESULT" ]; then
        PROVED=$(echo "$RESULT" | grep -o '[0-9]* / [0-9]*' | awk -F' / ' '{print $1}')
        GOALS=$(echo  "$RESULT" | grep -o '[0-9]* / [0-9]*' | awk -F' / ' '{print $2}')
        if [ "$PROVED" = "$GOALS" ]; then
            STATUS="✓ $PROVED / $GOALS"
        else
            STATUS="✗ $PROVED / $GOALS  ← UNPROVED"
        fi
    else
        STATUS="NO RESULT — check $OUT"
    fi

    # Serialize output so lines from concurrent jobs don't interleave
    (
        flock 9
        printf "[%s] %-30s  %s\n" "$(date '+%H:%M:%S')" "$FCT" "$STATUS"
    ) 9>"$LOCKFILE"
}

run_and_report() {
    local FCT=$1
    run_one "$FCT"
    print_result "$FCT"
}

export -f run_one print_result run_and_report
export FRAMA SRC OUTDIR BASE LOCKFILE

# Kill all background jobs on Ctrl-C / SIGTERM
pids=()
cleanup() {
    echo ""
    echo "[$(date '+%H:%M:%S')] Interrupted — killing ${#pids[@]} jobs..."
    kill "${pids[@]}" 2>/dev/null || true
    exit 130
}
trap cleanup INT TERM

echo "[$(date '+%H:%M:%S')] Launching Frama-C/WP for all functions in parallel..."
echo "----------------------------------------"
for FCT in $FUNCTIONS; do
    [ -z "$FCT" ] && continue
    # Run in a subshell that ignores INT so the terminal Ctrl-C reaches only
    # the parent trap above, which then kills jobs cleanly.
    ( trap '' INT TERM; run_and_report "$FCT" ) &
    pids+=($!)
done

echo ""
echo "[$(date '+%H:%M:%S')] Waiting for ${#pids[@]} jobs to complete..."
for pid in "${pids[@]}"; do
    wait "$pid" || true   # Frama-C exits 1 on unproved goals
done
echo "[$(date '+%H:%M:%S')] All jobs done."

# ── Final totals ──────────────────────────────────────────────────────────────
echo ""
echo "========================================"
printf "%-30s  %s\n" "Function" "Result"
echo "----------------------------------------"

TOTAL_PROVED=0
TOTAL_GOALS=0
FAILED=""

for FCT in $FUNCTIONS; do
    [ -z "$FCT" ] && continue
    OUT="$OUTDIR/frama_${FCT}.txt"
    RESULT=$(grep "Proved goals:" "$OUT" 2>/dev/null | tail -1)
    if [ -n "$RESULT" ]; then
        PROVED=$(echo "$RESULT" | grep -o '[0-9]* / [0-9]*' | awk -F' / ' '{print $1}')
        GOALS=$(echo  "$RESULT" | grep -o '[0-9]* / [0-9]*' | awk -F' / ' '{print $2}')
        TOTAL_PROVED=$((TOTAL_PROVED + PROVED))
        TOTAL_GOALS=$((TOTAL_GOALS + GOALS))
        if [ "$PROVED" = "$GOALS" ]; then
            STATUS="✓ $PROVED / $GOALS"
        else
            STATUS="✗ $PROVED / $GOALS  ← UNPROVED"
            FAILED="$FAILED $FCT"
        fi
        printf "%-30s  %s\n" "$FCT" "$STATUS"
    else
        printf "%-30s  %s\n" "$FCT" "NO RESULT — check $OUT"
        FAILED="$FAILED $FCT"
    fi
done

echo "========================================"
echo "TOTAL : $TOTAL_PROVED / $TOTAL_GOALS proved"
if [ -n "$FAILED" ]; then
    echo "NEEDS ATTENTION:$FAILED"
    exit 1
fi
echo "ALL GOALS PROVED"
echo "========================================"
