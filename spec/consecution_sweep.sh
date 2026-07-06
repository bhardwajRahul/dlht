#!/bin/bash
# Parallel, memory-safe consecution sweep — the practical way to discharge the
# system consecution gate (inv ∧ rsInv INDUCTIVE over systemStep) when the
# monolithic `quint verify --invariant=inv --max-steps=1` is too slow (~15h at
# 2-proc 1gen). Splits the 47 g_* family localizers into N groups, each checked
# concurrently as one `quint verify --invariants ...` on its OWN Apalache server
# (--server-endpoint distinct port — the "one verify at a time" limit is only the
# shared default port 8822).
#
# SOUNDNESS: every group runs from the SAME full anchor (init = systemIndInit =
# invPure ∧ rsInvPure), and the 47 families are a complete, distinct partition of
# inv ∧ rsInv (count==47 AND sort -u ==47 asserted below). So ALL groups [ok] is
# equivalent to the monolithic consecution [ok]. (A SWEEP_FAMILIES SUBSET proves
# ONLY those families, NOT the full gate — the OVERALL verdict says so.) Verdict is read from the
# `[ok] No violation found` / `[violation]` markers, NOT the process exit code
# (quint exits 0 spuriously when its server is killed).
#
# MEMORY SAFETY (learned the hard way): N concurrent Apalache JVMs can exhaust
# RAM and swap-storm the whole machine (every app stalls on page faults). The
# monitor sheds the youngest group ONLY when AVAILABLE RAM (free+inactive+
# speculative+purgeable) stays under AVAIL_FLOOR for 2 samples — the real thrash
# signal. Do NOT shed on swap growth: macOS proactively swaps cold pages while
# avail stays healthy, so a swap trigger only ever false-fires. A shed/reaped
# group lacks a verdict marker => reported INCOMPLETE => re-run it.
#
# Usage:
#   ./consecution_sweep.sh [N] [HEAP] [CFG]
#     N    concurrency / number of groups   (default 6)
#     HEAP per-group JVM -Xmx cap           (default 6g)
#     CFG  the verify config                (default verify/induction_resize_1gen_2proc.qnt;
#                                            pass verify/induction_resize_2gen_2proc.qnt for 2gen)
#   SWEEP_LOGDIR overrides the (transient) per-group log dir (default /tmp/dlht-sweep).
#   Run detached + caffeinated for a long run, e.g.:
#     nohup caffeinate -dimsu ./consecution_sweep.sh > /tmp/dlht-sweep/sweep.log 2>&1 & disown
set -uo pipefail
cd "$(dirname "$0")"   # => spec/, so CFG paths resolve like verify.sh

N=${1:-6}
HEAP=${2:-6g}
CFG=${3:-verify/induction_resize_1gen_2proc.qnt}
LOGDIR=${SWEEP_LOGDIR:-/tmp/dlht-sweep}     # transient per-run logs (NOT source)
export OUT_DIR="${APALACHE_OUT_DIR:-/tmp/dlht-apalache-out}"
STAGGER=${SWEEP_STAGGER:-15}   # s between launches — avoids the gRPC handshake-hang startup race (override for tests)
REAP_AFTER=180      # s after start to test each group for a handshake hang
AVAIL_FLOOR=2500    # MB of available RAM below which (for 2 consecutive samples) we shed
SHED_DELTA=9999999  # swap-growth trigger DISABLED on purpose (avail is the only reliable signal)

[[ -f "$CFG" ]] || { echo "FATAL: config not found: $CFG (run from spec/ or pass a valid path)"; exit 1; }
mkdir -p "$LOGDIR"

# The complete g_* partition of inv ∧ rsInv (33 invPure families incl typeOK + 14 rsInvPure).
# SWEEP_FAMILIES (space-separated g_* names) overrides this with a SUBSET for
# targeted re-verification of specific families; the full-47 completeness assertion
# is skipped for a subset, but the no-duplicates assertion always applies.
if [[ -n "${SWEEP_FAMILIES:-}" ]]; then FAMILIES=($SWEEP_FAMILIES); else
FAMILIES=(
  g_typeOK g_visibleSlotsWellFormed g_hashConsistency g_tryingOwnedUnique
  g_shadowOwnedUnique g_shadowSlotKeyed g_tagMonotonic g_tagValPaired
  g_invalidSlotClean g_liveKeyUniquePerBin g_deleteWindowOwned g_targetSlotInRange
  g_ownerSlotStateConsistent g_ownerSlotFilled g_retAtD8 g_retAtLC9
  g_pendingRetOnlyInRetWindow g_d8WindowOwnerUnique g_reservedKeyFresh
  g_reservedKeyFreshAtReserve g_reserveBumpedVersion g_reserveHeaderAgrees
  g_loopSlotValidAtCommit g_commitTagImpliesValid g_versionMonotonic
  g_snapStateAgrees g_freshReservationEmpty g_absentReturnConsistent
  g_genTopology g_pristineFutureGens g_predecessorsDone g_opGenSanity
  g_entryKeyAgreement
  g_rsSnapshotRelation g_rsSentinelDiscipline g_rsChildUnobservable
  g_rsCursorCoherence g_rsCompleteness g_rsChildFreeSlot g_rsClaimContinuity
  g_h0LoadedNoTransfer g_rsChildKeyFresh g_hLoopLoadedNoTransfer
  g_shadowGhostForm g_lc10AtDone g_tryingOwnerUnique g_carriedClaimExists
)
fi
TOTAL=${#FAMILIES[@]}
[[ -n "${SWEEP_FAMILIES:-}" ]] || [[ "$TOTAL" -eq 47 ]] || { echo "FATAL: expected 47 families, got $TOTAL"; exit 1; }
UNIQ=$(printf '%s\n' "${FAMILIES[@]}" | sort -u | wc -l | tr -d ' '); [[ "$UNIQ" -eq "$TOTAL" ]] || { echo "FATAL: duplicate families ($UNIQ unique of $TOTAL)"; exit 1; }

avail_mb() { vm_stat 2>/dev/null | awk '/page size of/{for(i=1;i<=NF;i++) if($i ~ /^[0-9]+$/){ps=$i;break}} /^Pages free/{gsub(/\./,"",$3);f=$3} /^Pages inactive/{gsub(/\./,"",$3);n=$3} /^Pages speculative/{gsub(/\./,"",$3);s=$3} /^Pages purgeable/{gsub(/\./,"",$3);p=$3} END{if(ps>0) print int((f+n+s+p)*ps/1048576); else print -1}'; }
swap_used_mb() { sysctl -n vm.swapusage 2>/dev/null | sed -E 's/.*used = ([0-9.]+)M.*/\1/' | cut -d. -f1; }
server_cpu_on_port() { local pid; pid=$(lsof -nP -iTCP:"$1" -sTCP:LISTEN -t 2>/dev/null | head -1); [[ -z "$pid" ]] && { echo 0; return; }; ps -p "$pid" -o time= 2>/dev/null | awk -F'[:.]' '{ if (NF>=3) print $1*60+$2; else print 0 }' || echo 0; }
kill_group() { kill -9 "${PID[$1]}" 2>/dev/null; lsof -nP -iTCP:"${PORT[$1]}" -sTCP:LISTEN -t 2>/dev/null | xargs kill -9 2>/dev/null; }

echo "START sweep $(date): CFG=$CFG groups=$N heap=$HEAP nice=10 avail_floor=${AVAIL_FLOOR}MB logs=$LOGDIR (start avail=$(avail_mb)MB swap=$(swap_used_mb)MB)"
declare -a GROUP
for g in $(seq 0 $((N-1))); do GROUP[$g]=""; done   # pre-init: set -u tolerates the accumulation, and N>#families stays safe
for i in "${!FAMILIES[@]}"; do GROUP[$(( i % N ))]="${GROUP[$(( i % N ))]} ${FAMILIES[$i]}"; done

pkill -9 -f 'apalache.jar server' 2>/dev/null || true; sleep 1
declare -a PID PORT
for g in $(seq 0 $((N-1))); do
  PORT[$g]=$((8830 + g)); log="$LOGDIR/grp${g}.log"
  echo "group $g -> :${PORT[$g]}  families:${GROUP[$g]}"
  JVM_ARGS=-Xmx$HEAP nice -n 10 quint verify "$CFG" --max-steps=1 --server-endpoint=localhost:${PORT[$g]} --invariants ${GROUP[$g]} > "$log" 2>&1 &
  PID[$g]=$!
  sleep "$STAGGER"
done
echo "all launched $(date): pids ${PID[*]}"

base_swap=$(swap_used_mb)
( reaped=0; t=0; breach=0
  while :; do
    sleep 30; t=$((t+30))
    any=0; for g in $(seq 0 $((N-1))); do kill -0 "${PID[$g]}" 2>/dev/null && any=1; done
    [[ $any -eq 0 ]] && break
    if [[ $reaped -eq 0 && $t -ge $REAP_AFTER ]]; then reaped=1
      for g in $(seq 0 $((N-1))); do kill -0 "${PID[$g]}" 2>/dev/null || continue
        [[ "$(server_cpu_on_port ${PORT[$g]})" -lt 15 ]] && { echo "MONITOR: group $g handshake-hung — killing" >>"$LOGDIR/grp${g}.log"; kill_group $g; }
      done
    fi
    av=$(avail_mb); sw=$(( $(swap_used_mb) - base_swap ))
    danger=0
    { [[ "$av" -gt 0 && "$av" -lt "$AVAIL_FLOOR" ]]; } && danger=1
    [[ "$sw" -gt "$SHED_DELTA" ]] && danger=1
    if [[ $danger -eq 1 ]]; then breach=$((breach+1)); else breach=0; fi
    echo "MONITOR t=${t}s avail=${av}MB swap+${sw}MB breach=$breach" >> "$LOGDIR/mon.log"
    if [[ $breach -ge 2 ]]; then
      for g in $(seq $((N-1)) -1 0); do
        if kill -0 "${PID[$g]}" 2>/dev/null; then echo "MONITOR: sustained memory pressure (avail=${av}MB swap+${sw}MB) — SHEDDING group $g" | tee -a "$LOGDIR/grp${g}.log"; kill_group $g; break; fi
      done
      breach=0; sleep 45; base_swap=$(swap_used_mb)
    fi
  done ) &
MON=$!

for g in $(seq 0 $((N-1))); do wait "${PID[$g]}" 2>/dev/null; done
kill "$MON" 2>/dev/null || true

echo "=== VERDICTS $(date) ==="
allok=1
for g in $(seq 0 $((N-1))); do
  log="$LOGDIR/grp${g}.log"
  if   grep -q "\[ok\] No violation found" "$log"; then echo "group $g: [ok] $(grep -oE '\([0-9]+ms\)' "$log" | tail -1)"
  elif grep -q "\[violation\]" "$log"; then echo "group $g: [VIOLATION]"; grep -iE "violation|does not hold|violated" "$log" | head -6; allok=0
  else echo "group $g: INCOMPLETE (shed/reaped/crash — re-run)"; tail -3 "$log"; allok=0
  fi
done
if [ "$allok" -eq 1 ]; then
  if [ -n "${SWEEP_FAMILIES:-}" ]; then
    echo "=== OVERALL: SUBSET ALL [ok] ($TOTAL of 47 families) -- subset evidence only, NOT the full gate ==="
  else
    echo "=== OVERALL: ALL [ok] -- full 47-family consecution GREEN (gate met for this CFG) ==="
  fi
else
  echo "=== OVERALL: NOT all green -- re-run INCOMPLETE/violation groups ==="
fi
echo "END $(date)"; echo SWEEP_ALLDONE
