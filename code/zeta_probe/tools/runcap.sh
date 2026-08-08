#!/bin/bash
# runcap.sh -- run a command under a hard RSS ceiling and a wall-clock timeout.
#
# macOS supplies no working address-space rlimit: `ulimit -v` returns
# "cannot modify limit: Invalid argument" and setrlimit(RLIMIT_AS/DATA) raises
# EINVAL even though the reported hard limit is RLIM_INFINITY.  So a process
# that allocates without bound will swap the machine to death rather than get a
# MemoryError.  This wrapper supplies the missing ceiling from outside: it runs
# the command in its own process group and polls the group's total RSS, killing
# the whole group the moment it crosses the cap.
#
# Usage:  runcap.sh <cap_mb> <timeout_s> <command> [args...]
# Exit:   the command's own status, or 137 (killed on RSS), or 124 (timeout).
#
# Rule 8 (MATH_RESEARCH_RULES): every enumeration runs under this.

set -uo pipefail

if [ "$#" -lt 3 ]; then
    echo "usage: runcap.sh <cap_mb> <timeout_s> <command> [args...]" >&2
    exit 2
fi

CAP_MB="$1"; shift
TIMEOUT_S="$1"; shift
CAP_KB=$(( CAP_MB * 1024 ))

# Own process group, so one kill takes the command and everything it spawned.
set -m
"$@" &
CHILD=$!
PGID=$(ps -o pgid= -p "$CHILD" 2>/dev/null | tr -d ' ')
set +m

if [ -z "$PGID" ]; then
    wait "$CHILD"
    exit $?
fi

# A 1 s poll is far too slow: a tight allocation loop reached 8.9 GB between two
# samples in testing.  Poll at 10 Hz, and additionally abort if the machine's own
# free memory falls below FREE_FLOOR_MB, which is the condition that actually
# hurts (swap death) regardless of whose RSS caused it.
POLL=0.1
TICKS_PER_S=10

# System-pressure floor, as a PERCENTAGE.  The first version of this script summed
# vm_stat's "Pages free" + "Pages speculative" and compared against an MB floor.
# That is the wrong measure on macOS: the VM keeps free pages deliberately low and
# holds most reclaimable memory as inactive / file-backed / compressed, so the sum
# reads a few hundred MB on a perfectly healthy machine and a 3 GB floor trips
# immediately -- it killed two legitimate audit runs before it was caught.  Use the
# figure macOS itself reports, `memory_pressure`'s "System-wide memory free
# percentage", which accounts for reclaimable pages.  If the tool is missing the
# check is skipped and the per-group RSS cap stands alone.
FREE_FLOOR_PCT=${RUNCAP_FREE_FLOOR_PCT:-15}

PEAK_KB=0
TICKS=0
ELAPSED=0
REASON="ok"

while kill -0 "$CHILD" 2>/dev/null; do
    # Total RSS over the whole process group, in KB.
    RSS_KB=$(ps -A -o rss=,pgid= 2>/dev/null \
             | awk -v g="$PGID" '$2 == g { s += $1 } END { print s+0 }')
    [ "$RSS_KB" -gt "$PEAK_KB" ] && PEAK_KB=$RSS_KB

    if [ "$RSS_KB" -gt "$CAP_KB" ]; then
        REASON="rss"
        echo "runcap: RSS $((RSS_KB/1024)) MB exceeded cap ${CAP_MB} MB -- killing group $PGID" >&2
        kill -9 -"$PGID" 2>/dev/null
        break
    fi

    # System-pressure floor, checked once a second (memory_pressure is not cheap).
    if [ $(( TICKS % TICKS_PER_S )) -eq 0 ] && command -v memory_pressure >/dev/null 2>&1; then
        FREE_PCT=$(memory_pressure 2>/dev/null \
                   | awk '/System-wide memory free percentage/ { gsub(/%/,""); print $NF }')
        if [ -n "$FREE_PCT" ] && [ "$FREE_PCT" -lt "$FREE_FLOOR_PCT" ]; then
            REASON="lowmem"
            echo "runcap: system memory free ${FREE_PCT}% below floor ${FREE_FLOOR_PCT}% -- killing group $PGID" >&2
            kill -9 -"$PGID" 2>/dev/null
            break
        fi
    fi

    if [ "$ELAPSED" -ge "$TIMEOUT_S" ]; then
        REASON="timeout"
        echo "runcap: wall clock ${ELAPSED}s exceeded ${TIMEOUT_S}s -- killing group $PGID" >&2
        kill -9 -"$PGID" 2>/dev/null
        break
    fi

    sleep "$POLL"
    TICKS=$(( TICKS + 1 ))
    ELAPSED=$(( TICKS / TICKS_PER_S ))
done

wait "$CHILD" 2>/dev/null
STATUS=$?

echo "runcap: peak RSS $((PEAK_KB/1024)) MB / cap ${CAP_MB} MB, ${ELAPSED}s / ${TIMEOUT_S}s, reason=$REASON" >&2

case "$REASON" in
    rss)     exit 137 ;;
    lowmem)  exit 137 ;;
    timeout) exit 124 ;;
    *)       exit $STATUS ;;
esac
