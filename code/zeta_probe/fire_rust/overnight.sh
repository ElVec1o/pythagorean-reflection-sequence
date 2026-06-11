#!/bin/bash
# Overnight pipeline: fire + deep, sequential, self-checking.
# Usage:  nohup caffeinate -i bash overnight.sh > /dev/null 2>&1 &
# Morning: cat OVERNIGHT_RESULT.txt
cd "$(dirname "$0")"
R="OVERNIGHT_RESULT.txt"
: > "$R"
log(){ echo "[$(date '+%H:%M:%S')] $*" >> "$R"; }

log "=== OVERNIGHT RUN START ==="
git pull >> "$R" 2>&1
cargo build --release >> build.log 2>&1 && log "build OK" || { log "BUILD FAILED — see build.log"; exit 1; }
BIN=./target/release/fire

# Stage 0: sanity gate
log "--- verify 14 (port gate) ---"
$BIN verify 14 2>/dev/null | tail -1 >> "$R"

# Stage 1: proven path, fresh terms
log "--- fire 22 (proven path, ~40 min) ---"
$BIN fire 22 2>/dev/null | tail -3 >> "$R"

# Stage 2+: the experiment, escalating depth, gated on MATCH
for D in 12 14 16 18; do
  log "--- deep $D (counting grammar) ---"
  $BIN deep $D > deep$D.log 2>&1
  grep -E "automaton complete|states \(4 variants" deep$D.log >> "$R"
  tail -4 deep$D.log >> "$R"
  if ! grep -q "^MATCH" deep$D.log; then
    log "deep $D did not MATCH — stopping escalation (logs kept in deep$D.log)"
    break
  fi
  grep -E "LINEAR RECURRENCE|no linear recurrence|NEW TERMS|u_[0-9]+ =" deep$D.log >> "$R"
done

log "=== OVERNIGHT RUN COMPLETE — paste this whole file into the chat ==="
