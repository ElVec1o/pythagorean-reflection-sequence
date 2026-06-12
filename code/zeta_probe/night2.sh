#!/bin/bash
# Night run 2: (a) mirror-shape shortest vector; (b) census saturation probe.
# Usage: nohup caffeinate -i bash night2.sh > /dev/null 2>&1 &
# Morning: cat NIGHT2_RESULT.txt
cd "$(dirname "$0")"
R="$PWD/NIGHT2_RESULT.txt"; : > "$R"
log(){ echo "[$(date '+%H:%M:%S')] $*" >> "$R"; }
log "=== NIGHT2 START ==="
( cd certify38_rust && cargo build --release >> build.log 2>&1 )
( cd fire_rust && cargo build --release >> build.log 2>&1 )
log "--- mirror shape (1,2), e=-6: expect L=66 via f=1-t ---"
( cd certify38_rust && ./target/release/certify38 ldist 34 5 -6 2>/dev/null ) >> "$R"
log "--- census saturation: budgets 18, 20 (each slower than the last) ---"
( cd fire_rust && for D in 18 20; do ./target/release/fire deep $D 6 census1 2>/dev/null >> "$R"; done )
log "=== NIGHT2 COMPLETE — paste this file ==="
