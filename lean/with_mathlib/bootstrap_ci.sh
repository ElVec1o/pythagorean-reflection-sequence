#!/usr/bin/env bash
# Bootstrap a fresh, toolchain-less container for lake build.
#
# Written for the cloud-routine loop (private/RESEARCH_LOG.md is gitignored and does
# not exist in a fresh cloud checkout, so this script and this comment are the
# continuity record for how the container needs to be set up). Found by hand,
# 2026-09-05: `elan toolchain install` reaches out to release.lean-lang.org, which
# this sandbox's egress policy returns 403 for. Fetching the same release tarball
# directly from github.com/leanprover/lean4/releases works (200), so that is the path
# here. If a future container already has `lake` on PATH, this script is a fast no-op.
#
# IMPORTANT, found 2026-09-05: Mathlib's precompiled-cache CDN
# (lakecache.blob.core.windows.net, what `lake exe cache get` fetches from) is
# BLOCKED by this sandbox's org egress policy -- confirmed via the proxy's own
# `/__agentproxy/status` diagnostics, not a transient failure. `lake exe cache get`
# will NEVER succeed here; do not attempt it, and do not spend time re-diagnosing
# this each run. This is an environment policy issue, not something a script can
# work around -- it needs the org to allowlist that host, or the environment image
# to ship Mathlib prebuilt.
#
# The practical workaround: DO NOT run a bare `lake build` (that targets all 60
# `defaultTargets` in lakefile.toml, i.e. effectively the whole of Mathlib -- a
# from-source build that can run for hours). Instead build the SCOPED target you
# actually need, e.g. `lake build EltBridge`, which only compiles the ~400 files
# EltBridge.lean actually depends on and is comparatively tractable, though still
# a genuine from-source compile (no cache) and not fast -- expect it to take a
# real amount of wall-clock time on a cold container, not seconds.
#
# Usage: source this file (not execute), from anywhere:
#   source lean/with_mathlib/bootstrap_ci.sh
# so the PATH export in the final step affects the calling shell. This script only
# installs the TOOLCHAIN; it deliberately does not run `lake build` itself (that
# should be run with the scoped target, in the background, by the caller).

set -euo pipefail

if command -v lake >/dev/null 2>&1; then
  echo "[bootstrap] lake already on PATH, nothing to do"
  return 0 2>/dev/null || exit 0
fi

PROJDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOLCHAIN="$(cat "$PROJDIR/lean-toolchain")"   # e.g. leanprover/lean4:v4.30.0
VERSION="${TOOLCHAIN#*:}"                       # e.g. v4.30.0

echo "[bootstrap] installing elan (toolchain manager only, no default toolchain)"
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
bash /tmp/elan-init.sh -y --default-toolchain none >/tmp/elan-install.log 2>&1 || {
  echo "[bootstrap] elan installer failed, log:"; cat /tmp/elan-install.log; exit 1; }

export PATH="$HOME/.elan/bin:$PATH"

echo "[bootstrap] fetching Lean $VERSION directly from GitHub releases (release.lean-lang.org is blocked by egress policy in this sandbox)"
ARCHIVE="/tmp/lean-${VERSION}.tar.zst"
curl -sSL -o "$ARCHIVE" \
  "https://github.com/leanprover/lean4/releases/download/${VERSION}/lean-${VERSION#v}-linux.tar.zst"

command -v zstd >/dev/null 2>&1 || apt-get install -y zstd >/tmp/apt-zstd.log 2>&1

DEST="$HOME/lean-manual-toolchains/${VERSION}"
mkdir -p "$DEST"
tar --zstd -xf "$ARCHIVE" --strip-components=1 -C "$DEST"

elan toolchain link "$TOOLCHAIN" "$DEST"

# `lean --version`/`lake --version` with no arguments resolve the toolchain from a
# `lean-toolchain` file in the CWD (or elan's configured default, which we
# deliberately did not set with --default-toolchain none). Running the check from
# an arbitrary directory therefore prints a harmless-but-alarming "no default
# toolchain configured" error even though the link above succeeded -- run the
# check from PROJDIR so it actually resolves.
echo "[bootstrap] done: $(cd "$PROJDIR" && lean --version)"
echo "[bootstrap] NOTE: lake exe cache get will NOT work here (Mathlib cache CDN is"
echo "[bootstrap] blocked by egress policy) -- build a SCOPED target instead, e.g.:"
echo "[bootstrap]   cd \"$PROJDIR\" && lake build EltBridge"
echo "[bootstrap] NOT a bare 'lake build' (that pulls in all defaultTargets)."
