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
# Usage: source this file (not execute), from anywhere:
#   source lean/with_mathlib/bootstrap_ci.sh
# so the PATH export in the final step affects the calling shell.

set -euo pipefail

if command -v lake >/dev/null 2>&1; then
  echo "[bootstrap] lake already on PATH, nothing to do"
  return 0 2>/dev/null || exit 0
fi

TOOLCHAIN="$(cat "$(dirname "${BASH_SOURCE[0]}")/lean-toolchain")"   # e.g. leanprover/lean4:v4.30.0
VERSION="${TOOLCHAIN#*:}"                                            # e.g. v4.30.0

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

echo "[bootstrap] done: $(lean --version)"
