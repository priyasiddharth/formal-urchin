#!/usr/bin/env bash
# Re-export the pinned Miri test corpus into conformance/corpus/.
# The pin lives in conformance/PIN (miri_commit line).
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
MIRI_REPO="${MIRI_REPO:-/home/siddharth/rustc/rust/src/tools/miri}"
COMMIT="$(grep '^miri_commit:' "$HERE/PIN" | awk '{print $2}')"
git -C "$MIRI_REPO" cat-file -e "$COMMIT" 2>/dev/null || git -C "$MIRI_REPO" fetch origin master
mkdir -p "$HERE/corpus"
git -C "$MIRI_REPO" archive "$COMMIT" tests | tar -x -C "$HERE/corpus"
echo "corpus exported at $COMMIT"
