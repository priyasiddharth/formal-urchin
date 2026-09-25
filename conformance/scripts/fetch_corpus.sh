#!/usr/bin/env bash
# Re-export the pinned Miri test corpus into conformance/corpus/.
# The pin lives in conformance/PIN (miri_commit line).
#
# The corpus comes from a Miri checkout. Set MIRI_REPO to point at one;
# otherwise the first existing candidate below is used, and if none
# exists a blobless mirror is cloned into $MIRI_CLONE_DIR (default
# ~/src/miri) — the tests are ~10MB, the blobless clone a few tens.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
COMMIT="$(grep '^miri_commit:' "$HERE/PIN" | awk '{print $2}')"
CLONE_DIR="${MIRI_CLONE_DIR:-$HOME/src/miri}"
MIRI_REMOTE="https://github.com/rust-lang/miri.git"

if [ -z "${MIRI_REPO:-}" ]; then
  for cand in "$CLONE_DIR" "$HOME/src/miri" "$HOME/rustc/rust/src/tools/miri"; do
    if [ -d "$cand/.git" ]; then MIRI_REPO="$cand"; break; fi
  done
fi
if [ -z "${MIRI_REPO:-}" ]; then
  echo "fetch_corpus: no Miri checkout found; cloning $MIRI_REMOTE into $CLONE_DIR" >&2
  mkdir -p "$(dirname "$CLONE_DIR")"
  git clone --filter=blob:none --no-checkout "$MIRI_REMOTE" "$CLONE_DIR"
  MIRI_REPO="$CLONE_DIR"
fi

git -C "$MIRI_REPO" cat-file -e "$COMMIT" 2>/dev/null || git -C "$MIRI_REPO" fetch origin master
mkdir -p "$HERE/corpus"
git -C "$MIRI_REPO" archive "$COMMIT" tests | tar -x -C "$HERE/corpus"
echo "corpus exported at $COMMIT (from $MIRI_REPO)"
