#!/usr/bin/env bash
# Regenerate ULLBC JSON artifacts for every prep/*.rs (or the ones named
# as arguments) into $CHARON_OUT (default charon/). Uses the pinned Charon
# (scripts/tools.sh). Run from conformance/ with RELATIVE paths: Charon
# records the source path as given.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
. "$HERE/scripts/tools.sh"
OUT="${CHARON_OUT:-$HERE/charon}"
shopt -s nullglob
files=("$@")
[ ${#files[@]} -eq 0 ] && { cd "$HERE"; files=(prep/*.rs); }
for f in "${files[@]}"; do
  name="$(basename "$f" .rs)"
  echo "charon: $name"
  env -u MIRI_SYSROOT "$CHARON" rustc --ullbc --mir built --monomorphize \
    --dest-file "$OUT/$name.ullbc.json" \
    -- --edition 2021 "$f"
done
