#!/usr/bin/env bash
# Regenerate ULLBC JSON artifacts for every prep/*.rs (or the ones named
# as arguments). Charon binary resolved from $CHARON or PATH.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
CHARON="${CHARON:-charon}"
shopt -s nullglob
files=("$@")
[ ${#files[@]} -eq 0 ] && files=("$HERE"/prep/*.rs)
for f in "${files[@]}"; do
  name="$(basename "$f" .rs)"
  echo "charon: $name"
  "$CHARON" rustc --ullbc --mir built --monomorphize \
    --dest-file "$HERE/charon/$name.ullbc.json" \
    -- --edition 2021 "$f"
done
