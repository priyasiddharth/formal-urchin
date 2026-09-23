#!/usr/bin/env bash
# Generate an execution CERTIFICATE for every prep/*.rs (or the files named
# as arguments): run the program under Miri on the pinned toolchain with
# MIRI_LOG tracing, and turn the block/terminator trace into
# charon/<name>.cert.json (see scripts/miri_cert.py and
# src/conformance/certificate.lean). The ULLBC artifact must already exist
# (scripts/gen_charon.sh) — the extractor reads the user function names
# from it.
#
# A prep file may carry `// miri-flags: -Zmiri-...` (extra MIRIFLAGS).
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TOOLCHAIN="${MIRI_TOOLCHAIN:-nightly-2026-06-01}"
CHARON_DIR="${CERT_CHARON_DIR:-$HERE/charon}"
BUILD="$HERE/.certbuild"
if ! cargo "+$TOOLCHAIN" miri --version >/dev/null 2>&1; then
  echo "gen_cert: cargo +$TOOLCHAIN miri is not available" >&2
  exit 2
fi
shopt -s nullglob
files=("$@")
[ ${#files[@]} -eq 0 ] && files=("$HERE"/prep/*.rs)
for f in "${files[@]}"; do
  name="$(basename "$f" .rs)"
  ullbc="$CHARON_DIR/$name.ullbc.json"
  if [ ! -f "$ullbc" ]; then
    echo "gen_cert: $name: missing $ullbc (run gen_charon.sh first)" >&2
    exit 2
  fi
  echo "cert: $name"
  crate="$BUILD/$name"
  mkdir -p "$crate/src"
  cat > "$crate/Cargo.toml" <<TOML
[package]
name = "certprobe"
version = "0.1.0"
edition = "2021"
[dependencies]
TOML
  cp "$f" "$crate/src/main.rs"
  extra="$(grep -h '^// miri-flags:' "$f" | sed 's|^// miri-flags:||' | tr '\n' ' ' || true)"
  flagargs=()
  for fl in $extra; do flagargs+=(--flag "$fl"); done
  set +e
  ( cd "$crate" && \
    MIRIFLAGS="-Zmir-opt-level=0 $extra" \
    MIRI_LOG="rustc_const_eval::interpret::step=info,rustc_const_eval::interpret::stack=info,rustc_const_eval::interpret::call=info" \
    cargo "+$TOOLCHAIN" miri run -q > "$crate/stdout.txt" 2> "$crate/miri.log" )
  status=$?
  set -e
  python3 "$HERE/scripts/miri_cert.py" --log "$crate/miri.log" --ullbc "$ullbc" \
    --source "prep/$name.rs" --out "$CHARON_DIR/$name.cert.json" \
    --exit-status "$status" --toolchain "$TOOLCHAIN" "${flagargs[@]}"
done
