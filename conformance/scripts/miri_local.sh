#!/usr/bin/env bash
# Run the LOCAL witnesses (conformance/local/*.rs, or the files named as
# arguments) under the pinned Miri and print the verdict each one gets:
#
#   <name>: ok
#   <name>: ub line=<n> :: <miri's first error line>
#   <name>: panic
#
# These programs are not from the Miri corpus, so this is how their
# manifest `expected` blocks are checked against real Miri instead of
# against model reasoning. Stacked Borrows is Miri's default; a file may
# carry `// miri-flags: -Zmiri-...` for extra flags, as preps do.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TOOLCHAIN="${MIRI_TOOLCHAIN:-nightly-2026-06-01}"
BUILD="${MIRI_LOCAL_BUILD:-$HERE/.miribuild}"
if ! cargo "+$TOOLCHAIN" miri --version >/dev/null 2>&1; then
  echo "miri_local: cargo +$TOOLCHAIN miri is not available" >&2
  exit 2
fi
shopt -s nullglob
files=("$@")
[ ${#files[@]} -eq 0 ] && files=("$HERE"/local/*.rs)
for f in "${files[@]}"; do
  name="$(basename "$f" .rs)"
  crate="$BUILD/$name"
  mkdir -p "$crate/src"
  cat > "$crate/Cargo.toml" <<TOML
[package]
name = "miriprobe"
version = "0.1.0"
edition = "2021"
[dependencies]
TOML
  cp "$f" "$crate/src/main.rs"
  extra="$(grep -h '^// miri-flags:' "$f" | sed 's|^// miri-flags:||' | tr '\n' ' ' || true)"
  set +e
  ( cd "$crate" && MIRIFLAGS="$extra" cargo "+$TOOLCHAIN" miri run -q \
      > "$crate/stdout.txt" 2> "$crate/stderr.txt" )
  status=$?
  set -e
  err="$crate/stderr.txt"
  if grep -q "^error: Undefined Behavior" "$err"; then
    line="$(grep -m1 -- '--> src/main.rs:' "$err" | sed 's|.*src/main.rs:\([0-9]*\):.*|\1|')"
    msg="$(grep -m1 "^error: Undefined Behavior" "$err" | cut -c1-140)"
    echo "$name: ub line=$line :: $msg"
  elif grep -qE "panicked at|^error: abnormal termination" "$err"; then
    echo "$name: panic :: $(grep -m1 -E 'panicked at' "$err" | cut -c1-120)"
  elif [ $status -eq 0 ]; then
    echo "$name: ok"
  else
    echo "$name: FAILED (miri exited $status)"
    sed -n 1,20p "$err" >&2
  fi
done
