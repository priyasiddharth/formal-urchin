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
. "$HERE/scripts/tools.sh"
shopt -s nullglob
files=("$@")
[ ${#files[@]} -eq 0 ] && files=("$HERE"/local/*.rs)
for f in "${files[@]}"; do
  name="$(basename "$f" .rs)"
  err="$(mktemp)"
  set +e
  run_miri "$f" > /dev/null 2> "$err"
  status=$?
  set -e
  if grep -q "^error: Undefined Behavior" "$err"; then
    # the first span AFTER the UB line (warnings print spans before it);
    # empty when the UB is in another file (std), as upstream's
    # `error-in-other-file` tests expect
    line="$(sed -n '/^error: Undefined Behavior/,$p' "$err" \
      | grep -m1 -- "--> .*$(basename "$f"):" | sed 's|.*\.rs:\([0-9]*\):.*|\1|' || true)"
    msg="$(grep -m1 "^error: Undefined Behavior" "$err" | cut -c1-140)"
    # MIRI_REPORT_OUT: keep Miri's own account of the UB — the error line
    # and the "this error occurs as part of <op> at <alloc>[<range>]" label
    # — for the harness's reason check (one file per run)
    if [ -n "${MIRI_REPORT_OUT:-}" ]; then
      { grep -m1 "^error: Undefined Behavior" "$err"
        part="$(grep -m1 -o "this error occurs as part of .*" "$err" || true)"
        [ -n "$part" ] && echo "$part"
      } > "$MIRI_REPORT_OUT"
    fi
    echo "$name: ub line=$line :: $msg"
  elif grep -qE "panicked at|^error: abnormal termination" "$err"; then
    echo "$name: panic :: $(grep -m1 -E 'panicked at' "$err" | cut -c1-120)"
  elif [ $status -eq 0 ]; then
    echo "$name: ok"
  else
    echo "$name: FAILED (miri exited $status)"
    sed -n 1,20p "$err" >&2
  fi
  rm -f "$err"
done
