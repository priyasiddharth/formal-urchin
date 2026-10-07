#!/usr/bin/env bash
# Generate an execution CERTIFICATE for every prep/*.rs (or the files named
# as arguments): run the program under the pinned Miri fork with
# FORMAL_URCHIN_EVENTS set (the fork's observation-only event stream:
# frames, branches, the blocks entered, enum-argument variants), and turn
# the events into charon/<name>.cert.json (see scripts/miri_cert.py and
# src/conformance/certificate.lean). The ULLBC artifact must already exist
# (scripts/gen_charon.sh) — the extractor reads the user function names
# from it.
#
# A prep file may carry `// miri-flags: -Zmiri-...` (extra MIRIFLAGS).
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
. "$HERE/scripts/tools.sh"
CHARON_DIR="${CERT_CHARON_DIR:-$HERE/charon}"
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
  events="$(mktemp)"; stderr="$(mktemp)"
  flagargs=()
  for fl in $(miri_file_flags "$f"); do flagargs+=("--flag=$fl"); done
  set +e
  FORMAL_URCHIN_EVENTS="$events" run_miri "$f" -Zmir-opt-level=0 > /dev/null 2> "$stderr"
  status=$?
  set -e
  python3 "$HERE/scripts/miri_cert.py" --events "$events" --stderr "$stderr" --ullbc "$ullbc" \
    --source "$(realpath -s --relative-to="$HERE" "$f")" --out "$CHARON_DIR/$name.cert.json" \
    --exit-status "$status" --toolchain "$(miri_version)" ${flagargs[@]+"${flagargs[@]}"}
  rm -f "$events" "$stderr"
done
