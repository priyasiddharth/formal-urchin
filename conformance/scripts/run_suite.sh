#!/usr/bin/env bash
# Run the SB conformance suite (Lean harness) against the manifest.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
cd "$REPO"
lake build sb_conformance
lake exe sb_conformance --manifest "$HERE/manifest.json" --charon-dir "$HERE/charon" "$@"
