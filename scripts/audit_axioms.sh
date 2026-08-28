#!/usr/bin/env bash
# Machine-checked axiom/sorry audit of the main correctness theorem.
# Fails (nonzero) on any axiom outside the whitelist or any drift in
# the audited sorry set. See scripts/axiom_audit.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Obseq3Proof >/dev/null
lake env lean scripts/axiom_audit.lean
