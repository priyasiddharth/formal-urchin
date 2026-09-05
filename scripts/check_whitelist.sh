#!/usr/bin/env bash
# Pin the CONTENTS of scripts/axiom_whitelist.txt.
#
# audit_axioms.sh checks the proof state AGAINST the whitelist; this script
# checks the whitelist itself, so a red audit cannot be made green by editing
# the pin: the [axioms] block must be exactly Lean's three, and the [sorries]
# block must be empty (obseq3 has been sorry-free since 2026-08-31).
set -euo pipefail
cd "$(dirname "$0")/.."
f=scripts/axiom_whitelist.txt

section() {  # entries of one section, comments and blanks stripped, sorted
  awk -v s="[$1]" '
    /^\[/ { on = ($0 == s); next }
    on && !/^#/ && NF { print $1 }' "$f" | sort
}

axioms=$(section axioms)
sorries=$(section sorries)
expected=$(printf 'Classical.choice\nQuot.sound\npropext\n')

if [ "$axioms" != "$expected" ]; then
  echo "axiom whitelist drift — [axioms] must be exactly propext, Classical.choice, Quot.sound; found:" >&2
  printf '  %s\n' $axioms >&2
  exit 1
fi
if [ -n "$sorries" ]; then
  echo "sorry whitelist not empty — obseq3 is sorry-free; found:" >&2
  printf '  %s\n' $sorries >&2
  exit 1
fi
echo "whitelist pinned: axioms = {propext, Classical.choice, Quot.sound}, sorries = {}"
