# Sourced by the conformance scripts: the PINNED tools, built from the
# submodules by scripts/bootstrap_tools.sh.
#   Miri   — conformance/vendor/miri, installed as the rustup toolchain
#            `miri` (./miri toolchain && ./miri install)
#   Charon — conformance/vendor/charon, built into .tools/charon/
# Both can be overridden (MIRI_TOOLCHAIN, CHARON) for experiments; the
# live suite (scripts/live.py) refuses a Miri whose commit is not the
# submodule's.
TOOLCHAIN="${MIRI_TOOLCHAIN:-miri}"
# Miri's own sysroot, built by bootstrap_tools.sh (not ~/.cache/miri, which
# any other Miri on the machine overwrites with its own rustc's std).
CHARON="${CHARON:-$HERE/.tools/charon/charon}"
# Charon's own std-with-MIR sysroot (bootstrap_tools.sh). Without it the
# driver runs `cargo miri setup` per call, into MIRI_SYSROOT/~/.cache/miri.
export CHARON_MIRI_SYSROOTS="${CHARON_MIRI_SYSROOTS:-$HERE/.tools/charon-sysroot}"

# Extra Miri flags a test file asks for: `// miri-flags: …` (preps, local
# witnesses) and the -Zmiri-* part of upstream `//@compile-flags: …`
# (corpus files run unprepped).
miri_file_flags() {
  { grep -h '^// miri-flags:' "$1" | sed 's|^// miri-flags:||'
    grep -h '^//@compile-flags:' "$1" | sed 's|^//@compile-flags:||' \
      | tr ' ' '\n' | grep '^-Zmiri-'
  } | tr '\n' ' ' || true
}

# The toolchain string certificates record, e.g. `miri 0.1.0 (34d6a79544 2026-08-13)`.
miri_version() { cargo "+$TOOLCHAIN" miri --version; }

# Run the pinned Miri driver directly on one file (no cargo crate per
# test: cargo-miri re-checks the shared sysroot on every call, and
# parallel calls race on it). The flags are exactly what `cargo miri run`
# passes for a one-file bin crate in the dev profile (opt-level 0, so
# debug assertions and overflow checks are on by rustc's own default).
#   run_miri FILE [extra miri flags...]    (stdout/stderr: the program's)
run_miri() {
  local f="$1"; shift
  : "${MIRI_SYSROOT:=$HERE/.tools/miri-sysroot}"
  : "${MIRI_BIN:=$(rustup which --toolchain "$TOOLCHAIN" miri)}"
  export MIRI_SYSROOT MIRI_BIN
  # shellcheck disable=SC2046
  "$MIRI_BIN" --sysroot "$MIRI_SYSROOT" --edition=2021 --crate-type bin \
    -C debuginfo=2 "$f" $(miri_file_flags "$f") "$@"
}
