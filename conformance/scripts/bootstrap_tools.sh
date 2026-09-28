#!/usr/bin/env bash
# Build the PINNED Miri and Charon from the submodules under
# conformance/vendor/ (the pins ARE the submodule commits; see PIN).
# Idempotent: each tool is rebuilt only when its stamp does not name the
# current submodule commit, so a CI cache restore makes this a no-op.
#
#   Charon  vendor/charon, cargo build --release on the toolchain its
#           rust-toolchain file names; the two binaries are copied to
#           .tools/charon/ with a stamp; its MIR-carrying std in
#           .tools/charon-sysroot.
#   Miri    vendor/miri, `./miri toolchain` (the exact rustc its
#           rust-version names, via rustup-toolchain-install-master, as the
#           rustup toolchain `miri`) then `./miri install` (miri + cargo-miri
#           into that toolchain) and `cargo +miri miri setup` (the sysroot,
#           in .tools/miri-sysroot — NOT the default ~/.cache/miri, which
#           every Miri on the machine shares and rebuilds for itself).
#
# Needs rustup, git, a C toolchain, network on first run.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
export MIRI_AUTO_OPS=no   # ./miri: no automatic toolchain/fmt/clippy runs

git -C "$REPO" submodule update --init conformance/vendor/miri conformance/vendor/charon
charon_rev="$(git -C "$HERE/vendor/charon" rev-parse HEAD)"
miri_rev="$(git -C "$HERE/vendor/miri" rev-parse HEAD)"

# --- Charon --------------------------------------------------------------
dest="$HERE/.tools/charon"
if [ "$(cat "$dest/STAMP" 2>/dev/null)" != "$charon_rev" ]; then
  echo "bootstrap: building Charon $charon_rev"
  ( cd "$HERE/vendor/charon" && rustup toolchain install )
  ( cd "$HERE/vendor/charon/charon" && cargo build --release --bin charon --bin charon-driver )
  mkdir -p "$dest"
  cp "$HERE/vendor/charon/charon/target/release/charon" \
     "$HERE/vendor/charon/charon/target/release/charon-driver" "$dest/"
  echo "$charon_rev" > "$dest/STAMP"
else
  echo "bootstrap: Charon $charon_rev (cached)"
  ( cd "$HERE/vendor/charon" && rustup toolchain install >/dev/null )
fi
"$dest/charon" version >/dev/null
# Charon's driver wants a std with MIR (`cargo miri setup` on ITS toolchain).
# Left alone it runs that setup on every call — honouring MIRI_SYSROOT and
# otherwise writing ~/.cache/miri, the pinned Miri's sysroot — so build it
# once, here, into its own directory (tools.sh points CHARON_MIRI_SYSROOTS
# at it).
charon_tc="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$HERE/vendor/charon/rust-toolchain")"
( cd "$HERE" && env -u MIRI_SYSROOT MIRI_SYSROOT="$HERE/.tools/charon-sysroot" \
    cargo "+$charon_tc" miri setup >/dev/null )

# --- Miri ----------------------------------------------------------------
short="${miri_rev:0:10}"
if ! cargo +miri miri --version 2>/dev/null | grep -q "($short "; then
  echo "bootstrap: building Miri $miri_rev"
  command -v rustup-toolchain-install-master >/dev/null ||
    cargo install rustup-toolchain-install-master
  ( cd "$HERE/vendor/miri" && ./miri toolchain && ./miri install )
else
  echo "bootstrap: Miri $miri_rev (cached)"
fi
# Smoke test through the same path the suite uses; a sysroot built by
# another rustc fails with E0514, and is rebuilt once.
. "$HERE/scripts/tools.sh"
smoke="$(mktemp -d)/smoke.rs"; echo 'fn main() {}' > "$smoke"
for attempt in 1 2; do
  MIRI_SYSROOT="$HERE/.tools/miri-sysroot" cargo +miri miri setup >/dev/null
  if run_miri "$smoke" >/dev/null 2>&1; then break; fi
  [ $attempt = 2 ] && { run_miri "$smoke"; exit 1; }
  echo "bootstrap: Miri sysroot does not match the pinned rustc; rebuilding" >&2
  rm -rf "$HERE/.tools/miri-sysroot"
done
cargo +miri miri --version
