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
# vendor/miri is the formal-urchin FORK (branch formal-urchin): upstream Miri
# at PIN's miri_commit, plus ONE observation-only patch (the certificate
# event stream) in src/machine.rs and src/concurrency/scheduler.rs
# (miri_tool_commit, from which the TOOL is built), plus our tests under
# tests/formal-urchin/. Test edits never rebuild Miri (or miss the CI cache);
# the tool may differ from upstream only in those two files.
miri_up="$(sed -n 's/^miri_commit: *//p' "$HERE/PIN")"
miri_rev="$(sed -n 's/^miri_tool_commit: *//p' "$HERE/PIN")"
for c in "$miri_up" "$miri_rev"; do
  git -C "$HERE/vendor/miri" cat-file -e "$c^{commit}" 2>/dev/null ||
    git -C "$HERE/vendor/miri" fetch -q --depth=1 origin "$c"
done
patch="$(git -C "$HERE/vendor/miri" diff --name-only "$miri_up" "$miri_rev" -- . ':!tests/formal-urchin')"
if [ "$patch" != "$(printf 'src/concurrency/scheduler.rs\nsrc/machine.rs')" ]; then
  echo "bootstrap: the Miri tool commit $miri_rev differs from upstream $miri_up in:" >&2
  echo "$patch" >&2
  exit 1
fi
outside="$(git -C "$HERE/vendor/miri" diff --name-only "$miri_rev" HEAD -- . ':!tests/formal-urchin')"
if [ -n "$outside" ]; then
  echo "bootstrap: vendor/miri differs from the tool commit $miri_rev outside tests/formal-urchin:" >&2
  echo "$outside" >&2
  exit 1
fi

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
  src="$HERE/.tools/miri-src"   # a worktree of the fork at the pinned commit
  [ -d "$src" ] || git -C "$HERE/vendor/miri" worktree add -q --detach "$src" "$miri_rev"
  git -C "$src" checkout -q --detach "$miri_rev"
  ( cd "$src" && ./miri toolchain && ./miri install )
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
