# The corpus was one clone away

2026-09-25. "Get the corpus sources." Done in one command, which is the
point of the entry.

[FACT] `conformance/scripts/fetch_corpus.sh` exports the pinned Miri
`tests/` from a Miri checkout. Yesterday its hard-coded default
(`/home/siddharth/rustc/rust/src/tools/miri`) did not exist, and I
recorded that as "the corpus cannot be obtained on this machine" —
scoping the slice work's validation down to local witnesses. Wrong: the
remote is public, this machine has network, and a blobless clone of
rust-lang/miri carries the pinned commit
(34d6a7954425f3d97d6a7ff19bdf0f7a51560754, 2026-08-13). Corpus exported:
9.6 MB, and all 125 manifest `source` paths resolve.

[SUPERSEDED → this note] journal/2026-09/2026-09-24-slice-length.md's
[OBS], durable/pointer-values-carry-an-extent.md's [OPEN] and the
"Range sub-slicing" parked entry each carried the claim. **Why I was
misled:** the script failed with `fatal: cannot change to '<path>'`, and
I read a missing DEFAULT as a missing CAPABILITY. The same mistake sat
in the 2026-08-21 parked item about Miri itself ("needs a Miri build at
the PIN commit" — the toolchain already had the component). Two for two:
when a tooling script fails on a path, check what the path is for before
concluding the environment lacks the tool.

`fetch_corpus.sh` now searches `$MIRI_REPO`, then `~/src/miri`, then the
old rustc path, and clones the blobless mirror itself if none exists.
The checkout location is recorded in `conformance/PIN`.

[FACT] Artifacts are REPRODUCIBLE, verified rather than assumed:
regenerating `illegal_read1.ullbc.json` from the fetched corpus with the
pinned charon gives a byte-identical file — but only when
`scripts/gen_charon.sh` runs with cwd = `conformance/`. Charon records
the source path relative to the cwd (`"Local": "prep/illegal_read1.rs"`)
and its own `dest_file` absolutely, so running it from the repo root
produces content-equal JSON that differs in those two fields plus
`short_names` map ORDER. Content equality (`type_decls`, `fun_decls`,
`global_decls`, …) holds either way. README now says where to run it.

[OPEN] What this unblocks: the three slice tests (zst_slice,
buggy_split_at_mut, buggy_as_mut_slice) can now be prepped, charon'd and
certified like any other entry — the sub-slicing parked entry is the
work, and it is now *more* attractive than when it was parked, because
its validation target exists again.
