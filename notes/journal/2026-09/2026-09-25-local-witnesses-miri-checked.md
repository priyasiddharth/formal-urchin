# The local witnesses are Miri-checked, not model-reasoned

2026-09-25. "Can you do the miri check instead of local" — i.e. stop
resting the project-authored witnesses on model reasoning. Done, and the
parked entry from 2026-08-21 ("Verify local conformance witnesses
against real Miri", estimated ~1h) is closed.

[FACT] Every one of the 13 `conformance/local/*.rs` now runs under the
pinned Miri and agrees with its manifest `expected` block:

    assign_move_keeps_borrows      ok
    deref_read_disables_sibling    ub line=13
    move_arg_field_spares_sibling  ok
    move_arg_ok                    ok
    move_arg_via_temp_spares_raw   ok
    nested_proj_borrow             ok
    slice_len_alias                ok
    slice_len_value                ok
    split_field_borrows            ok
    unassigned_local_addr          ok
    zst_interior_field             ok
    zst_ref                        ok
    zst_tail_field                 ok

The UB one is the interesting agreement: Miri reports it at line 13
("attempting a read access … tag does not exist in the borrow stack")
and names the `*p = 5` one line earlier as the invalidation — the exact
mechanism the witness was written for in August, when the model was
changed to make deref resolution a real SB read.

[FACT] The 2026-08-21 parking note was wrong about WHY this was blocked.
It assumed Miri had to be built at the PIN's miri_commit. The pinned
TOOLCHAIN already carries the `miri` component (conformance/tools/
rust-toolchain lists it) and `cargo +nightly-2026-06-01 miri` works. What
this machine actually lacks is the corpus SOURCES (the Miri checkout
`fetch_corpus.sh` exports from), which is a different problem and only
blocks UNSUPPORTED corpus entries — see
[[2026-09-24-slice-length]]. Worth the general lesson: a parked
"blocked on tooling" note should name the exact missing artifact, since
the wrong one was assumed for five weeks.

[FACT] The run is repeatable, not a one-off: `conformance/scripts/
miri_local.sh` builds a throwaway crate per witness under
`conformance/.miribuild/`, runs it with any `// miri-flags:` the file
carries (the same convention preps use), and prints
`<name>: ok | ub line=<n> | panic`. Re-run it when a witness is added or
the pin moves.

[OBS] Two witnesses gained real provenance rather than a corrected one:
`slice_len_alias` (yesterday's manifest claimed Miri verification that
had not actually been performed — it has now, verdict ok) and
`slice_len_value` (its certificate came from Miri, so Miri had run it,
but the verdict itself was never recorded).
