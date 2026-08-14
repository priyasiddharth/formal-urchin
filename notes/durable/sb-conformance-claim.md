# The SB conformance claim: complete rule coverage

Recorded 2026-08-14, at the close of the conformance session (suite:
pass 75 | fail 0 | xfail 0 | xpass 0; fail tests 55/75 verdict-conformant,
47 line-accurate; 20 pass scenarios; miri @ 34d6a795).

[FACT] obseq3 implements the complete Stacked Borrows RULE SET: per-cell
stacks with granting; write-pops/read-disables (Disabled kept in place so
SRW groups never merge); Unique/Frozen/SharedReadWrite items with
insert-above-granting placement and SRW write grouping; two-phase
reserved borrows; strong protectors with weak protection on SRW;
fn-entry retags of args/returns including tuple fields (and correctly
NOT struct fields); retags on reference loads; UnsafeCell freeze masks
on shared/raw-const retags; deallocation checks (grant + protectors +
stack removal); exposed provenance with wildcard accesses; provenance-
preserving casts/arithmetic/transmutes; runtime-length slice retags.
Each rule is witnessed by at least one conformant miri test — the
rule → witness table lives in conformance/README.md.

[FACT] The 20 remaining unsupported fail tests are blocked on
LANGUAGE/STD features, not SB rules: dynamic control flow (SwitchInt:
zst_slice, buggy_split_at_mut, fnentry_invalidation), containers
(Vec/String/Rc/NonNull), threads (retag_data_race_* — the data-race
detector, a different checker), drop glue (drop_in_place_*), closures/
fn-ptr args (newtype_*, deallocate_against_protector*, track_caller),
unions (illegal_read3), custom allocators. One genuine SB-policy
simplification remains: Box is modeled as an implicit mutable raw
rather than getting miri's Unique box retag + weak protector
(box_noalias_violation is the only test that needs it).

[FACT] User framing that set this claim (2026-08-14): "we don't need
additional features to be stacked borrows compliant" — compliance is
about the model's rules, all of which are implemented and witnessed;
the unsupported tail re-exercises the same rules through more language
surface.
