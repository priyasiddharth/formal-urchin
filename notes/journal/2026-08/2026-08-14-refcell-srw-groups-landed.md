# RefCell shims + SRW grouping + Disabled state — 50/75, zero divergences

[OBS 2026-08-14] Sixth increment: flag-elided RefCell shims. Suite:
pass 69 | fail 0 | xfail 0 | xpass 0 | unsupported 47 (116 entries);
fail tests 50/75 (42 line-accurate), 19 pass scenarios. New:
shared_rw_borrows_are_weak2 (miri's line) + six interior_mutability
scenarios (aliasing_mut_and_shr, aliasing_frz_and_shr, refcell_basic,
ref_protector, ref_mut_protector, box_derefer).

[FACT] RefCell's borrow-flag discipline is orthogonal to SB, so the
shims elide it: RefCell<T> maps to the value region (cell T);
borrow/borrow_mut are masked-shared/unique reborrows; Ref/RefMut guards
are RAW-layout values — deliberately, because miri does NOT protect or
retag struct-wrapped references at fn boundaries (ref_protector /
ref_mut_protector pass tests state this outright: "adding a protector
for Ref would break this"); guard deref/deref_mut are typed loads whose
load-retag produces the fresh reborrow; replace = masked reborrow +
read + write; mem::drop (bodyless) is a no-op. Valid only for
conflict-free executions — which is all the corpus exercises.

[FACT] The RefCell tests forced the last two core-model fidelity fixes,
closing the documented SRW divergence:
1. **SRW grouping** (sb.lean writeCell): a write through a
   SharedReadWrite item pops only items above its contiguous SRW run —
   ref_mut_protector needs the &rc autoref sibling to survive
   borrow_mut's write access.
2. **Disabled state** (new Item.Disabled): reads DISABLE Uniques in
   place instead of removing them; a Disabled item grants nothing but
   keeps its position, so SRW groups on either side never merge.
   Implementing grouping WITHOUT Disabled broke
   disable_mut_does_not_merge_srw and interior_mut2 (missed UB, caught
   loudly by the harness) — the miri test's own comment describes
   exactly this: disabling-not-removing exists to prevent group merges.

[OBS 2026-08-14] Charon detail: global_decls can contain literal null
entries (stripped decls) — the parser now filters them; RefCell shares
the ["core","cell","new"] constructor path with Cell/UnsafeCell so the
existing prescan covers it; guard pointees are inferred from
deref/deref_mut call sites with a one-word fallback.
