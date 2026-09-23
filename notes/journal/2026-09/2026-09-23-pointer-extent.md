# Pointers carry an extent; the slice retag is exact

[FACT 2026-09-23, verified against 25cb78e+] See
durable/pointer-values-carry-an-extent.md. The user's question ("why is
`&s[2..5]`'s retag coarser than Miri's?") had the answer "the value has
no length field", and the user's decision was to add one rather than
narrow `size` (which would conflate provenance with metadata: dealloc,
`ptrOffset`'s low-end guard, `fromExposed`). Field order per the user:
base, offset, extent, size, tag.

[OBS 2026-09-23] The migration touched every pointer literal in the
proof (~200 sites, 11 files) and built with five rounds of fixes, all
mechanical. The one design choice that kept it mechanical:
`PtrRegisterEntry` existential in the extent. Chains produce register
entries whose extent is not static (a `deref` level's register holds a
loaded pointer), so an explicit extent parameter would have forced
`∃ e` into `ptrChain_lowering_sim`'s conclusion and every consumer; the
existential inside the definition hides it, and `obtain ⟨e, h_lookup⟩
:= h_entry` at each step lemma is the only visible cost.

[OBS 2026-09-23] Lean idioms: `subst h` with `h : a = b`, both local
variables, eliminates `b` — so after `obtain ⟨…, h_e, …⟩; subst h_e`
with `h_e : e2 = e` the surviving name is `e2`. `refine ⟨_, ?_⟩` for an
existential the tail closes by `rw … rfl` does NOT get its witness
assigned ("don't know how to synthesize placeholder"); name it.

[FACT 2026-09-23] Suites unchanged: units 17/17 + 116/116, corpus
93/0/43, differential 93 matched; audit 3 axioms / 0 sorries. Expected:
every slice in the corpus is a whole allocation, for which extent =
size − offset.
