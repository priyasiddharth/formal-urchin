# obseq2 Development Log

Entries are newest-first. Each entry records a design discussion or decision made during obseq2 development.

---

## 2026-08-28 (night, latest) — Overlapping Copies Become UB, and the Last Countermodel Retires

Forty-third increment. Overlapping place-to-place assignment is now UB on both
machines: mirlite's `doAssign` guards the `.copy` branch (resolved src range
vs resolved dst range, checked with the access-free resolver so no SB event
is duplicated), and oseair's `Memcpy` gained the matching nonoverlapping
check — it models LLVM memcpy, so refusing overlap is what the instruction
always meant. This is the retag fix's sibling: source success at the guard
*supplies* the disjointness the target fragment needs, and the
`Borrow(Shared); Memcpy; Die` interleaving that made the nonzero-offset copy
leaf false now dissolves — the `Die` and the destination write act on
provably disjoint cells.

d33, the overlap countermodel, is retired: both machines now refuse the
forged state, and the test pins exactly that, with teeth verified by
transiently disabling each side's check. d35 pins the reachable case
differentially — `x := copy x` is UB at the same statement on both machines.
The Miri-pinned corpus is unchanged, confirming reachable behavior is
otherwise preserved.

The bookkeeping consequence is the pleasant one: after this and the
lowering-order fix, **no residual shape in copy, ref, or const_write has a
standing countermodel**. The separation invariant — a week ago the looming
next conjunct — is demoted to the parked list's cold storage, both its
consumers dissolved by cheaper, more faithful fixes at events the semantics
already owned. What remains everywhere is composition work, not blockers.

One engineering note: the first guard implementation, a `let overlapUB :
Bool` in the main flow, leaked an `if false` wrapper into every non-copy
proof; the right shape is a branch-local guard (`doAssignCont` split) so
non-copy rhs reduce to the exact old term. And one process scar, the same
one as last time: a `git checkout` during teeth-verification destroyed the
uncommitted semantics — reverts during teeth are now inverse edits, never
checkouts.

Units 16/16 + 48/48, suite pass 82 | fail 0 of 123, differential includes
d34 (agreement) and d35 (shared UB).

---

## 2026-08-28 (night, later) — The Compiler Learns MIR's Order

Forty-second increment: the lowering-order bug is fixed, hours after d34
pinned it. The rhs lowering is split into a source phase — every load,
borrow, and temporary the right-hand side needs — and a store phase that is
just a function of the eventual destination register. The assign-place arm
now runs them in MIR's order: rhs first, destination second, store third, so
no destination temporary is ever live while right-hand-side code executes.
d34's pin fired on the first post-fix run and the test is now a plain
agreement check, with reversion teeth: swap the two lines back and the
divergence returns on cue.

The proof fallout was almost indecently small. The rhs instruction streams
are unchanged by the split, and code-free right-hand sides (every constant
write) emit byte-identical assign-place fragments, so all closed regimes kept
their statements; the state-function monad's definitional monad laws kept
most `rfl` equations alive through the refactor, and the rest was a handful
of `simp` lists learning two new names. The one enduring lesson was
operational, not mathematical: bare `lake build` builds only the default
target, which does not include the proof library — two "full build, zero
errors" sweeps were vacuous before the axiom-audit wrapper, which builds the
proof lib explicitly, caught the real breakage. Validation now names its
targets.

With the interleaving obstacle gone, the non-local-destination residuals are
down to the separation/overlap analysis alone — the two parked decisions.

Units 16/16 + 47/47 (d34 now agreement), suite pass 82 | fail 0 of 123.

---

## 2026-08-28 (night) — The First Reachable Divergence: a Lowering-Order Bug

Forty-first increment, and the sharpest kind: d34 pins a divergence on a
REACHABLE state — a compiler bug, not an invariant gap. The assign-place
lowering mints its destination temporary `Borrow(Mut)` before the rhs runs,
but a rhs deref spine may legitimately read the very cell that temporary
guards: with `t : (u64, *mut u64)`, `p = &raw mut t`, `w = &raw mut t.1`,
the statement `(*p).1 := &mut **w` succeeds in mirlite (raw tags survive
foreign reads; no temporary exists) and errs in the compiled fragment (the
spine's load of `t.1`'s cell and the fresh Unique on it kill each other).
The differential harness confirmed the prediction on first run: source `.ok`,
target `.ub` at the statement.

No invariant strengthening or added UB can repair this — both machines'
behaviors are defined, and simulation owes the source its success. The fix
is the order MIR itself uses: evaluate the rhs into a temporary first, then
lower the destination and store. Parked as a model decision; landing it
flips d34 to a plain agreement test and dissolves the interleaving obstacle
across every non-local-destination residual at once.

The divergence taxonomy is now three-fold, with one exemplar each: junk
states fixed at a typed event (the retag bound, t16), junk states needing an
invariant (the overlap, d33), and reachable states needing a compiler change
(the lowering order, d34).

Units 16/16 + 47/47, suite pass 82 | fail 0 of 123.

---

## 2026-08-28 (late) — Zero-Offset Field Copies Close; a Countermodel Names the Next Invariant

Fortieth increment. `dst := copy src.f` at zero offset is regime L→L with a
wider source allocation — `placeToRegChecked` hands back the base register, so
the fragment is the same lone `Memcpy`, and the source-side bounds check is
paid by typing, precisely as C0 widened regime A. Closed in one sitting, with
d32 covering it differentially.

The nonzero-offset shape did not close, and the reason is worth the increment
on its own: it *cannot* close as stated. Its fragment is
`[Borrow(Shared); Memcpy; Die]`, and `Memcpy` is atomic — the destination
`useMut` executes between the keystone's read and its `Die`. In any reachable
state that's harmless, because the borrowed field and the destination local
are disjoint. But `CompilerInv` has no separation conjunct, and in a junk
state where two distinct locals overlap, a stack shaped `[.. tagD .. tagS]`
lets the source's read and write both succeed while the target's `useMut`
pops the fresh Shared out from under its `Die` — which demands its tag
exactly on top, and errs. Target UB, source fine: the leaf is false. (Same-
local aliasing is impossible — a `PathTo τ τ` would need a layout to contain
itself — so this is purely the invariant-gap pattern again, the retag story's
sibling. But where that gap closed at a typed *event*, this one is a property
of reachable *states*, so the fix must be a new invariant conjunct.)

The proposal, parked for a model decision: distinct bound locals occupy
disjoint blocks. It transports verbatim through every leaf that doesn't touch
the environment, costs real work only at allocation sites, and in exchange
die↔useMut commute by cell disjointness — unlocking nonzero-offset copies,
deref-src copy cleanup, and the interleaved-keystone residuals for non-local
destinations across ref and const_write. One conjunct, three residual classes.

Units 16/16 + 45/45, suite pass 82 | fail 0 of 123, differential 83/0/0.

---

## 2026-08-28 (evening) — Copy Closes Its First Regime, and Undef Learns Its Place

Thirty-ninth increment. `dst := copy src` for bound locals is one target
instruction — `Memcpy` — and its simulation is the cleanest leaf yet: the
instruction's read-then-useMut is *literally* the source's two events in the
same order at the same lengths, so BRIDGE 3's read and write members transport
them one-to-one, no tag is minted, no register is written, and both renames
grow by `refl`.

The interesting part is the blocker that dissolved. The audit had predicted a
"bidirectional memory relation": a target cell holding junk where the source
holds nothing would survive the copy and refute `SourceMemSim`, since the
source destination becomes an explicit `.undef` that the old `MemValSim`
related only to `Undef`. The tempting fix — a reverse-domain invariant
conjunct — would have taxed every closed write site in the development. The
right fix is a *weakening*: undef refines anything. Every source operation
that observes a word demands its constructor and errs on undef — branches,
alloc-length reads, pointer loads — so the cases where target junk could
diverge are exactly the cases where the source has no defined behaviour to
simulate. One row of `MemValSim` changed; the whole project rebuilt with zero
proof edits; and `readWordSeq_sim` — the pointwise relation between the two
machines' range reads — falls out of `SourceMemSim` alone, holes included.

With `runN_Memcpy_step` (whose Bool `||` bounds check is a new small idiom
next to the Prop `if`s elsewhere) and BRIDGE 2's existing cell-by-cell write
lemma, the leaf closed in one sitting. `CompilerInv_step_copy` is now a proved
dispatcher, `copy_place_residual` names the non-local shapes, and the audit
holds at four with the copy entry strictly narrower.

Units 16/16 + 44/44, suite pass 82 | fail 0 of 123, differential 82/0/0.

---

## 2026-08-28 (later) — The Event Fix Pays Off: Reborrow Through a Loaded Pointer

Thirty-eighth increment. `ref_deref_local_simulation` closes `dst := &kind *p`
for any load spine `p` — the regime that was *unprovable* one increment ago.
The proof is deliberately unoriginal: the spine prelude and source inversion
are the C-deref text, the endgame is the P→L text, and the only new sentence
is the one the event fix was added to make sayable. When the source's `.ref`
succeeds, it has just checked `addr + blockSize τ ≤ allocBase + allocSize`
against the pointer it loaded from memory; `MemValSim` says the target loaded
the *same* offset and size; so the target `Borrow`'s bounds check is the same
inequality in different variable names. `by_cases` on the check, one `grind`,
done. Compare the P→L increment, where the bound came from typing — each
closed regime now documents *where* its bounds obligation is paid: typing for
fields, the event for loaded pointers.

The fresh-tag bookkeeping composes with the spine without new lemmas: reads
don't mint, so the extension pair `(permsP'.NextTag, p2.NextTag)` rewrites
back to the state NextTags through the read-framing equations, and
`TagRenameBounded` transports across the spine for free.

Also in this increment, a grind audit of the new proof: seven manual
`Nat`-chains and injectivity dances collapsed to `grind`, two `have`s deleted.
The catalogued potholes all showed up on schedule — `subst` ate the wrong
variable, `omega` refused `Word`, an unascribed `LocalBindingSim` eta-expanded
— and one new entry for the list: a register that appears in an *evidence
type* cannot be rewritten away (dependent motive); quantify over it instead.

Audit stays at four, with the ref residual down to non-spine pointer places,
unbound destinations, non-local destinations, and proj-of-proj sources.
Units 16/16 + 44/44, suite pass 82 | fail 0 of 123, differential 82/0/0.

---

## 2026-08-28 — Retags Must Be Dereferenceable: an Event Fix, Not an Invariant Fix

Thirty-seventh increment (backfilled; landed with the morning commit). The
deref-source ref regime was blocked on a genuine model gap: the target
`Borrow` checks the borrow range against the loaded pointer's extent, and
nothing in mirlite's `.ref` implied it. The untyped-memory analysis showed
why no invariant could state the missing fact — `ptrVal (b,0,0,t)` is a legal
value at pointee `()` and junk at pointee `u64`, and only the retag *event*
knows the pointee type. Miri agrees: retags require their whole range
dereferenceable. So mirlite's `.ref` gained exactly that check, in range form
(`addr + blockSize σ > allocBase + allocSize`) so one-past-the-end ZST
reborrows stay legal. Reachable behaviour is unchanged — every mint site
stores the allocation's true size — confirmed by the full suite and
differential; the three already-closed ref regimes each needed one `if_neg`.
The invariant-gap example is pinned three ways: t16 forges the junk state and
demands the error (the suite's first state-level test, teeth-verified by
reverting the check), d30 runs the reachable reborrow, d31 the ZST corner.

---

## 2026-08-27 (night) — The Read-Side Keystone, and the Mixed Chains Close

Thirty-sixth increment. The two deref-rooted shapes — a projection and a
dereference in the same destination chain, in either order — are closed.
`(*p).f := v` works over any load spine: the spine lemma delivers the loaded
pointer and the C1 endgame finishes, with the parent tag now coming from a
loaded value rather than a local binding. And `*(s.f) := v` — writing through a
pointer *field* — is the first consumer of the new BRIDGE 1S.

BRIDGE 1S is the Mut keystone's read-side mirror: `Borrow(Shared); read via the
fresh tag; Die` nets to the bare parent read. What makes it the right lemma is
that mirlite *performs* that parent read — `resolvePlaceAcc` reads the pointer
cell when it dereferences — so the two machines reconcile with no new
invariant. Its phase 2 is where the symmetry is instructive: the Mut keystone's
middle phase rewrites every cell to itself, while the Shared one is a no-op
outright, because a read through a fresh `Ref` sitting on top of a stack has
nothing above it to disable. The proof was generated by systematically adapting
the Mut text, and compiled after one extra reduction — the fold machinery
underneath is op-agnostic enough that keystones now come in pairs for the cost
of one.

The dispatcher `const_write_deref_nonspine_simulation` is now a proved theorem,
and the residual class has a sharper name: *deep* chains — a second projection
segment below a dereference — which want the pending-cleanup generalization of
the spine lemma. Audit stays at four, with strictly more closed.

One process scar worth recording: a chunked edit deleted an entire adjacent
theorem, silently, because its end marker matched inside the next proof — and
the build stayed green, since the file remained well-formed minus one theorem.
The audit's habit of grepping for theorem *names* is what caught it; the text
was reassembled from the session's own patches. Splice markers must be unique,
and slice edits get a name-grep afterwards, always.

Units 15/15 + 42/42, suite pass 82 | fail 0 of 123, differential 82/0/0.

---

## 2026-08-27 (later) — GEP Stays a Borrow, of Exactly the Field

Thirty-fifth increment. The nested-projection divergence is fixed at its root,
per the design call that offset computation should remain a borrow: the two
place-lowering functions now *reassociate* projection chains —
`.proj (.proj b q) p` compiles as `.proj b (q.append p)` — so any projection,
however deep, emits one `Borrow` anchored at the chain root, at the composed
offset, with the final field's length. The retag spans exactly the accessed
field; intermediate places are never retagged. `PathTo` was already a
cons-chain, so composition is twelve lines and its offset is additive by
construction.

The interesting cost was not semantic but *proof-mechanical*: reassociation
recurses on a non-subterm, so both functions went from structural to
well-founded, and a well-founded definition stops unfolding definitionally.
Every `:= rfl` closed-form broke (six), the generic-projection equation became
conditional on "the base is not itself a projection", and two structural
inductions had to become functional inductions — whose generated principle
hands each case exactly the side condition the conditional equation needs.
None of it was deep; all of it was the predictable tax of changing a
definition eleven proofs deep, and the whole stack was green again within the
session.

The witness went from mismatch to matched with the corpus untouched, and is
now also pinned in-repo as differential test d26 — teeth verified by reverting
the arms and watching it fail with the exact divergence. And the two residual
theorems that were refuted this morning are true again, narrower than before:
nested-local-rooted bases no longer reach the general lowering arm at all, so
only deref-rooted shapes remain, provable with machinery that already exists.

Suite pass 81 | fail 0 of 122, differential matched 81 | mismatch 0, units
15/15 + 39/39.

---

## 2026-08-27 — The Keystone Earns Its Name

Thirty-fourth increment. `const_write_proj_simulation` closes for a bound-local
base, split by the projection's *offset* — which, it turns out, is what decides
the shape of the lowering. At offset zero `placeToRegChecked` hands back the
base's own register and the fragment is a bare `CStore`; the proof is regime A
with a wider `allocSize`, since a projected place's bounds come from the base's
layout rather than from the field's. At a nonzero offset the compiler mints an
internal `Borrow(Mut)` into a temp and records a `Die` that the assign arm
emits after the store.

That second shape is the first one in this development whose target mints a
tag, uses it, and then kills it — and so, twelve days and eleven closed regimes
after it was proved, BRIDGE 1 finally carries weight. `sb_ref_use_die_cancels`
says exactly what is needed: the triple's net effect on the borrow stacks is
the bare parent write the source performs, so `PermSim` transfers from
BRIDGE 3's result by rewriting three component equalities.

The more interesting result is that both of BRIDGE 1's side conditions turned
out to be *derivable* from the invariant rather than assumable. It takes the
retag's success as a hypothesis, and on the target nothing supplies it — the
source performs a bare write, so there is no retag to transport. But a mutable
retag is per cell a write followed by a push, and a push onto the stack the
write just produced cannot fail; write-success implies retag-success, proved by
feeding one existing lemma's output straight into another's input. And the
"fresh tag is unprotected" condition falls out of `TagRenameBounded` plus
`PermSim`: every tag in a target protector frame came through ρt, whose range
lies strictly below the counter, so the tag being minted *at* the counter
cannot already be protected. That is the third time the bound has paid for
itself beyond the case it was introduced for.

A pattern worth naming, since it has now recurred: every bridge needs a
companion *"…succeeds when…"* lemma on the target side, because the bridges are
stated as transports of a successful source event, and the target sometimes
performs an event the source does not. Copy's `Memcpy` will want the same.

The residual narrowed rather than vanished — a base that is itself a projection
or a dereference emits its own code and carries its own cleanup, so the `Die`
becomes a list rather than an instruction. Audit stays at 4. Suite pass 80 |
fail 0 of 121, differential 80/0/0.

---

## 2026-08-23 — Two Fresh Tags in One Statement

Thirty-third increment. `ref_fresh_dst_simulation` closes the
fresh-destination ref regime: `&src` stored into a local the source has not
yet bound, so mirlite's prepare allocates it and the fragment is three
instructions, `Alloc; Borrow; RStore`. Audit 5 → 4, and `CompilerInv_step_ref`
is down to a single residual.

What makes it worth an entry is that it is the first statement in which ρt
extends *twice* — `sb_own` mints the destination's root tag, then `sb_ref`
mints the reference tag. That composed with no new machinery, and the reason
is a decision made yesterday for an unrelated purpose: each minting member
*returns* the `TagRenameBounded` at the intermediate counters that the next one
*takes* as a hypothesis. Had the bound stayed a per-leaf side condition, the
second extension would have had nothing to stand on. It is the clearest
argument so far for putting facts in the invariant rather than in the
statement that first needs them.

ρa also grows, once, at the identity pair. The wrinkle relative to regime B is
that here the extension has to be transported into facts established *before*
it: `doAssign` resolves the source against the post-allocation state, so the
source local's address facts — including the block-domain conjunct added for
the L→L regime — cross the destination's allocation. That is mechanical, but
it is the first place two renames and an ordering constraint interact.

Two structural lemmas fell out, both reusable. `prepare_lookup_ne` says
preparing one local leaves other bindings alone. And a small dependent-typing
fact that had to be proved rather than assumed: a `PtrL τ` destination and a
`τ` source are necessarily *distinct* locals, because `Local` carries its type
proof and equal indices would force `τ = PtrL τ`. `grind` cannot see that —
its congruence closure happily puts `τ` and `τ.PtrL` in one equivalence class
— but `congrArg sizeOf` plus `simp` kills it in a line.

Suite pass 80 | fail 0 of 121, differential 80/0/0, units green.

---

## 2026-08-22 (last) — A Witness Closes Two Gaps, and rustc Refutes a Third

Thirty-second increment, and a short one on the proof side: `ref_zst_residual`
is gone, audit 6 → 5, and it was closed by removing its cause rather than by
proving it. The OSEA target's `Rhs.Borrow` bounds check was
`addr ≥ base + size`, which rejects every zero-sized retag; it is now the range
form `addr + len > base + size` — Miri's actual requirement, the same form
`writeThroughPtr` already used, and one that admits the one-past-the-end
address a ZST borrow legitimately has. It is *stricter* for multi-cell retags,
and the differential did not move. The L→L regime dropped its
`0 < blockSize τ` side condition the same hour.

That is the second time today a proof obligation was discharged by aligning a
machine with Miri instead of by a proof — the first was the opaque `BEq`. Both
were found by attempting a leaf, which is becoming the pattern: the proofs are
now a sharper conformance oracle than the suite for anything the corpus does
not exercise.

The home-grown witness `local/zst_ref` did all of this. It was written to probe
one claim — the target's ZST check — and found a loader gap standing in front
of it (unit assignments dropped, so ZST locals were never allocated), then,
once that was fixed, exposed the target check as the differential's single
mismatch, then passed end to end. Three signals, in order, from one
twelve-line program.

The follow-up probe went the other way. I had hypothesised that dropping
`StorageLive/Dead` and allocating at first assignment could be exposed by a
borrow-before-write. rustc refuses to compile that program (E0381); the only
legal form is `MaybeUninit`, a union, outside the surface. So for the union-free
fragment the borrow checker *guarantees* the property the lowering relies on.
The hypothesis is superseded, and the probe is registered `unsupported: unions`
so it lights up if that ever changes.

Suite pass 78 | fail 0 of 119, differential matched 78 | mismatch 0, units and
all targets green.

---

## 2026-08-22 (late) — The Ref Leaf Opens: a Derived Instance Was the Wall

Thirty-first increment. `ref_local_local_simulation` is proved — `dst := &src`
with both locals bound — and it is the first leaf that grows ρt at a tag the
*program* can see. Until now every fresh tag the simulation had to pair was a
compiler-internal temp; here the source's reference tag and the target's are
paired by `sb_ref_respects_PermSim` and then *stored*, so the extended ρt has to
carry all the way into `MemValSim`.

The day's real story is what blocked it first. `obseq.TyVal` is a nested
inductive, and `deriving BEq` on a nested inductive produces a `partial def` —
which compiles to an `opaque` constant with no equations. The instance
evaluated perfectly (every suite was green) and was completely invisible to
the logic: `(PTy == PTy) = true` was unprovable by any tactic. `oseair`'s
`RStore` is guarded by exactly that comparison, so no theorem could step over
an `RStore`, and the ref fragment is `Borrow; RStore`. `deriving DecidableEq`
refuses the type outright, as the hand-written `layoutDecEq` in the same file
had quietly been telling us.

The fix is the one the file's own precedent suggested: a mutual structural
`beq`, plus a `LawfulBEq` instance so the guard discharges over a *variable*
type, not only on constructor forms. That last part matters more than this
leaf — `alloc`, `exposeAddr` and `refSlice` all end in an `RStore` and now
inherit `runN_RStore_step` unchanged. It cannot have broken existing proofs,
because the old instance had nothing to depend on; behaviour is pinned by the
lawfulness proof and by every suite coming back identical.

Two smaller facts worth keeping. The ref fragment has no `Die` when the
destination is a local — the borrow *is* the stored value — so this leaf never
needed BRIDGE 1; the keystone enters `ref` only through a non-local
destination. And the block-domain conjunct added to `LocalBindingSim` this
afternoon is precisely what the stored pointer's `MemValSim` consumes.

A second divergence surfaced and is parked: for a zero-sized referent the
target's `Borrow` bounds check fires while mirlite's retag does not, and here
Rust sides with the *source*. The closed regime carries `0 < blockSize τ`.

Audit 4 → 6 by the same accounting as the D1 split: the ref leaf is now a
dispatcher over one closed regime and three named residuals. Validation
unchanged across all suites.

---

## 2026-08-22 (night) — Regime B Closed: the Audit Moves Again

Thirtieth increment, and the first time the audit count has dropped since the
deref spine. `const_write_fresh_local_simulation` is proved: a constant write
to an unbound local, where mirlite's prepare allocates it and the compiled
fragment is `Alloc; CStore`. Five sorries become four.

It is the only regime that grows *both* renames, and the asymmetry between them
is the interesting part. ρt's extension is delicate — `TagRenameBounded` is
load-bearing twice, once for injectivity and once to make the extension an
extension rather than an overwrite. ρa's extension needs no side condition at
all, because `IdentityOnDomain` already does both jobs: if the fresh address
were somehow already mapped, it would already be mapped to itself. The identity
discipline on ρa, chosen back when v3's rename maps were designed, pays for
itself exactly here.

The proof did need a tenth `CompilerInv` conjunct: `UnboundLocalsUnmapped`, the
converse of `LocalBindingSim` on the mapping component. Without it nothing in
the invariant says whether the fragment begins with the root `Alloc` or is the
bare `CStore` of regime A — the two regimes are distinguished by a fact the
invariant simply had not been asked to carry. Source `preparePlaceAssign` and
target `ensureLocalRegE` allocate the root at the same statement, so the two
notions of "exists yet" do agree; the invariant just had to say so.

This also confirmed this afternoon's prediction. Regime B was the third
`CompilerInv` construction site, and its conjunct cost three bullets instead of
two. The sequencing lesson stands: wire conjuncts before closing the leaf that
adds a site.

Four sorries left — the two `Borrow`-emitting const_write regimes, copy, and
the ref leaf — and all four are leaf-local proof work. The SB machinery is
done. Validation unchanged: units 15/15 + 38/38, suite pass 77 | fail 0 of 117,
differential matched 77 | mismatch 0 | skipped 0.

---

## 2026-08-22 (end of day) — Lockstep Allocation, and Regime B Runs Out of Excuses

Twenty-ninth increment. `CompilerInv` gains a ninth conjunct,
`AllocLockstep s_mir.mem s_osea.mem` — the two bump allocators sit at the same
watermark.

The reason it belongs in the invariant rather than in a leaf is worth stating.
`IdentityOnDomain ρa` is already a conjunct, and it is false the moment the two
machines hand out different addresses for corresponding allocations. So a fresh
local can extend ρa by `.refl` only if the allocators are in lockstep — and
that is a property of the whole execution history, not of the statement being
simulated. It has to be carried.

Cheaper than this afternoon's `TagRenameBounded` wiring, which was already
cheap. Two construction sites got one bullet each, since a store moves no
watermark, and the load spine needed no change at all — it never touches memory
on either machine.

That is now two invariant conjuncts in an afternoon, both about an hour, both
with the same shape: define the fact, prove that the operations the closed
regimes actually perform leave it alone, add one bullet per construction site.
The cheapness is structural rather than lucky: `CompilerInv` is *constructed*
in exactly two places, and every other theorem either takes it as a hypothesis
or passes it through a delegation. That will hold until a third construction
site appears — which regime B will be.

And regime B is now out of machinery excuses. `sb_own` mints its root tag and
extends ρt; `AllocLockstep.allocate_eq` makes both machines allocate at the same
address. What is left is leaf-local: invert mirlite's `allocateBase`, execute
the target's `Alloc` fragment, extend `SourceMemSim` and `LocalBindingSim` at
the new cell.

Audit stays at 5, but for the first time none of the five is waiting on a
missing lemma. Validation unchanged: units 15/15 + 38/38, suite pass 77 |
fail 0 of 117, differential matched 77 | mismatch 0 | skipped 0.

---

## 2026-08-22 (later still) — `sb_own` Closes the Transport Family

Twenty-eighth increment. `sb_own_respects_PermSim` completes BRIDGE 3 over all
five range ops. Nothing in the proof core's SB surface is now without a
transport.

This one is worth recording mostly as a confirmed prediction. The morning's
note said `sb_own` would reuse the `sb_ref` increment wholesale and cost a
fraction of it; it did, and it compiled on the first attempt. Every piece of
the ρt-extension algebra applied verbatim. The difference in cost — a morning
versus a day — traces to one thing: `ownCell` was already a named top-level
cell op, whereas `sb_ref`'s per-cell action was an inline `match` that had to
be factored out of the model before anything could be said about it under a
`RefKind` variable. That is a lesson about how to write the model, not about
the proof.

The one genuine wrinkle: `ownCell` is the only cell op that *succeeds* on a
missing stack — creating the cell is its whole job — so it does not fit
`foldCells_ok_inv`, whose per-cell function hard-codes failure on absence. The
indexed fold's characterizations already take an `Option`, so the fix was a
bridge rather than a duplicate: `foldCells_ok_iff_foldCellsIdx_ok`. The two
folds are not equal as functions, because they decorate errors differently —
one names the failing address, the other the offset — but they agree on
success, which is all any consumer needs. Stating the iff rather than an
equality kept it to a 20-line induction.

Regime B now has exactly one machinery blocker left: the lockstep-allocation
conjunct, `s_osea.mem.addrStart = s_mir.mem.addrStart`, which is what lets ρa
extend at the *equal* fresh address. On the evidence of this afternoon's
`TagRenameBounded` wiring, that should be cheap.

Audit stays at 5. Proof layer only — no model changes. Validation unchanged:
units 15/15 + 38/38, suite pass 77 | fail 0 of 117, differential matched 77 |
mismatch 0 | skipped 0.

---

## 2026-08-22 (later) — The Bound Becomes an Invariant

Twenty-seventh increment, and the short half of the previous one.
`TagRenameBounded` is now an eighth conjunct of `CompilerInv`, which is what
turns this morning's `sb_ref` transport member from a proved lemma into an
applicable one: the member takes the bound as a hypothesis, so no leaf could
have used it while the invariant did not carry it.

The wiring was cheap for a reason worth naming. The bound only moves when a
counter moves, and the three access ops do not move counters — `sb_write`,
`sb_read` and `sb_die` rewrite stacks and nothing else, which falls straight
out of the existing fold inversion (the result is `{ ap with StackMap := … }`,
so `NextTag` is syntactically the old one). Both `CompilerInv` construction
sites — regime A and the deref spine — discharge their new obligation by
rewriting through those three equalities and handing the incoming bound back
unchanged.

The spine needed one genuine addition: `loadSpine_lowering_sim` now also
reports that neither machine's `NextTag` moved. Without it a consumer cannot
carry the bound across a spine of unknown depth, because the induction is
exactly where the counters would otherwise go opaque. Both cases are cheap —
two `rfl`s in the base, the IH composed with `sb_read_NextTag` in the step.

Blast radius: four proof obligations and three destructuring patterns. Smaller
than an eighth conjunct sounds, because `CompilerInv` is built in only two
places today and the delegating theorems pass it through. The same should hold
for the lockstep-allocation conjunct regime B still wants.

Audit stays at 5, but the shape of the remaining list has changed: three of
the five are now blocked on proof work rather than on missing machinery.
Validation unchanged: units 15/15 + 38/38, suite pass 77 | fail 0 of 117,
differential matched 77 | mismatch 0 | skipped 0.

---

## 2026-08-22 — The Minting Transport: `sb_ref` Respects `PermSim`

Twenty-sixth increment. `sb_ref_respects_PermSim` completes the BRIDGE 3
transport family. The three non-minting ops landed on 08-18 and 08-19; this is
the fourth and structurally different one — `sb_ref` creates a fresh tag, and
the two machines mint at their own counters, so the theorem cannot conclude for
the ρt it was given. It concludes for `ρt` extended at the fresh pair.

That extension is only legitimate under a fact the audit has been naming since
regime C without having it: `TagRenameBounded ρt nS nT`, every mapped pair below
both counters. It earns its keep twice over. The *range* bound puts the target's
fresh tag outside ρt's range, which is exactly what keeps the extended map
injective. The *domain* bound gives `ρt srcFresh = none`, which is what makes
the operation an extension rather than a silent overwrite. Miss either and
`TagRenameWF` does not survive the step. This is the tag half of the
strengthened well-formedness condition whose register half landed the day before
as `PlaceRegMapBound`.

Two model factorings preceded the proof, both behavior-preserving and both in
the tradition of `readCellContent`: `insertAboveContent` out of
`insertAboveCell`, and `refCellOp` out of `sb_ref`. The second matters more than
it looks. `sb_ref`'s per-cell action was an inline `match kind with ...`
producing lambdas — a shape that cannot be reasoned about under a `RefKind`
variable without case-splitting the entire proof five ways. Naming it lets the
proof side collapse all five retag variants into one stack-to-stack function, so
the same `foldCellsIdx` inversion/construction pair the other family members use
applies unchanged, and the kind analysis is confined to two small lemmas. The
construction half of that pair, `foldCellsIdx_ok_of_cells`, did not exist before
today; the indexed fold had only its inversion.

The member unblocks three of the five remaining sorries — the `ref` leaf and
both `Borrow`-emitting `const_write` regimes. It does not close them: `CompilerInv`
does not yet carry `TagRenameBounded`, and every consumer needs it as a
hypothesis. Adding it as an eighth conjunct is the next increment, and a cheap
one — the closed regimes transport permissions with `sb_write`/`sb_read`, which
do not move `NextTag`, so their bound is literally unchanged.

Audit stays at 5. Validation unchanged throughout: units 15/15 + 38/38, suite
pass 77 | fail 0 of 117, differential matched 77 | mismatch 0 | skipped 0.

---

## 2026-08-21 — Regime D Spine-Complete: One Induction Replaces Three Theorems

Twenty-fifth increment. `const_write_deref_spine_simulation` closes the constant
write through EVERY all-deref pointer chain (`*p`, `**q`, any depth) in one theorem,
subsuming the morning's depth-1 regime D1 and dissolving the D2/D3 residual split —
regime D's only remaining sorry is a projection in the chain, which shares regime C's
sb_ref blocker. The engine is `loadSpine_lowering_sim` (new proof/spine.lean): an
induction over load-spine places whose conclusion hands the consumer a register with
the ρ-renamed resolved pointer plus PermSim of the threaded perms and full framing.
Attempting the induction surfaced a real semantics gap no test had hit: the target
Load bounds-checks loaded pointers, mirlite's deref resolution didn't — the theorem
was unprovable without either a perms↔mem coherence invariant or the mirrored check.
Took the check (Miri's dereferenceable requirement, the read-side mirror of the write
bounds check); suite unchanged 77/117, differential 77/0/0, t15/d25 pin the OOB
alignment. The proof-shaping lesson worth keeping: sub-fragment code installation
threads through `CheckedCompilerM.incr` + bind decomposition with tails kept folded —
no closed forms needed — the pattern copy/ref/dealloc will reuse. Audit 6 → 5
sorries; units 15/15 + 38/38; obseq2 green.

---

## 2026-08-21 — Regime D1 Closed: The Canonical Deref Write Simulates

Twenty-fourth increment, same-day payoff of the deref-read change. `*p := v` with a
bound pointer local now simulates end-to-end (`const_write_deref_local_simulation`):
Load matched by the source's resolvePlaceAcc read via the sb_read transport, loaded
value recovered as the ρ-renamed stored pointer via MemValSim inversion, CStore via
BRIDGE 2 + sb_write. Two honest invariant extensions were needed (the morning's
"existing machinery only" was over-optimistic): the `PlaceRegMapBound` conjunct
(mapped registers < nextReg — the register half of obseq2's never-built strengthened
CompilerStateWF; fresh Load temps cannot clobber bound locals) and a strengthened
MemValSim pointer case (non-wildcard stored tags + referent range in ρa's domain).
The proof was deliberately factored for reuse: Load step execution, deref-resolution
inversion, fresh-register binding-sim preservation, RegMap update algebra (+ a
LawfulBEq Register instance), mapped-local lowering run/value, emit_nil — all in
common §D/§E/§F, consumed next by D3's spine induction, regime C, copy, and ref.
Regime D delegates by pointer-place shape: D1 closed (fresh-local vacuous), D2 (proj
pointer) merges its blocker with regime C's sb_ref transport, D3 (nested deref) is
mechanical spine induction. Sorry count 5 → 6 by the split, but every closed shape is
end-to-end. Validation: 14/14 + 37/37, suite 77/117 pass, differential 77/0/0,
obseq2 green.

---

## 2026-08-21 — Deref Resolution Reads: Risk Item (a) Resolved at the Source

Twenty-third increment. mirlite place resolution for accesses (`resolvePlaceAcc`) now
performs a real SB read per deref level — Miri's operand-read behavior and what the
compiled `Load` already did. The divergence was real (`&mut p` disabled by `*p`'s
evaluation: source-ok/target-UB before, Miri with the target); it is now pinned by t14,
d24 (the program that previously mismatched), and a NEW `conformance/local/` witness —
project-authored Rust through the same charon pipeline, provenance-marked
model-reasoned pending a real Miri run. `doAssign` resolves the destination once, with
accesses, before the rhs (the compiled order); the dead `finishPlaceAssign` path is
gone. Validation all green first run: Miri corpus unchanged (its verdicts already
assume the reads), differential extended to 77/0/0, suite pass 77/117. Regime D's
blockers collapse to fragment execution — the source read's success now transports via
`sb_read_respects_PermSim`, no SB-env coherence needed for deref.

---

## 2026-08-18 — Regime A: the First End-to-End Statement Simulation

Twenty-second increment. The const-write evidence lemma is total (fresh-root branch via
`ensurePlaceRoot_maps_root`), and REGIME A — constant write to a bound local — is proved
end to end: fragment computation and location, BRIDGE 2 execution (its conclusion made
concrete for this), BRIDGE 3 permission transport (first consumer of the new
non-wildcard binding-tag fact in `LocalBindingSim`), full invariant rebuild.
`const_write_resolved_simulation` is now a proved delegation over regimes. This is
obseq2's long-parked "Step 4 regime-A milestone", done against the corrected PermSim
invariant. Enabling surgery: the never-consumed `CompilerStateWF` conjunct dropped
(returns strengthened when the proj regime needs it). The five remaining sorries each
carry a NAMED missing invariant extension (lockstep allocation, strengthened WF, SB-env
coherence, bidirectional memory, tag bounds) — invariant-design increments, exactly the
"blocking factors" obseq2's own comments predicted. All suites unchanged.

---

## 2026-08-18 — Bridges 2 and 3 Closed: the Transport Family Lands (audit 7 → 4)

Twenty-first increment. All three common.lean sorries closed. The §E combinator glue
was mechanical once binds got explicit arguments. BRIDGE 2 (`writeThroughPtr_sim`)
needed only pointwise memory reasoning — `SourceMemSim.write_extend` (obseq2's
single-cell core) folded over paired value lists — no setChain machinery, exactly as
assessed. BRIDGE 3 (`sb_write_respects_PermSim`, new proof/permsim_transport.lean,
~560 lines) is the ρt-transport family executed per the refactor plan: generic
`ListRel` transports, the `beq_eq` injectivity workhorse, constructor-preserving
`ItemSim` facts (why the relation was designed that way — SRW grouping via
`reverse ∘ takeWhile` transports for free), `splitStack`/`firstProtectedIn`/
`writeCellContent` transports, and relational `setChain`, riding the keystone's new
`foldCells_ok_inv`/`writeCell_content_form` wrappers. Non-wildcard acting tags only —
core programs cannot mint wildcards, so the `resolveWildcardIn` transport defers with
the non-core constructs. Remaining: the four leaf-side sorries (order 4→1→2→3).
All suites unchanged (pass 76, differential 76/0/0, units 13+36).

---

## 2026-08-15 — Keystone Closed: Ref-Use-Die Cancellation via a setChain Normal Form

Twentieth increment. `sb_ref_use_die_cancels` — the lemma obseq2's const_write sorry
silently depended on and never stated — is now a theorem (proof/keystone.lean, no
sorries; audit 8 → 7). Enablers: a behavior-preserving sb.lean refactor (content
functions `writeCellContent`/`dieCellContent` factored out of the per-cell ops;
`sb_ref`'s nested `let rec` promoted to a top-level `foldCellsIdx` — nested let-recs
are unaddressable in proofs; suite re-verified identical) and a small fold theory:
content-driven cell folds normalize to `setChain`s, and since `SB.set` is
move-to-front, chains collapse only under the explicit normal form
`entries.reverse ++ filtered original` (`setChain_normal`/`setChain_override`) —
pointwise equality wouldn't feed `PermSim`'s raw-list comparison. The three target
phases (ref-fold pushes `MutRef t' :: wⱼ`; write-through-top rewrites it unchanged —
the fresh Unique's pop-set is empty; die pops back to `wⱼ`) collapse entry-for-entry
onto the source's single write fold. Side conditions (fresh tag ≠ wildcard, not
protected) are reachable-state invariants — the future WF conjunct. Notable pothole:
`omega` cannot see through the `Word`/`Tag` Nat-abbrevs in 4.28. All suites unchanged
(pass 76, differential 76/0/0, units 13+36).

---

## 2026-08-15 — obseq3 Proof Skeleton: PermSim Corrects the Invariant (8 audited sorries)

Nineteenth increment. `src/obseq3/proof/` (Obseq3Proof lib): both top-level theorems —
`CompilerInv_step` and `compile_correct` for the CoreProg fragment — are FULLY PROVED,
complete modulo 8 audited sorries (audit + closing order at the top of
proof/compiler.lean). The headline is a correction to obseq2's invariant: its conjunct
`s_osea.ap = s_mir.perms` is false beyond local-only places (internal borrows advance
NextTag; die pops items, not the counter; after the split every corresponding tag VALUE
differs). v3 replaces it with `PermSim ρt` — item-wise ρt-renamed stack equality
(constructor-preserving, so SRW-group/Disabled structure is identical), renamed
protFrames/exposed, NextTag ≤ — with ρt injective-fixing-wildcard rather than identity.
~85% of common.lean is proved (prefix machinery, mem statics over the v3 instruction
set, PermSim vocabulary + rename_mono, lowering totality + the new
`ensurePlaceRoot_run_eq_of_mapped`, Die-run helpers, runN composition); the 8 sorries
are the 3 simulation leaves, 3 bridges (keystone `sb_ref_use_die_cancels` — the lemma
obseq2 never wrote; range `writeThroughPtr_sim`; `sb_write_respects_PermSim`), and 2
mechanical stragglers. oseair.runN reverted to idle-fuel semantics (nothing used the
early stop; it broke `runN_add`). Suite + differential unchanged: pass 76, matched 76/0/0.

---

## 2026-08-15 — OSEA-v3 refSlice: Full-Suite Differential (76/76, 0 mismatches)

Eighteenth increment, closing the coverage arc. `Rhs.BorrowRest (kind, prot, srcPtr)` —
the runtime-length slice retag (`len := size − offset` from the stored fat value, mask
always []) — was the last uncompiled construct. Differential: **matched 76 | mismatch 0 |
skipped 0**: every passing conformance test compiles to OSEA-IR and agrees with mirlite,
UB attributed to the same source statement throughout. The compiler is now total on
obseq3's statement/rvalue surface (g5 re-purposed as a totality witness). Eight
increments, each with zero mismatches on first run — evidence that the compilation
discipline (mirror mirlite's event order; reads live inside instructions; Die only for
compiler-minted tags) was right. Unit tests 36/36 (g13 golden; d22 slice write; d23 the
fnentry_invalidation2 popping mechanism).

---

## 2026-08-15 — OSEA-v3 Pointer Ops: ptrCast for Free, PtrOffset Pre-Scaled (matched 75/76)

Seventeenth increment. `ptrCast` compiled with NO new instruction — mirlite's semantics
(tag-preserving one-cell copy with an SB read) is exactly `Memcpy` at PTy; that's the
third construct absorbed by an existing instruction (after uninit → CStore-of-Undef and
const-alloc → AllocN). `Rhs.PtrOffset` carries its delta pre-scaled to cells
(delta · blockSize of the source pointee, known statically — the Die-length pattern);
runtime reads the cell via the place's tag, shifts the STORED pointer's offset with tag
preserved, and errs on negative-past-base like mirlite. Differential: **matched 75 |
mismatch 0 | skipped 1** — the sole remaining skip is fnentry_invalidation2, blocked on
`refSlice`, the last uncompiled construct. Unit tests 33/33 (g12 pins the scaling;
d19/d20 the cast-and-add idiom; d21 offset-before-base UB).

---

## 2026-08-15 — OSEA-v3 SkipIf: the First Branch (matched 71; 93% differential)

Sixteenth increment. `assignIf` compiles via `Instr.SkipIf discrPtr val skip` — an
event-free discriminant peek (mirlite's raw `mem.find?`, no SB read) with a forward-only
jump over the guarded block, whose length is measured by a dry-run compilation
(`emitSkipIfAround`; sound because instructions carry only registers and relative skips,
so emitted content is start-label-independent). The code-map `Prog = Nat → Option Instr`
design absorbed the first branch with no interpreter-shape changes; statement ranges stay
contiguous so UB attribution is untouched. The skip suppresses the block's SB *events*,
not just its store (d17: a skipped guarded write leaves a `&mut` alive that the block's
Borrow would have popped). One latent asymmetry recorded, unreachable from the corpus:
a fresh local first assigned under a skipped guard. Differential: **matched 71 |
mismatch 0 | skipped 5** (all 3 enum tests agree; remaining ptrCast 3 · ptrOffset 2).
Unit tests 29/29, count now derived from the test list.

---

## 2026-08-15 — OSEA-v3 Exposed Provenance (matched 68; 89% differential)

Fifteenth increment. `Rhs.ExposeAddr`/`Rhs.FromExposed` as a pair, with the allocs table
+ `resolveAddr` ported into `oseair.Mem`. The subtle split: ExposeAddr reads the pointer
cell via the *place's* tag but exposes the *stored* pointer's tag; FromExposed yields a
`wildcardTag` pointer whose resolution lives entirely in the permission model, so use
sites need no new machine logic. `allocate` records every allocation (locals and heap,
as mirlite's single allocate does) — that shared bookkeeping is what makes both machines
resolve the same integer to the same allocation. Differential: **matched 68 |
mismatch 0 | skipped 8** (remaining: assignIf 3 · ptrCast 3 · ptrOffset 2). Unit tests
25/25 (g10; d14 round trip; d15 exposed-then-invalidated wildcard UB).

---

## 2026-08-15 — OSEA-v3 Heap Alloc/Dealloc (matched 63; 83% of suite differential)

Fourteenth increment. `Rhs.AllocN`/`Rhs.AllocDyn` + `Instr.Dealloc`, with
`Mem.removeRange` ported to oseair. Everything is event-order fidelity: dst-root Alloc
before the length read (mirlite's `preparePlaceAssign` order — keeps bump allocators
address-identical); `AllocDyn` performs mirlite's `readAllocLen` SB read *inside* the
instruction; `Dealloc` takes the loaded pointer register (the `Load` is mirlite's
pointer-cell read) and checks offset/size against the stored value — no allocs table
needed until fromExposed. Differential: **matched 63 | mismatch 0 | skipped 13**
(all 7 heap tests incl. dealloc-against-protector agree; remaining: exposeAddr 5 ·
assignIf 3 · ptrCast 3 · ptrOffset 2). Unit tests 22/22 (g8/g9, d10 lifecycle,
d11 use-after-free, d12 double free, d13 runtime length).

---

## 2026-08-15 — OSEA-v3 uninit: CStore of Undef, No New Instruction

Thirteenth increment. `RExpr.uninit` compiles to `CStore ty (replicate blockSize Undef)` —
CStore already stores arbitrary `Val` lists through a useMut write, which is exactly
mirlite's undef fill. Undef cells are verdict-inert on both machines (SB never inspects
values), so partially-initialized aggregates copy identically through Memcpy.
Differential: **matched 56 | mismatch 0 | skipped 20**; uninit was first-blocker in only
3 of its 6 tests (histogram now alloc 7 · exposeAddr 5 · assignIf 3 · ptrCast 3 ·
ptrOffset 2). Unit tests 16/16 (golden g7, differential d9 incl. partial-init tuple copy).

---

## 2026-08-15 — OSEA-v3 Protector Frames (matched 25 → 53)

Twelfth increment, ~20 lines: `Instr.PushProt`/`PopProt` in oseair calling
`M.pushFrame`/`M.popFrame` (pop errors propagate as target UB), emitted directly from
`Stmt.pushProtectors`/`popProtectors`. The protected seam-retag borrows already carried
`prot` into `Rhs.Borrow`, so only the frame bracketing was missing. Differential:
**matched 53 | mismatch 0 | skipped 23** — every otherwise-core inlined-call test now
agrees with mirlite, protector UB attributed to the same statement. `assignIf` (3 tests)
surfaced from behind pushProtectors. Unit tests 14/14 (golden g6, differential d7/d8).

---

## 2026-08-15 — OSEA-IR v3 and the Differential Oracle (compiler back online)

Eleventh increment: the mission's compiler leg restarts on the v3 semantics.
`src/obseq3/oseair.lean` forks the v2 target with the machine parameterized by
`obseq3.PermissionModel` (`perms : M.State`, symmetric with mirlite, so a future
`CompilerInv` states `s_osea.perms = s_mir.perms` verbatim), all permission calls
range-based, and one `Rhs.Borrow (kind, prot, mask, len)` replacing the three v2 borrow
forms; `Die` carries the borrow's static length. `src/obseq3/compile.lean` ports the
Checked compiler family for the proof-core subset (constInit/copy/ref/halt; everything
else `CompilerError.unsupported`). Three deliberate scheme changes vs v2: deref lowering
no longer dies the loaded pointer register (its tag was loaded, not minted — dying it
would pop the source's own reference under per-cell stacks); `ensurePlaceRoot` allocates
a projected destination's root local before the rhs, mirroring mirlite's
`preparePlaceAssign` (aggregate desugaring assigns `_x.0` first); allocation order
matches mirlite so both machines mint identical addresses.

The harness gained `--osea`: compile each loaded program, run it, and require the same
verdict as mirlite — with target UB attributed to a source statement via per-statement
label ranges (`stmtLabelRanges`). First run: **osea: matched 25 | mismatch 0 |
skipped 51**; 14 of the matches are fail-tests UB-matched at the exact statement.
None of the plan's three GEP-as-ownership-events risks fired (the Raw-temp Die risk is
vacuous: compiler temps are never Raw). Skip histogram: pushProtectors 31 · alloc 6 ·
uninit 6 · exposeAddr 5 · ptrCast 2 · ptrOffset 1 — parked as named instruction designs.
Unit tests: 5 golden + 6 differential (2 negatives). Suite unchanged: pass 76 | fail 0.

---

## 2026-08-15 — The Box Unique Retag: Claim Unqualified

Tenth increment. Suite: **pass 76 | fail 0 | xfail 0 | xpass 0** — fail tests **56/75**
(48 line-accurate), 20 pass scenarios. Box arguments now receive miri's box retag at
inline seams: a protected Unique reborrow of the pointee (`UTy.boxT`; `Box::from_raw` =
tag-preserving copy; `mem::forget` = no-op). `box_noalias_violation` — whose expected
error, "weakly protected", is a category existing solely for this rule — is conformant at
miri's line, and all previously-passing Box tests held. The conformance claim loses its
one SB-policy qualification; what remains documented is the weak-vs-strong protector
dealloc nuance and untagged plain Box assignments, both unexercised by any reachable
test. The 19 remaining fail tests are language surface only.

---

## 2026-08-14 — The Conformance Claim: Complete SB Rule Coverage

Ninth and final increment of the session. Two stragglers whose unsupported-reasons
predated later increments turned out to already be reachable: `illegal_read_despite_exposed2`
(pure exposure machinery — the wildcard read Disables the Unique in place) and
`invalidate_against_protector3` (a `Layout::for_value` shim; protector violation on heap
cells). Suite: **pass 75 | fail 0 | xfail 0 | xpass 0** — fail tests **55/75**
(47 line-accurate), 20 pass scenarios.

With that, the claim (user's framing: compliance is about the model's rules, not the
language surface): **obseq3 implements the complete Stacked Borrows rule set**, each
mechanism witnessed by conformant tests — the rule → witness table is in
conformance/README.md, the durable statement in notes/durable/sb-conformance-claim.md.
The 20 remaining fail tests are blocked on SwitchInt, containers, threads, drop glue,
closures, or unions — the same SB rules through more language. One genuine SB-policy
simplification is documented: Box as implicit raw (no Unique box retag/protector;
box_noalias_violation alone needs it).

---

## 2026-08-14 — Slices: the First Runtime-Length Retags

Eighth same-day increment. Suite: **pass 73 | fail 0 | xfail 0 | xpass 0** — fail tests
**53/75** (45 line-accurate), 20 pass scenarios, 43 unsupported.

Slice references are one-cell fat values (the ordinary `ptrVal`) whose length is the rest
of their allocation; reborrows of slice data are `RExpr.refSlice` — the model's first
retag whose length is read at runtime (`size − offset` cells via the fat value's tag).
Unsize coercions are value copies; `as_ptr`/`as_mut_ptr` shims reproduce the receiver's
fn-entry retag before the raw data retag. Two fidelity facts pinned by
`fnentry_invalidation2` (now conformant at miri's exact line): named-struct fields are
NOT fn-entry-retagged (new `structT`/`tup` distinction — tuples ARE retagged, per
pass_invalid_shr_tuple), and call-replacing shims must carry the callee's entry retag
(the first draft missed the UB precisely because it didn't). The remaining 22 unsupported
fail tests all need dynamic control flow, std containers, threads, drop glue, unions, or
MaybeUninit — the retag-rule frontier is complete.

---

## 2026-08-14 — Arrays and Constant Pointer Arithmetic

Seventh same-day increment. Suite: **pass 72 | fail 0 | xfail 0 | xpass 0** — fail tests
**52/75** (44 line-accurate), 20 pass scenarios, 44 unsupported.

Fixed-size arrays are homogeneous tuples; charon's operand-carrying `Index` projections
resolve to static fields through tracked constant locals; `Repeat` rvalues and array
aggregates desugar per element; built-MIR bounds checks (`BinaryOp(Lt)` + `Assert`) are
const-folded away at lowering (dynamic arithmetic stays unsupported — arithmetic exists
only in statically-foldable positions). `ptr.add/offset/wrapping_offset` shim to
`RExpr.ptrOffset`: a constant delta scaled by pointee size, provenance-preserving, with
signed constants now parsed. Newly conformant: `unescaped_static` (UB at cell offset 1 —
the per-cell stacks in their purest form), `transmute-is-no-escape`
(`wrapping_offset(-1)` lands on a cell where the transmuted tag never existed), and the
`array_casts` pass scenario. Slices proper (fat pointers, runtime lengths) remain the
honest boundary.

---

## 2026-08-14 — RefCell Shims, SharedReadWrite Grouping, and the Disabled State

Sixth same-day increment. Suite: **pass 69 | fail 0 | xfail 0 | xpass 0** — fail tests
**50/75** (42 line-accurate), 19 pass scenarios, 47 unsupported.

RefCell is supported by *flag-eliding* shims (the borrow-flag discipline is a dynamic
borrow checker orthogonal to SB): `borrow`/`borrow_mut` = masked/unique reborrows of the
value region; `Ref`/`RefMut` guards = raw-layout values, deliberately unprotected at seams
(the `ref_protector` tests assert miri adds no protector for struct-wrapped refs); guard
`deref`/`deref_mut` = typed loads whose load-retag is the reborrow; `replace` and
`mem::drop` shimmed. Valid for conflict-free executions — all the corpus exercises.

Landing this forced the last core-model divergence closed, in two coupled fixes:
**SharedReadWrite grouping** (a write through an SRW item pops only above its contiguous
SRW run — `ref_mut_protector` needs the autoref sibling to survive) and **the Disabled
state** (reads disable Uniques in place rather than removing them; grouping without
Disabled merged groups and broke `disable_mut_does_not_merge_srw` + `interior_mut2` —
caught as missed-UB by the harness, exactly the failure mode miri's test comment warns
about). Newly conformant: `shared_rw_borrows_are_weak2` plus six `interior_mutability`
scenarios.

---

## 2026-08-14 — Transmute and Exposed Provenance (int-to-ptr without angelic choice)

Fifth same-day increment. Suite: **pass 62 | fail 0 | xfail 0 | xpass 0** — fail tests
**49/75** verdict-conformant (41 line-accurate), 13 pass scenarios, 48 unsupported.

The only memory-model addition is `Mem.allocs`, an allocation table making
address→(base, offset, size) a *function* — concrete Nat addresses under the deterministic
bump allocator mean int-to-ptr resolution needs no angelic choice (miri does the same
range lookup). Provenance semantics lives entirely in the SB state: an `exposed` tag set,
a reserved `wildcardTag` (so `ptrVal` and the access signatures are unchanged), and
per-access wildcard resolution to the topmost exposed granting item — a determinization of
miri's angelic wildcard, matching `-Zmiri-permissive-provenance` on all covered tests.
The ptr→int→ptr round trip deliberately destroys tag provenance: integers are bare words;
authority is re-derived at each access.

Transmute is shimmed by destination type (to-raw = tag-preserving `ptrCast`; to-ref = a
real retag — `illegal_write4` shows miri retags transmute-to-&mut results;
`transmute_copy` = a typed load). Reified fn pointers (`Cast FnPtr` + `Const FnDef`) are
tracked statically and `Dynamic` calls resolve to their targets, so the `aliasing_mut*`
family fails through genuine protected-seam collisions. Newly conformant: 13 fail tests
(aliasing_mut1-4, illegal_read8, illegal_write4, interior_mut2,
shared_rw_borrows_are_weak1, static_memory_modification, unescaped_local, exposed_only_ro,
illegal_read/write_despite_exposed1) + 2 pass scenarios (shr_and_raw, mut_below_shr).

---

## 2026-08-14 — Interior Mutability (UnsafeCell freeze masks, weak SRW protection)

Fourth same-day increment. Suite: **pass 47 | fail 0 | xfail 0 | xpass 0** — fail tests
**36/75** verdict-conformant (32 line-accurate), 11 pass scenarios, 63 unsupported.

Shared and raw-const retags now carry a type-derived per-cell **freeze mask**: cells inside
`UnsafeCell` get a SharedReadWrite item inserted above the granting item with no access;
the rest freeze. The mask is computed loader-side (`freezeMask` over `UTy`, which gained a
`cell` constructor) and carried on `RExpr.ref` — `obseq.LayoutTy` stays untouched.
Protection became **weak on SharedReadWrite** (popping/deallocating protected SRW is
allowed — verified by the `unsafe_cell_invalidate` pass scenario — while protected
Unique/frozen pops remain UB). `UnsafeCell`/`Cell` are opaque in charon output with
bodyless `new`/`get`: pointees are inferred from call sites, `new` is shimmed as identity,
`get` as a masked shared reborrow, `ptr::read` as a deref read; `Atomic*` maps to a
one-word cell. Pointer type-punning casts became tag-preserving reinterprets
(`RExpr.ptrCast`). Newly conformant: interior_mut1, illegal_read7,
mixed_mutability_static (all at miri's lines), plus cell_inside_struct and
unsafe_cell_invalidate on the pass side.

---

## 2026-08-14 — Enums (Option) and Heap Allocation/Deallocation (Box, std::alloc)

Third same-day increment. Suite: **pass 42 | fail 0 | xfail 0 | xpass 0** — fail tests
**33/75** verdict-conformant (29 line-accurate), 9 pass scenarios, 67 unsupported with
reasons. (Corrected progression: 21 → 25 → 33; earlier entries overstated by 2.)

**Semantics (obseq3):** `Stmt.alloc`/`Stmt.dealloc` (heap; `sb_dealloc` requires a live
writable tag at every cell, rejects any protected item in the stack, and removes the
borrow stacks — freed cells then fail with "no borrow stack"); `Stmt.assignIf` (an
assignment guarded on a runtime discriminant word — the variant-conditional retag
primitive); `AllocLen` (static or place-read allocation sizes).

**Loader:** type_decls parsing — monomorphized struct decls map to tuples, enum decls to
a discriminant word + prefix-merged payload cells, `Box` (opaque) to a mutable raw with
the pointee inferred from deref-projection use sites, `Layout` to its size word.
Enum-variant aggregates desugar to discriminant + payload writes. Seam copies of
enum-typed values retag payload refs under `assignIf` guards. Reference-typed values
loaded through a deref are retagged (Miri's load retag — what load_invalid_mut/shr test).
Name-based shims for `Box::new`, `std::alloc::{alloc,dealloc}`,
`Layout::from_size_align_unchecked`; `Drop` terminators lower to no-op gotos.

Newly conformant: illegal_dealloc1 (Miri's exact line and "deallocation … tag does not
exist" phrasing), illegal_write1, load_invalid_mut/shr, box_exclusive_violation1,
pass_invalid_shr_option (fails through the guarded enum retag at Miri's line),
return_invalid_{mut,shr}_option (verdict-only: call-site seam vs miri's `ret` line).
Box divergence noted: modeled as an implicit mutable raw, no Unique box retag.

---

## 2026-08-14 — Protectors and Statics Hoisting (zero conformance divergences)

Same-day follow-up to the conformance-suite entry below. Protectors landed as call-frame
protector sets in obseq3 (`AccessPerms.protFrames`; `pushProtectors`/`popProtectors`
pseudo-statements bracketing inlined calls; seam retags of reference-typed arguments —
including tuple fields — register their fresh tags as protected; read/write/die error when a
pop would remove a protected item). Statics hoisting landed loader-only (ULLBC `Global`
place roots rewritten to `uninit`-materialized locals; initializers not run). New
`RExpr.uninit`; 12 obseq3 unit tests.

Result: both protector xfails became line-accurate passes (Miri's exact lines and phrasing),
both statics tests promoted. Suite: **pass 34 | fail 0 | xfail 0 | xpass 0** — fail tests
25/75 verdict-conformant [corrected from 27/75; see notes correction 2026-08-14], and every test that loads agrees with Miri's
verdict. Remaining exclusions: interior mutability, deallocation, int-to-ptr, enums,
slices, threads, drop glue.

---

## 2026-08-14 — obseq3: Miri SB Conformance Suite (per-cell stacks, writable raws, Charon ingestion)

### Context

Goal: be able to call the SB semantics "conformant" by scoring it against Miri's test corpus
(fail tests must be flagged UB, pass tests must run clean). Audit found two v1/v2 divergences
from real SB that dominated feasibility (raws never writable; borrow stacks only at allocation
base addresses), and no executable tests on the SB-enforcing semantics at all. Full plan:
`plans/sb_conformance_obseq3.md`.

### What landed

- **`src/obseq3/`** — new versioned codebase (v1/v2 untouched, all proofs still green):
  per-cell borrow stacks (`sb_own` roots every cell; all ops range-based), mutability-carrying
  raw items (`RawPtr mutbl`: raw-mut ≈ SharedReadWrite — writable, survives reads; raw-const
  behaves like a shared item), `TwoPhase` reserved borrows, `Except String` errors with cell
  offsets, and a length-parameterized `PermissionModel`. Semantics forked from obseq2's mirlite
  with range-based access sites + implicit root allocation through projections.
  10 unit tests in `src/obseq3/tests.lean` (assert pattern + `expectErr`).
- **Faithful raw-retag placement**: raw-mut retags perform *no* parent access and insert the new
  item *directly above the granting item* (Miri's SharedReadWrite placement). This is what makes
  sibling raws coexist (`two_raw`) while `raw_tracking` still catches the invalidation — the
  earlier write-access-and-push-on-top draft was strictly stronger than Miri.
- **`src/conformance/`** — Charon ULLBC JSON → untyped AST → lowering (call inlining,
  linearization, storage/FakeRead dropping, tuple-aggregate desugaring, seam retags incl.
  composite tuple-field retags) → elaborator into the intrinsically-typed obseq3 syntax
  (`DecidableEq LayoutTy` + transport; no per-program proofs) → manifest-driven harness
  (`lake exe sb_conformance`). Charon emits no Retag statements — retags are synthesized at
  `Ref`/`RawPtr` rvalues (= the eager model) plus inline-seam retags.
- **`conformance/`** — pinned corpus (miri @ 34d6a795, 2026-08-13; charon nightly-2026.08.14),
  30 curated prep files, committed ULLBC artifacts, manifest with per-test
  status/reason/verdict/line.

### Score (miri @ 34d6a795)

- **fail tests: 21/75 verdict-conformant** [corrected from 23/75] (line-accurate on 19), 2 xfail-model
  (protector tests: our model silently pops protected items), 50 unsupported with
  per-test reasons.
- **pass scenarios: 9 clean** (incl. two_raw, mut_raw_mut, partially_invalidate_mut,
  disable-SRW-merge behaviors), rest unsupported with reasons.
- Suite: `pass 30 | fail 0 | xfail 2 | xpass 0 | unsupported 77 | total 109`; missed UB is
  always a hard failure; Miri message *text* is never matched (structural verdict + line only).

### Exclusions (documented per-test in conformance/manifest.json)

Protectors, interior mutability (UnsafeCell/Cell), deallocation/Box, int-to-ptr exposure,
transmute, enums/control flow, arrays/slices, threads, statics. These are Phase C in the plan.

---

## 2026-06-17 — Closing the `const_write` Sorry: Reconstruct-not-Port and the Identity-on-Domain Rename Invariant

### Context

`compile_correct` and its single-step driver `CompilerInv_step` are fully proved. The remaining
gaps are the three per-instruction simulation lemmas they delegate to:
`CompilerInv_step_constWrite` (via `const_write_resolved_simulation`), `CompilerInv_step_copy`,
and `CompilerInv_step_ref`. This entry records the design decisions made while planning the first
of these, the constant-write case. A v1 (`obseq`) analog — `existing_write_simulation` in
`src/obseq/proof/state_helpers.lean` — exists and is fully proved, which raised the question of
whether to port it or reconstruct natively.

### Decision 1: Reconstruct from v2, do not port v1

The v2 proof should be reconstructed against v2's own primitives; v1's `existing_write_simulation`
is a *phase-structure reference only*, not code to port. The reason is principled rather than
stylistic: v1's lemma is dominated by exactly the machinery v2 was designed to delete.

| Concern | v1 (`existing_write_simulation`) | v2 (reconstruct) |
|---|---|---|
| Fragment placement | `StartsAt` list slices, offset case-splits with literal instr lists | code-map `simp` + `compileProgFrom_code_eq_compileStmt` |
| State monotonicity | `*_state_incr` lemma family | `CompilerM.incr` (StateIncr in the monad) |
| Type consistency | explicit `PlaceMap π`, `baseLayout`/`subLayout`, `ptr_sim` | free (intrinsic typing `Place Γ τ`) |
| Invariant | `StateSim π ρa ρt … ptr_sim` + separate `TargetNonInterference` | single `CompilerInv` |
| Execution | `StepStarWith` (transitive closure) | indexed `runN n` + `oseair_runN_add` |
| Pointer-in-register | `place_runtime_sim` hypothesis | `PlaceRegReady` (packages the `useMut` witness) |

A line-by-line port would re-introduce v1 scaffolding (separate type tracking, list-slice
placement, per-function state-incr lemmas, `StepStar`, the two-part invariant) and then fight every
v2 abstraction to map it back. What actually transfers is the small *seven-step skeleton* (invert
MIR write → run fragment → transport SB → memory sim → preserve freshness → reconstruct invariant →
extend ρ), which is already encoded in `common.lean`'s factoring.

### Decision 2: Add an identity-on-domain rename conjunct, justified by lockstep bump allocators

This is the pivotal decision. `CompilerInv` carries `s_osea.ap = s_mir.perms` as **verbatim
equality**, yet `PlaceRegReady` demands `useMut s_osea.ap (b' + off) t' = some ap2` at the
**renamed** target address `b' = ρa(allocBase)`, while the source write consumed `useMut` at the
**un-renamed** source address `resolved.addr`. These reconcile only if ρa is the identity on live
addresses and ρt on live tags. Nothing in the invariant asserted this, even though it is true: the
source and target run **identical lockstep bump allocators** —

```
-- src/obseq2/mirlite_semantics.lean
def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  let base := m.addrStart
  (base, { m with addrStart := base + sz })

-- src/obseq2/oseair.lean
def allocate (m : Mem) (sz : Nat) : Word × Mem :=
  (m.addrStart, { m with addrStart := m.addrStart + sz })
```

so both sides hand out the same `addrStart` in the same order, and the address/tag namespaces
coincide. We make this explicit by adding two conjuncts to `CompilerInv`:

```lean
def IdentityOnDomain {α : Type} (ρ : α → Option α) : Prop :=
  ∀ a a', ρ a = some a' → a = a'

-- CompilerInv now ends with:
--   … ∧ s_osea.ap = s_mir.perms
--   ∧ PermissionModel.stackedBorrows.WellFormed s_mir.perms
--   ∧ IdentityOnDomain ρa ∧ IdentityOnDomain ρt
```

Consequence: in `writeThroughPtr_sim`, permission transport becomes the source `useMut` verbatim
(via `s_osea.ap = s_mir.perms` + identity), the bounds check is literally the source bound
(`b' + off = allocBase + off = resolved.addr`), and memory simulation is `MemValSim (word v)
(Dat v)`. No renaming-invariance lemmas are needed in `permission.lean`.

**Alternatives rejected.** (a) Generalize `s_osea.ap = s_mir.perms` to a renamed relation
`PermSim ρa ρt s_mir.perms s_osea.ap` and prove `useMut`/`sb_use_mb` renaming-invariance lemmas —
more faithful to CompCert's `inject` model, but heavier and it touches the permission layer.
(b) Leave the invariant unchanged and derive `ρa a = a` on the fly inside the write lemma —
risk: the equality is not derivable without a global identity fact, so it would surface as a stuck
goal.

**Preservation obligation.** The conjunct must survive `AddrRenameIncr`/`TagRenameIncr`. Regime-B
fresh allocation (below) extends ρa/ρt with *identity* entries (`newAddr ↦ newAddr`), so it stays
identity-on-domain; a small preservation lemma is owed when that code lands. This is a *semantic*
invariant, categorically different from the code-placement/slice conjunct that was deliberately
kept out (see the 2026-04-28 entry on why `CompilerInv` stays lean).

### Decision 3: Split `const_write_resolved_simulation` by regime

The single lemma was quietly covering two regimes admitted by its `h_prep`/`h_res` hypotheses:

- **Regime A — existing write:** `resolvePlace? s_mir dst = some _`, so `preparePlaceAssign` was a
  no-op (`s_pre = s_mir`); ρ unchanged. The direct analog of v1's `existing_write_simulation`.
- **Regime B — fresh local:** resolves only after prepare (only reachable for `.local loc`;
  proj/deref error in `preparePlaceAssign`). `allocateBase` ran, so ρa/ρt must **extend** — this is
  where the rename maps do real work and the identity-extension preservation lemma is needed.

Keep `const_write_resolved_simulation` for A; add `const_write_fresh_local_simulation` for B;
dispatch in `CompilerInv_step_constWrite` by casing on `resolvePlace? s_mir dst`.

### The native-v2 regime-A skeleton (five phases)

1. **Locate** the fragment via `compileProgFrom_code_eq_compileStmt` + `targetLabelAt` (replaces
   v1's `StartsAt` list slicing).
2. **Run the place fragment** (`placeToRegChecked_run_sim`, shared with copy/ref) → `PlaceRegReady`;
   empty for the already-mapped-local case.
3. **CStore** via `runN_CStore_step` + `writeThroughPtr_sim`.
4. **Cleanup `Die`s** via `runN_cleanupInstrs` (none for local).
5. **Reconstruct** the invariant, composing runs with `oseair_runN_add`.

### Decision 4: `runN_cleanupInstrs` is conditional, not unconditional

The original commented stub claimed the `Die` sequence *succeeds* unconditionally. That is false:
each `Die` calls `sb_die`, which can fail. The lemma was reformulated as **"if the run completes,
it preserves memory and registers and advances the pc by the cleanup length"**; run completion
(the per-`Die` `sb_die` success, i.e. the deferred ap-coherence) stays the caller's obligation,
where the borrow facts are available. `runN_CStore_step` and the locator carry no such caveat.

### Scoping note

Not all "mechanical helpers" are on the const-write critical path. `runN_cleanupInstrs` is **not**
needed for writes to a local: the `assignLocal` branch of `compileStmtChecked` emits no
`cleanupInstrs`, and `ensureLocalRegE` returns `cleanup := []` for both existing and fresh locals,
so **both** local regimes have zero `Die`s. Cleanup is only needed for proj/deref `dst`. The
recommended first milestone is therefore regime-A already-mapped-local (`n = 1`, fragment is just
`[CStore …]`), which exercises the full reconstruction with the least scaffolding.

### Status

- Step 1 (landed): `IdentityOnDomain` predicate + the two `CompilerInv` conjuncts; the two
  destructure sites in `const_write.lean` updated. `lake build` green; only the three expected
  sorries remain.
- Step 2 (landed): mechanical execution helpers in `common.lean` —
  `compileStmt_emitted_in_compProg` (locator wrapper), `runN_CStore_step`, `step_Die_preserves_reg`,
  `runN_allDie_preserves`, `runN_cleanupInstrs`. All proved; shared with copy/ref.
- Next: `writeThroughPtr_sim` (now tractable under the identity conjunct), then the regime-A
  already-mapped-local milestone.

---

## 2026-04-30 — CompCert Memory Model and Non-Interference

### Context

The question arose whether adopting a CompCert-style `Block × Z` address space (opaque block IDs
rather than flat `Word` addresses) would simplify non-interference proofs — particularly the
simulation invariant for `placeToReg`.

### What CompCert Does

CompCert represents memory addresses as `(b : Block) × (ofs : Z)` where `Block` is a globally
unique allocation ID. Each call to `Mem.alloc` returns a fresh block strictly greater than all
existing ones. The key consequence is `Mem.load_store_other`:

```
b1 ≠ b2 → Mem.load chunk m b1 ofs = Mem.load chunk (Mem.store chunk m b2 ofs' v) b1 ofs
```

Two distinct blocks are *definitionally* disjoint — the memory map is a function over `Block` and
stores to `b2` literally do not affect the map at `b1`. Cross-allocation non-interference reduces
to `b1 ≠ b2`, which follows immediately from the allocator's freshness guarantee.

CompCert does not use a rename map for addresses between passes. Most passes use `inject_id` (the
identity injection), so source addresses and target addresses are literally the same `Block × Z`
values. No ρa equivalent is needed because the shared address namespace is preserved through
compilation.

### What It Would Help in obseq2

The main place flat arithmetic hurts currently is in `placeToReg_emits_no_mem_effects` and
`placeToReg_mem_preserved` — specifically showing that a newly allocated local (from `ensureLocalReg`
→ `Rhs.Alloc`) does not overlap with any binding already in `Env`. With a block model this reduces
to `newBlock ≠ existingBlock`, which follows directly from the allocator's freshness postcondition.
With flat addresses the `AllocatorProofSpec.alloc_fresh` field must carry explicit arithmetic facts
about `addrStart + i` not appearing in any prior `mMap` entry.

### What It Would Not Help

The harder non-interference obligation is intra-allocation aliasing: that `placeToReg` for `deref`
and `proj` emits `BorOffset`/`MutBorOffset`/`Load` instructions that do not conflict with the
destination's `useMut` permission check. This is entirely a stacked-borrows concern — `Block × Z`
addresses are orthogonal to `AccessPerms`. The permission model reasons per-address within a block,
and block separation does not rule out aliasing within a single allocation.

The real bottleneck is the stacked-borrows frame lemma: "if I hold permission `tag` at address `a`,
and `sb_ref`/`sb_read` fires at a *different* address `a'`, my permission at `a` is unaffected."
That lemma lives in `sb.lean` and has no dependency on flat vs. block addresses.

### Why the Migration Is Not Worth It Now

- `oseair.Val.Ptr` uses `(base offset size tag : Word)` — migrating to `(block : BlockId) (offset size : Word) (tag : Tag)` would require changing every pattern match.
- `sb.lean` uses flat `Word` addresses throughout `AccessPerms` and all `sb_*` operations.
  Refactoring it to `BlockId × Z` is a large surface-area change with no payoff on the central proof gap.
- The current `AllocatorProofSpec` serves the same purpose as block freshness — it just requires
  explicit arithmetic reasoning rather than deriving it from disjoint block IDs.

### Verdict

A block-based model would remove one tedious arithmetic side condition (cross-allocation freshness),
but would not touch the central difficulty (stacked-borrows frame lemmas for intra-allocation
aliasing). Migration cost is high; benefit is narrow. The pragmatic path is to keep flat addresses,
treat `AllocatorProofSpec.alloc_fresh` as the block-separation axiom, and focus proof effort on the
stacked-borrows frame lemmas that are the actual bottleneck.

---

## 2026-04-30 — Fragment Installation: Labels vs Runtime PCs

### Problem

Proof obligations such as the `placeToReg` slice in `const_init.lean` originally mixed two
different facts in one goal:

```lean
compileProgFrom cs0 prog (s_osea.pc + i) =
  dstCS.code (cs_cur.nextLabel + i)
```

The left side starts from the runtime machine PC, while the right side is indexed by compile-time
labels allocated in `CompilerState`. This works for straight-line code, but it hides the important
distinction between code layout and control-flow reachability.

### Decision: Split the Facts

Use a compile-time label predicate for code layout:

```lean
def FragmentInstalledAtLabel (m : CompilerM α) (cs : CompilerState)
    (baseLabel : Nat) (prog : oseair.Prog) : Prop := ...
```

This says: the fragment emitted by `m` from compiler state `cs` appears in `prog` starting at
compile-time label `baseLabel`. It deliberately does not mention runtime PC.

Keep the execution-facing predicate separate:

```lean
def FragInstalled (m : CompilerM α) (cs : CompilerState)
    (s : oseair.State) (prog : oseair.Prog) : Prop := ...
```

This says: the same fragment is installed at the current runtime PC, so an execution lemma such as
`placeToReg_correct` can run it with `runN`.

The bridge is explicit:

```lean
s.pc = baseLabel →
FragmentInstalledAtLabel m cs baseLabel prog →
FragInstalled m cs s prog
```

### Branching Implication

When branches are added, `FragmentInstalledAtLabel` should remain a pure compile-time layout fact.
What changes is the runtime control proof that establishes `s.pc = baseLabel`. In straight-line
code this comes from prefix compilation (`targetPcAt`); with branches it should come from a CFG or
label-map invariant saying that execution has reached the relevant source point's target label.

Naming rule: use `label` / `baseLabel` / `nextLabel` for compile-time code positions. Reserve `pc`
for runtime machine state.

---

## 2026-04-30 — CompCert-Style `StateIncr` Compiler Monad

### Problem

The 2026-04-28 code-map refactor fixed the representation problem (`Prog = Nat → Option Instr`),
but it left a large proof-engineering burden in `proof/common.lean`: every compiler function that
threaded `CompilerState` needed paired monotonicity lemmas such as:

- `placeToReg_state_incr`
- `placeToBorrowReg_state_incr`
- `compileRExprTo_state_incr`
- `compileStmt_state_incr`
- fold-level state-growth lemmas

Those lemmas all proved the same structural fact: compiler actions only extend the generated code
and fresh counters; they do not rewrite previously allocated target-code labels.

### CompCert Analogy

CompCert's RTL generator does not separately re-prove this after every compiler function. Its
code-generation monad carries a `state_incr` proof in the result type. `bind` composes those proofs
with `state_incr_trans`, so monotonicity is a construction invariant of the compiler, not a family
of after-the-fact lemmas.

### Decision: Add `CompilerM`

`src/obseq2/compile.lean` now defines the compiler-state growth relation directly:

```lean
structure StateIncr (s1 s2 : CompilerState) : Prop where
  nextLabel_le : s1.nextLabel ≤ s2.nextLabel
  nextReg_le   : s1.nextReg ≤ s2.nextReg
  code_eq      : ∀ label, label < s1.nextLabel → s2.code label = s1.code label
```

The `label` argument is deliberately not called `pc`: this is a compile-time target-code slot.
Runtime states later use natural-number PCs to index the same code map, but `StateIncr` is about
compiler state transitions.

The new compiler monad is:

```lean
abbrev CompilerM (α : Type) : Type :=
  (cs : CompilerState) → α × { cs' : CompilerState // StateIncr cs cs' }
```

`pure` returns the same state with `StateIncr.refl`. `bind` runs the first computation, then the
second from the intermediate state, and composes their witnesses with `StateIncr.trans`.

### Compiler Refactor

The compiler functions now produce monadic computations:

| Old shape | New shape |
|-----------|-----------|
| `placeToReg cs kind p : PtrResult` with `PtrResult.cs` | `placeToReg kind p : CompilerM PtrResult` |
| `placeToBorrowReg cs kind p : PtrResult` | `placeToBorrowReg kind p : CompilerM PtrResult` |
| `compileRExprTo cs dst expr : CompilerState` | `compileRExprTo dst expr : CompilerM Unit` |
| `compileStmt cs stmt : CompilerState` | `compileStmt stmt : CompilerM Unit` |
| `List.foldl compileStmt cs prog` | `CompilerM.run (compileStmts prog) cs` |

`PtrResult` and `RExprResult` no longer contain a `cs` field. Intermediate compiler states are
obtained explicitly with:

```lean
CompilerM.run m cs
```

and emitted result values with:

```lean
CompilerM.value m cs
```

The primitive operations are now:

- `emitM : List Instr → CompilerM Unit`
- `freshRegM : CompilerM Register`

Both carry their `StateIncr` proof at construction time.

### Proof Effects

The repeated per-function state-growth lemmas were removed from `src/obseq2/proof/common.lean`.
When a proof needs state monotonicity, it now uses:

```lean
CompilerM.incr computation initialState
```

For example, suffix compilation preservation in `compileProgFrom_code_eq_compileStmt` now gets the
"later statements do not overwrite this statement's emitted code" fact directly from the monadic
state witness:

```lean
(CompilerM.incr (compileStmts suffix) stmtState).code_eq label h_label
```

The code-map preservation lemmas `emit_code_lt_nextLabel` and `emit_nextLabel_ge` moved into
`compile.lean`, because they are foundational facts used by `emitM` itself rather than
proof-only infrastructure.

### Impact on `const_init.lean`

The previous `const_init` proof script was written against the old `.cs` field:

```lean
let dstRes := placeToReg cs_cur .Mut dst
dstRes.cs
```

After the monadic refactor the same proof strategy is expressed with explicit monadic state
extraction:

```lean
let dstM := placeToReg RefKind.Mut dst
let dstRes := CompilerM.value dstM cs_cur
let dstCS := CompilerM.run dstM cs_cur
let h_place_incr := CompilerM.incr dstM cs_cur
```

The old proof body was temporarily too stale to typecheck after the API break. The file now keeps
the original phase structure as a monadic skeleton:

1. prove the `placeToReg` slice in the full compiled program,
2. run `placeToReg_correct`,
3. identify and run the emitted `CStore`,
4. identify and run cleanup `Die`s,
5. reconstruct `CompilerInv`.

The detailed slot-identification proofs remain as localized `sorry`s, but the proof strategy is
preserved instead of being collapsed into a single opaque placeholder.

### Current Status

`lake build` passes with the existing proof scaffolding. The refactor reduces the long-term proof
burden: adding new compiler functions should require constructing `CompilerM` computations from
`emitM`, `freshRegM`, and other monadic compilers, rather than adding a new family of
`*_state_incr` lemmas.

---

## 2026-04-28 — Code Map Representation for OSEA-IR (`Prog = Nat → Option Instr`)

### The Problem

`const_init.lean` contains a sorry that cannot be closed without a new structural lemma:

```lean
have h_slice : ∀ (i : Fin fragLen),
    (compileProgFrom cs0 prog).get? (s_osea.pc + i.1) = some (fragInstrs.get i) := by
  sorry
```

The claim is that the instructions emitted by `placeToReg cs_cur .Mut dst` appear at position
`targetPcAt cs0 prog s_mir.pc` in `compileProgFrom cs0 prog`. Proving it requires reasoning about
`List.foldl compileStmt` and how each `emit` appends to the growing instruction buffer — a
structural fact (`compileStmt_instrs_prefix`) not currently in `common.lean`. The same pattern
recurs for `h_cstore_instr` and `h_die_instrs` in the same proof, and will repeat for the copy
and ref cases.

### How CompCert Avoids This

CompCert uses a `PTree.t instruction` (a partial map from node IDs to instructions) in its RTL
pass rather than a flat `List Instr`. Compilation writes each instruction directly to a specific
code position at emit time. The simulation relation's "current instruction" conjunct is then a
direct map lookup — `fn_code ! pc = Some instr` — not a derived fact about list structure.

### Decision: `Prog = Nat → Option Instr`, `CompilerState` uses a label allocator

**`oseair.Prog`** changes from `List Instr` to `Nat → Option Instr` — a partial function from
target PC to instruction.

**`CompilerState`** replaces `instrs : List Instr` with two fields:

```lean
structure CompilerState where
  nextReg   : Nat                 -- fresh register allocator (unchanged)
  nextLabel : Nat                 -- fresh code-position allocator
  code      : Nat → Option Instr  -- sparse map; only emitted slots are Some
```

`nextLabel` is the code-position analog of `nextReg`: it is a compile-time counter, not a runtime
construct. The name is deliberately distinct from "PC" to avoid conflating compilation order with
runtime control flow. When branches are added to oseair, `freshLabel` will allocate a slot before
its instruction is known (forward references), and `setInstr` will fill it in later — exactly the
backpatching pattern that is impossible with an append-only `List Instr`.

**`emit`** writes a batch of sequential instructions starting at `nextLabel`:

```lean
def emit (cs : CompilerState) (instrs : List Instr) : CompilerState :=
  { cs with
    nextLabel := cs.nextLabel + instrs.length,
    code      := fun pc =>
      if h : cs.nextLabel ≤ pc ∧ pc < cs.nextLabel + instrs.length
      then instrs.get? (pc - cs.nextLabel)
      else cs.code pc }
```

The slice condition `h_slice` then holds by `simp` from the `emit` definition — the instructions
are in the map by construction. `h_cstore_instr` and `h_die_instrs` close the same way.

### Why Not Just Add the Structural Lemma?

For the current straight-line IR a single `compileStmt_instrs_prefix` lemma would also close the
sorry. The code-map refactor is chosen instead because:

1. **Branches are planned.** A flat `List Instr` cannot express forward branch targets without a
   second pass. When oseair gains `Jump`/`Branch` instructions, the flat-list compiler must be
   rewritten regardless. Doing it now avoids the refactor twice.
2. **All three slice sorries disappear at once.** The lemma approach closes `h_slice` but still
   leaves `h_cstore_instr` and `h_die_instrs` as separate sorries requiring additional argument.
3. **`CompilerInv` stays at 7 conjuncts.** The 8th-conjunct approach (adding the slice fact to the
   invariant) would close the sorry but grows the invariant for every future case.

### Files Changed

| File | Change |
|------|--------|
| `src/obseq2/oseair.lean` | `abbrev Prog := Nat → Option Instr`; `stepWith` uses `prog state.pc` |
| `src/obseq2/compile.lean` | `CompilerState`: drop `instrs`, add `nextLabel` + `code`; rewrite `emit`, `freshReg`, `initLocals`, `compileProg` |
| `src/obseq2/proof/common.lean` | `CompilerStateWF`, `compileProgFrom`, `targetPcAt` updated; `h_slice` pattern closes by `simp` |
| `src/obseq2/proof/const_init.lean` | `h_slice`, `h_cstore_instr`, `h_die_instrs` sorries removed |

### Implementation Note

The refactor is now implemented. The proof-side placement argument is not a list-slice lemma
anymore; it is factored through code-map preservation lemmas:

- `emit_code_lt_nextLabel`: emitting at `nextLabel` preserves all earlier labels.
- `compileStmt_code_lt_nextLabel` and `foldl_compileStmt_code_lt_nextLabel`: compiling later
  statements cannot overwrite code below their starting label.
- `compileProgFrom_code_eq_compileStmt`: if `prog.get? pc = some stmt`, then the whole compiled
  program agrees with the code produced by compiling `stmt` from `csAt cs0 prog pc`, for every
  label before that statement's resulting `nextLabel`.

`const_init.lean` uses those facts to close the old `h_slice`, `h_cstore_instr`, and
`h_die_instrs` obligations without adding new sorries. The remaining sorries in that file are the
pre-existing semantic simulation obligations unrelated to emit placement.

---

## 2026-04-25 — Bounds Semantics, Typed OSEA-IR, and Proof Infrastructure Direction

### Should OSEA-IR be typed like MIRLite?

Considered making OSEA-IR intrinsically typed (dependent type indices on `Instr`, like MIRLite's
`RExpr Γ τ`). Decided against full typed IR. The right approach is a **proof-side WF layer** over
the flat IR:

- `RegValWF ty vals` — values have the right shape for the type
- `RegMapWF regTypes reg` — every live register matches its expected type
- `InstrWF regTypes instr regTypes'` — instruction-level typing relation tracking register effects
- `CompiledWF Γ cs` — compiled code is well-formed

This keeps OSEA-IR operationally simple while giving proofs the same benefit as typing: impossible
bad states are ruled out once by WF lemmas, not reproved at every step. Full typed OSEA-IR would
only pay off if type preservation were a stated goal; for behavioral simulation it is unnecessary.

### Two target semantics bugs fixed

**Bug 1: `RStore`/`CStore` ignoring their `ty` field**

Both instructions carried a `ty : TyVal` parameter but matched it with `_ty`, ignoring it. Fixed:
- `RStore ty src ptr` now checks `srcTy == ty` (source register type must match declared type)
- `CStore ty vals ptr` now checks `vals.length == typeSize ty`

These were invisible in obseq1 proofs because `step_RStore`/`step_CStore` take `ty` and `srcTy` as
independent unconstrained variables — no hypothesis requiring `srcTy = ty`. The proof went through
regardless, mirroring the bug.

**Bug 2: `writeThroughPtr` bounds check — matching MIRLite**

Original check: `addr >= base + size` (start-of-write only).

This was initially changed to `addr + vals.length > base + size` (end-of-write), then reverted,
then restored after understanding the full picture.

**Why it was invisible in obseq1:** All compiled `CStore`/`RStore` use freshly allocated pointers
at offset 0. With `offset = 0`, the check `addr >= addr + blockSize layout` is trivially false for
any non-empty type — it fires for no values of `vals`. The `vals` parameter was never constrained
to `vals.length = blockSize layout` because no proof obligation required it.

### Stacked borrows does not subsume bounds checking

Stacked borrows is a **per-address permission model**. It answers "does tag T have permission to
access address A?" — not "is address A within allocation B?" These are orthogonal:

| | Bounds check | Stacked borrows |
|---|---|---|
| Catches | write past end of allocation | write without valid permission |
| OOB into another live allocation | YES | NO (passes if tag valid there) |
| In-bounds write after borrow expired | NO | YES |

Relying on stacked borrows alone to catch OOB is incorrect.

### Correct bounds semantics added to MIRLite

`writeResolvedPlace` had no bounds check — only `M.useMut`. This is correct for the current typed
fragment (type system guarantees `Place.offset + blockSize τ ≤ blockSize σ`), but wrong for future
raw pointer arithmetic where offsets can be arbitrary.

Changes made in `src/obseq2/mirlite_semantics.lean`:
- `PlaceRes` gains `allocBase : Word` and `allocSize : Word`
- `resolveDirectPlace?` populates them from `Place.baseLocal` and `blockSize`
- `writeResolvedPlace` now checks `dst.addr + values.length > dst.allocBase + dst.allocSize`
  before the permission check

Changes made in `src/obseq2/oseair.lean`:
- `writeThroughPtr` checks `addr + vals.length > base + size`
- `RStore`/`CStore` now validate their `ty` field at runtime

Both sides now use the same bounds predicate: the entire write range must fit within the allocation.
For well-typed programs, `PathTo` structure guarantees this statically and the check never fires.
For future raw pointer arithmetic, both sides error on the same condition, preserving simulation.

### WF layer is the next step

Proof order going forward:
1. Target WF predicates (`RegValWF`, `InstrWF`, `CompiledWF`)
2. Step lemmas using WF as preconditions
3. Symbolic execution automation

`CompiledWF` will discharge the end-of-write obligation statically: for every `RStore`/`CStore`
emitted by the compiler, prove `vals.length = typeSize ty` and `offset + typeSize ty ≤ allocSize`.
This is derived from MIRLite's `PathTo` type structure — it is a static obligation, not a runtime
one.

---

## 2026-04-22 — Initial obseq2 Design Notes

### Why obseq2 Uses Types (vs obseq)

obseq tracks types *separately* from the IR, in compiler state (`PlaceMap`). A `Place` is just
`base : Word` + `path : List Word` (raw offsets). A `RExpr` carries no type information.
Correctness proofs must explicitly show that the compiler's type tracking is consistent with
runtime behavior — the bulk of the ~17k line proof burden.

obseq2 bakes types into the IR as dependent type indices. `RExpr Γ τ` is indexed by its result
type at compile time. `ref` always produces `RExpr Γ (PtrL τ)` — Lean's type checker enforces
this, not a proof. This eliminates the "type soundness" portion of the correctness proof: ill-typed
programs are simply unrepresentable.

What still needs proof in obseq2: memory/register correspondence, permission semantics preservation.
The `CompilerInv` scaffolding in `src/obseq2/proof/compiler.lean` sets this up.

### What `Ctx` Is

`Ctx := List LayoutTy` is the type signature of the local variable slot array. `Γ[i]` is the
layout type of local variable `i`. It does not accumulate all types seen in the program — expression
result types (e.g. `PtrL τ` from a `ref`) do not need to appear in `Γ`. Intermediate struct field
types in `PathTo` are also not in `Γ`.

`Γ` is fixed for the whole `Prog Γ`. In a real pipeline you'd need an elaboration pass over the
source that collects all local variable declarations, assigns each an index, and produces a
`Σ Γ : Ctx, Prog Γ`.

### `Place Γ τ` — What It Means

```lean
inductive Place (Γ : Ctx) : LayoutTy → Type where
| local : Local Γ τ → Place Γ τ
| proj  : Place Γ σ → PathTo σ τ → Place Γ τ
```

A type family: `Γ` is a fixed parameter, `LayoutTy` is an index that varies per value.
`Place Γ τ` is "a place in program `Γ` whose content has layout type `τ`".

- `local`: a bare local variable. `Local Γ τ` is an index `i : Fin Γ.length` with proof
  `Γ[i] = τ`. The layout type is statically known.
- `proj`: field projection. Navigates from a base place of type `σ` through a `PathTo σ τ`
  to reach a sub-place of type `τ`.

The type `τ` is a static guarantee — you cannot construct a `Place Γ NatL` that actually
points to a `PtrL` slot.

### `PathTo src dst` — Type-Indexed Field Paths

```lean
inductive PathTo : LayoutTy → LayoutTy → Type where
| nil : PathTo τ τ
| field {tys : List LayoutTy} (idx : Fin tys.length) :
    PathTo (tys.get idx) τ → PathTo (obseq.LayoutTy.TupL tys) τ
```

`PathTo src dst` is a sequence of field projections that navigates from layout type `src` down
to a sub-layout of type `dst`.

- `nil`: the empty path — source and destination are the same type.
- `field idx tail`: pick field `idx` from a tuple `TupL tys`. The field's type is `tys.get idx`,
  and `tail : PathTo (tys.get idx) τ` continues to `dst`.

Example: given `TupL [NatL, TupL [NatL, PtrL NatL]]`, the path to the inner `PtrL NatL`:
```lean
field ⟨1, _⟩ (field ⟨1, _⟩ nil)
-- type: PathTo (TupL [NatL, TupL [NatL, PtrL NatL]]) (PtrL NatL)
```

Two guarantees from the types:
- **Out-of-bounds impossible** — `idx : Fin tys.length` is bounded by the tuple length at compile time.
- **Type mismatch impossible** — `PathTo (TupL [NatL, NatL]) (PtrL NatL)` is uninhabited;
  you cannot construct a path claiming to reach a type that isn't there.

In obseq the equivalent was `path : List Word` — raw offsets with no bounds or type guarantees.

### Three Styles for Pointer Values in Memory

The `MemValue.placeTag` constructor in `mirlite_semantics.lean` stores the pointer value.
Three designs worth comparing:

**Current: symbolic typed place**
```lean
| placeTag {τ : LayoutTy} (place : Place Γ τ) (tag : Tag)
```
Stores the whole symbolic place — "pointer to local #3, field path [1]". Re-resolves the place
at each deref rather than reading a stored address.

Cost: `Γ` propagates into `MemValue → Mem → State` everywhere. The type safety is not
fully constructive — the `if τ' == τ` check at deref is still a runtime check.

Benefit: `MemValSim` in the proof can relate pointer values to source locals by index without
a separate heap correspondence invariant.

**Alternative: type + resolved address**
```lean
(τ : LayoutTy) × Word × Tag
```
No `Γ` anywhere. Cleaner types throughout. The `if τ' == τ` check is still there —
behaviorally identical to current. For proofs you'd need an explicit heap correspondence predicate
"address `w` was allocated for source local `i`", which is essentially what `MemValSim` contains
anyway. The work moves rather than disappears.

**Untyped (obseq style): raw word**
```lean
Word × Tag
```
No type anywhere. Simulation proof must track types externally — this is the path to 17k lines.

**Verdict:** The current design is shaped by proof convenience more than operational clarity.
Storing symbolic places lets the simulation invariant be stated without a separate heap
correspondence predicate, but it pays a real cost (propagating `Γ` into `State`) for a benefit
that is partly illusory (the runtime type check remains). Type + address would be cleaner
operationally with comparable proof overhead.

### Why `State` Carries `Γ`

`State (M : PermissionModel) (Γ : Ctx)` needs `Γ` for one reason: `MemValue.placeTag` stores
`Place Γ τ`, which contains a `Local Γ τ`, which is an index `Fin Γ.length` into the context.
To make that index well-typed, `MemValue` must be parameterized by `Γ`, which propagates up
through `Mem Γ` to `State`.

`Env Γ := Fin Γ.length → Option Binding` also mentions `Γ`, but only uses `Γ.length` — it
could equivalently be a bounded array. The `Γ` in `Env` is a consequence of indexing by
`Local Γ τ`, not an independent reason.

### What Is Standard vs. Novel in This Design

**Standard / textbook:**
- `Ctx` as a list, `Local` as a de Bruijn index with a type proof. Standard intrinsically-typed
  representation used throughout Lean/Agda mechanization literature (e.g. PLFA, Allais et al.
  "A Type and Scope Safe Universe of Syntaxes with Binding").
- Environment-store split. `Env` maps variable IDs to locations; `Mem` maps locations to values.
  Standard two-level memory model from operational semantics textbooks.
- Overall simulation proof structure. Rename maps `ρa`/`ρt`, pointwise memory simulation
  (`MemValSim`), top-level invariant (`CompilerInv`) follow the CompCert (Leroy) proof
  architecture: forward simulation with a lock-step invariant.

**Specific to this design:**
- `Place` as a recursive tree of projections, not a flat (base, offset) list. Allows structural
  induction on places in proofs and defers offset arithmetic to `Place.offset`/`PathTo.offset`.
- `MemValue.placeTag` — storing pointers symbolically as `Place Γ τ` rather than a resolved
  address. Lets `MemValSim` relate pointer cells to source locals by index without a separate
  heap-shape invariant, but propagates `Γ` into `MemValue → Mem → State` and leaves a runtime
  type check at deref.
- Lazy local allocation. `Env` returns `none` until the first direct assignment to a base local.
  Most source semantics allocate all locals upfront. The lazy design matches the target's
  `initLocals` behavior but makes the source semantics slightly unusual.
- Permission model abstracted as a typeclass `PermissionModel`. Source semantics parameterized
  over an arbitrary permission model rather than committing to stacked borrows directly.
  `CompilerInv` specializes to `PermissionModel.stackedBorrows`. Shaped by the goal of keeping
  source semantics reusable across permission models.
