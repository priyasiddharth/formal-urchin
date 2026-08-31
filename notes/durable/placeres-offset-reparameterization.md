# [FACT] Reparameterizing PlaceRes by offset: sound, verified, and too late

Date: 2026-08-31
Tags: obseq3, mirlite, representation, refactor, attempted

## the proposal

Carry `offset` in `mirlite.PlaceRes` instead of the absolute `addr`,
deriving `addr := allocBase + offset` — so that mirlite and oseair share
one representation and the simulation's pointer-offset conjunct holds on
the nose. See durable/resolved-address-vs-pointer-offset.md for why the
two forms differ.

## [FACT] it is sound, and behaviour-preserving — VERIFIED

The invariant `addr = allocBase + Σoffsets` holds in ALL constructors,
so the reparameterization is faithful:

| `resolvePlaceAcc` arm | offset |
|---|---|
| `.local` | `0` |
| `.proj` | accumulates `PathTo.offset path` |
| `.deref` | the loaded pointer's OWN offset, with `allocBase := its base` |

There is no other `PlaceRes` constructor (`resolvePlace?` mirrors the
same three arms). The semantics change alone was made and **built
clean, with the corpus unchanged: 17/17 + 99/99, identical verdicts**.
The patch is kept at `notes/attic/placeres-offset-reparameterization.patch`.

It also makes one bounds disjunct provably dead:
`ptrRes.addr < ptrRes.allocBase` (`mirlite_semantics.lean:171`) is
unreachable once `addr = allocBase + offset` with `offset : Nat`.

## [FACT] why it was reverted: ASSOCIATIVITY, not the literals

The cost estimate given before starting was "35 `PlaceRes` literals plus
fallout". The literals were real and mechanical — 28 of them, rewritten
by script in one pass, `offset` being `0` or the visible `+ k`.

What the estimate MISSED is that deriving `addr` changes the
ASSOCIATIVITY of every projected address:

```
old:  { res with addr   := res.addr   + k }.addr  =  (allocBase + offset) + k
new:  { res with offset := res.offset + k }.addr  =   allocBase + (offset + k)
```

Every proof that speaks of `resolved.addr + pathOffset path` — in
`sb_ref`/`sb_write` arguments, `show` statements, `rw` patterns and
`simpa` targets — therefore stops matching. That is ~50 sites spread
across `const_write.lean`, `copy.lean` and `ref.lean`.

A bridging simp lemma fixes the shape:

```lean
@[simp] theorem PlaceRes.addr_shift (r : PlaceRes) (k : Word) :
    ({ r with offset := r.offset + k } : PlaceRes).addr = r.addr + k
```

but it has to be applied at each consumer, on the goal or on the named
hypothesis, and WHICH is per-site. Three automated passes moved the
error count 59 → 46 → 55 → 67: non-monotone, because Lean reports one
error per declaration, so each fix unmasks the next. It needs a patient
per-declaration migration, not a script.

## [OBS] the judgement

The payoff is real — `h_dle` becomes `Nat.le_add_right`, and the
`h_cancel` idiom (38 derivations, 143 uses) largely evaporates — but it
is a FIXED one-time cost of ~50 sites, and the remaining proof work is
FIVE residual sites. The refactor would have paid for itself several
hundred leaf-lines ago; it does not now.

Recorded rather than carried: if the leaf population ever grows again
(a second permission model, or a v4), do this FIRST, before the leaves
accumulate.
