# Attribute and binder mechanics that actually shorten Lean proofs

**Status:** durable. Learned 2026-09-01 across `f744e0a`..`2721fce`,
which removed 1,919 lines between them without touching a single proof
*argument*. Every rule below was verified against the build or in a
scratch file, not reasoned about.

The theme: a large fraction of a mature proof corpus is not proof. It is
tactic *invocations* re-listing what could be named once, and binder
lists re-declaring what could be hoisted. That mass is invisible to
"factor out a lemma" thinking and is much cheaper to remove.

## `@[grind]` is safe where `@[simp]` is not

Marking the eight `csnorm` projection lemmas global `@[simp]` cascaded
(4 errors → 15) and blind cleanup of the newly-redundant tactics broke
three `rfl`s. It was reverted. See
[[transport-compiled-states-by-defeq]].

`@[grind]` has no such blast radius: **it changes no normal form**, and
`grind` is only ever invoked explicitly. Nothing that does not call
`grind` can observe the attribute.

The repo had **483 `grind` calls and zero `@[grind]` attributes** — every
call passed its lemmas inline. Across all 483 only **nine** distinct
lemmas ever appeared. Registering those nine made a bare `grind` as
strong everywhere.

**Placement is the whole difficulty.** An attribute must follow its
definition, so the nine needed FOUR registration points in common.lean:
`RegisterBelow` is defined ~300 lines above the `AddrRenameMap`
operations, and grind calls sit between them. Two red builds were
placement alone.

## Simp sets: the biggest single win, and three traps

`simp only` excludes the default simp set. So lemmas that are ALREADY
global `@[simp]` still have to be listed by hand at every `simp only`
site — and that is how 205 sites came to spell out the same six
`CheckedCompilerM` run/value projections, three dedicated lines each.
Naming them `csMonad` returned **659 lines**.

This is the complement of the `csnorm` decision, not a reversal of it.
`csnorm` stays out of the global set because it WOULD change normal
forms. A `csMonad`-style set changes nothing: the lemmas were already
`@[simp]`, and the set only saves `simp only` from re-listing what it
deliberately excluded. **The test for "is this set safe?" is: were these
lemmas already `@[simp]`, or is every site that lists one listing all of
them?**

Traps, each of which cost a red build:

1. **A simp attribute cannot be APPLIED in the file that REGISTERS it.**
   `register_simp_attr` must sit upstream of every use. Hence
   `proof/simpattrs.lean`, which exists for that reason alone.
2. **`register_simp_attr` needs `import Lean`** — which is why it is not
   in production `compile.lean` (that file imports only `obseq3.syntax`
   and `obseq3.oseair`, and should stay that way).
3. **Commands do not take docstrings.** `register_simp_attr`,
   `attribute` and `variable` are commands, not declarations, so `/-- -/`
   before them is a parse error. Use `--` or `/-! -/`. This one bit
   three times in one session.

**Choose clusters by measured line saving, not site count.** Two
counter-examples: `{emit, List.length_cons, List.length_nil}` occurs at
78 sites and is worth **zero** lines (it always already fits on one
line); folding `compileRExprToChecked` into `csCompile` scores 27 lines
but only 74 of that set's 162 sites list it, so the other 88 would begin
unfolding the rvalue compiler — a semantic change for one line per site.

Landed sets: `csMonad` (659), `csRun` (91), `csCompile`/`mirPrep`/
`mirAlloc`/`csCleanup` (137). After those the best remaining cluster is
under 30 lines; the seam is worked out.

## `variable` hoisting: implicits are free, explicits are not

Verified in a scratch file before touching anything:

* A section variable **mentioned in the statement** is auto-included —
  no `include` needed.
* A theorem that binds its own `{Γ : Ctx}` **shadows** the section
  variables cleanly and picks up none of them. No error, no capture.
  This is what makes hoisting viable in a file where the 64 target
  theorems are interleaved with ~140 fragment lemmas that all declare
  their own `Γ`.

**The rule that decides everything: variables are inserted AHEAD of a
theorem's own binders.** So

* hoisting an **implicit** that was already a LEADING binder produces a
  byte-identical signature — free, no call-site churn;
* hoisting an **explicit** hypothesis reorders the explicit arguments of
  every affected theorem and breaks every call site.

So the four ambient implicit lines (`Γ`/`cs0`/`prog`, `ρa`/`ρt`,
`s_mir`/`s_mir'`, `s_osea`) hoisted for free at 64 theorems (208 lines),
and the tempting larger version — also hoisting
`compProg`/`h_comp`/`h_inv`/`h_stmt`, another ~198 lines — was NOT done:
those are hypotheses, no conclusion mentions them, so each theorem would
need an `include` line AND the explicit order would change.

## `{X with f := v}` — confirmed, and it cuts both ways

copy.lean spelled a record update longhand 281 times where its three
sibling files already used `{X with …}`. Converting was worth 214 lines.

Exactly one theorem could not take it, and for the reason already in
[[transport-compiled-states-by-defeq]]: **`{X with f := v}` elaborates
to a `let` in a HYPOTHESIS but a flat literal in a goal.** In
`copy_projdst_offset_chainsrc_simulation` two `have`s state bounds on
`(emit {X with …} l).nextReg`; once their types carried the `let`, the
closing `omega` no longer saw the same atoms as the goal, and
`simp only [emit] at h1 h2` did not recover it.

So the note's warning is precise rather than general: the `with` form is
the right default, and the `let` bites only where a hypothesis's TYPE is
later matched syntactically against a goal. One failure in 254.

**And it does not scale into NESTED towers — measured, do not retry.**
Only 84 of copy.lean's 219 longhand records were multi-line; the other
135 sit INSIDE records the converter had already rewritten, on single
enormous lines (median 670 chars, max 4,010). Converting those too runs
clean — 92 more records, zero build errors — and makes the file *worse*:

    pre-conversion    1,144,128 bytes  12,247 lines  maxline 12,102
    outer only        1,157,830        12,033        maxline  9,345
    + nested          1,179,921        12,125        maxline  9,345

`{X with f := X.f + 1}` mentions `X` **twice** against longhand's four,
so it wins when `X` is small and LOSES when `X` is itself a giant nested
tower: the outer rewrite has already duplicated that text, and halving
the inner copies does not pay for the duplication.

The real defect there is not the spelling. It is that a term like
`emit { … } [Instr.Assgn …]` is written out in full at every nesting
level, which wants a NAMED intermediate state (a `def`, or `set` in the
proof) — a different and larger job.

## The other lever: invert, do not `split`

Not an attribute trick, but it belongs with them because it was found
the same way — by ranking repeated blocks rather than reading proofs.

52 leaves opened with the same eight-line `simp only
[writeResolvedPlace]` / `split` / `split` ritual. That is worse than
eight lines: the two dead branches wrap the ENTIRE remainder of the
proof in nested bullets, costing four columns of indentation and forcing
extra wrapping all the way down. One inversion lemma
(`writeResolvedPlace_ok_inv`) replaces the header with a single `obtain`
and de-indents the body — **415 lines**.

**When a `split` has dead branches, state the inversion instead.** The
line count of such a block is never just its header.

One site needed `simp only at h_nb` afterwards: the lemma states its
bound with `dst.addr`/`dst.allocSize` as projections, whereas `split`
had beta-reduced them against a `PlaceRes` literal, so a downstream
`omega` lost the arithmetic.
