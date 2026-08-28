# 2026-08-29 (cont. 2) — The flattening recursion + the zero-offset deref leaf

## What closed (const_write, the non-local-dst class begins)
1. **stmt0-generalization**: the five closed const-write leaves
   (C0, C1, C-deref, the new C-deref-zero, D-spine) now take the
   PROGRAM's statement abstractly — `{stmt0} (h_stmt : get? = stmt0)`
   plus run/value transfer functions to the canonical spelling. The
   leaves only ever consumed h_stmt through
   `compileStmt_emitted_in_compProg` / `prefixCompileState_succ`, so
   the surgery per leaf is: fragment-run composed with `h_run0`,
   stmtOut through `h_val0`, refine witness `run stmt0`. Old call
   sites pass `(fun _ => rfl) (fun _ so h => ⟨so, h⟩)`.
2. **Flattening**: nested projection towers reassociate on BOTH
   machines. Source: `resolvePlace?/resolvePlaceAcc/preparePlaceAssign
   _proj_assoc` (spine.lean) — offsets compose by `offset_append` +
   `Nat.add_assoc`. Compiled: `compileStmt_assign_proj_assoc_run/_value`
   (rhs-generic) via `placeToRegChecked_proj_assoc_eq` + bind-peeling.
   `const_write_proj_simulation` is now an INDUCTION on the base: the
   proj case recurses with the composed path, threading stmt0 — the
   program's nested spelling never changes, only the canonical target.
3. **C-deref-zero** (`(*p).f := v` at offset 0): the projection returns
   the loaded register, so the fragment is D-spine's
   `[spine; Load; CStore]`. Proof stitched: C-deref's inversion +
   scaffolding, D-spine's endgame, one `rw [show path.offset = 0 from
   h_o]` (the spelling-atom pothole again: `pathOffset` vs `.offset`).

Every projection tower over a bound local or a load-spine pointer, at
any offset and any nesting depth, is now closed. The residual holds
only unbound roots (regime-B) and non-spine pointer chains (deep-chain
class).

## Why a statement-transfer, not a leaf-per-spelling
The program may contain `s.f.g := v` while the lowering compiles the
reassociated `s.(f++g) := v`. The leaves' invariant-rebuilding is tied
to `prog.get?`'s literal statement, so either every leaf is re-proved
per spelling (exponential) or the leaves abstract over the statement
up to compiled run/value — one parameter triple, five mechanical
surgeries, and the recursion is three lines per level.

## Tests
d38 (nested tower write, pair-of-pairs), d39 (zero-offset field write
through a pointer): 52/52. Suite 82/123 unchanged; axiom audit exact;
leaf axioms standard.

## Potholes
- The stitched-proof approach (copy C-deref head + D-spine tail with
  renames) worked on the second try — the one failure was, again, a
  spelling mismatch (`path.offset` in a subst'd hypothesis vs
  `pathOffset path` in the rewrite).
- End-marker discipline for python extraction: D-spine's tail ends at
  the DEEP-residual docstring, not at C0's (file order moved long ago).
