// PLDI 2027 review layout. Build from the repository root with:
// typst compile --root . --font-path assets/fonts/acm \
//   pldi27/mirlite-oseair-correctness.typ
//
// Presentation follows oopsla26/opsem.tex: for each language, SYNTAX is one
// grammar | semantic domains | types figure, SEMANTICS is one
// Premises | Conclusion | Rule Name table, and the EXAMPLE is a stepwise
// post-state table followed by a walkthrough that cites rule names.
// Every number in the example tables is printed by
// notes/2026-09-18-paper-running-example.lean and pinned by the witnesses
// g14/d92 in src/obseq3/compile_tests.lean.
#import "@preview/faithful-acmart:0.1.0": acmart
// Numbered environments. All kinds share one counter, reset per section,
// so a section reads Definition 5.1, Lemma 5.2, Theorem 5.3, ...
#let thmcnt = counter(figure.where(kind: "thmenv"))
#show heading.where(level: 1): it => { thmcnt.update(0); it }
#let thmenv(head, bodyfmt: emph) = (..args, body) => figure(
  kind: "thmenv",
  supplement: head,
  outlined: false,
  placement: none,
  numbering: (..n) => context numbering("1.1", counter(heading).get().first(), ..n.pos()),
  caption: if args.pos().len() > 0 { args.pos().first() } else { none },
  bodyfmt(body),
)
#show figure.where(kind: "thmenv"): it => block(
  width: 100%,
  above: 0.9em,
  below: 0.9em,
  {
    set align(left)
    set par(first-line-indent: 0pt)
    strong[#it.supplement #it.counter.display(it.numbering)]
    if it.caption != none [ (#it.caption.body)]
    h(0.5em)
    it.body
  },
)
// A reference to a numbered environment takes its section number where the
// environment stands, not where the reference does.
#show ref: it => {
  let el = it.element
  if el != none and el.func() == figure and el.kind == "thmenv" {
    let h = counter(heading).at(el.location()).first()
    let n = counter(figure.where(kind: "thmenv")).at(el.location()).first()
    link(el.location(), text(fill: black)[#el.supplement #h.#n])
  } else { it }
}
#let definition = thmenv("Definition")
#let lemma = thmenv("Lemma")
#let theorem = thmenv("Theorem")
#let corollary = thmenv("Corollary")
#let example = thmenv("Example", bodyfmt: x => x)
#let proof(body) = block(
  width: 100%,
  above: 0.9em,
  below: 0.9em,
  {
    set par(first-line-indent: 0pt)
    [_Proof sketch._]
    h(0.5em)
    body
    h(1fr)
    $square$
  },
)

#let accent = rgb("315d82")
#let pale = rgb("eef4f8")
#let rule = rgb("c8d2da")
#let sanscaps(body) = text(font: "Libertinus Sans", size: 8pt, weight: "semibold", body)
#let source(body) = block(
  width: 100%,
  inset: (top: 3pt, bottom: 3pt, left: 5pt, right: 5pt),
  fill: rgb("f7f7f7"),
  stroke: (left: 1.5pt + accent),
  text(font: "Libertinus Sans", size: 8pt, fill: rgb("4d5963"), body),
)
#let takeaway(title, body) = block(
  width: 100%,
  breakable: false,
  inset: 6pt,
  radius: 2pt,
  fill: pale,
  stroke: 0.6pt + rule,
  [#sanscaps(title) #h(4pt) #body],
)

// ---------------------------------------------------------------------
// Syntax: BNF panels and the grammar | semantic domains | types figure.
// ---------------------------------------------------------------------
// prod(lhs, alt-line, alt-line, ...): the first line is introduced by ::=,
// every further line by |.
#let prod(lhs, rel: $::=$, ..lines) = {
  let out = ()
  for (i, l) in lines.pos().enumerate() {
    out.push(if i == 0 { lhs } else { [] })
    out.push(if i == 0 { rel } else { $|$ })
    out.push(l)
  }
  out
}
// Every line is headed `Name ∋ x`. `::=` is reserved for productions;
// defn gives a set that simply equals something (maps, lists, numbers);
// decl declares a further metavariable over a set defined elsewhere.
#let defn(lhs, rhs) = prod(lhs, rel: $=$, rhs)
#let decl(lhs) = (lhs, [], [])
#let bnf(..prods) = {
  set text(size: 7.6pt)
  set par(first-line-indent: 0pt, justify: false, leading: 0.4em)
  grid(
    columns: (auto, auto, 1fr),
    column-gutter: 3pt,
    row-gutter: 3.6pt,
    align: (right, center, left),
    ..prods.pos().flatten()
  )
}
#let panel(title, body) = block(width: 100%, below: 7pt, {
  set par(first-line-indent: 0pt)
  text(font: "Libertinus Sans", size: 6.4pt, weight: "semibold", fill: accent, upper(title))
  v(-6pt)
  line(length: 100%, stroke: 0.4pt + rule)
  v(-6pt)
  body
})
#let grammarfig(caption, lpanel, rpanel, split: (1fr, 1fr)) = figure(
  kind: image,
  caption: caption,
  block(width: 100%, inset: (x: 2pt), grid(
    columns: split,
    column-gutter: 12pt,
    align: top + left,
    lpanel, rpanel,
  )),
)

// ---------------------------------------------------------------------
// Semantics: Premises | Conclusion | Rule Name tables.
// ---------------------------------------------------------------------
// Rule names are small caps and are bound to identifiers, so a table row
// and the prose that cites it cannot drift apart.
#let rn(name) = box(text(font: "Libertinus Sans", size: 0.8em, weight: "semibold", fill: accent, upper(name)))
#let ir(name, premises, conclusion) = (premises, conclusion, name)
#let thead(..cells) = table.header(..cells.pos().map(c => text(fill: white, weight: "bold", c)))
#let ruletable(caption, ..rules, cols: (46%, 38%, 16%), placement: auto, size: 7.7pt) = figure(
  kind: table,
  placement: placement,
  caption: caption,
  {
    set text(size: size)
    set par(first-line-indent: 0pt, justify: false, leading: 0.42em)
    table(
      columns: cols,
      align: (left + horizon, left + horizon, left + horizon),
      inset: (x: 3.5pt, y: 3.6pt),
      stroke: (x, y) => (
        top: 0.45pt + rule,
        bottom: 0.45pt + rule,
        left: if x > 0 { 0.45pt + rule } else { none },
      ),
      fill: (x, y) => if y == 0 { accent } else { none },
      thead([Premises], [Conclusion], [Rule Name]),
      ..rules.pos().flatten(),
    )
  },
)
// Judgment arrows, colour-coded as in the OOPSLA paper.
#let jbox(c, body) = box(fill: c, inset: (x: 1.4pt), outset: (y: 1.6pt), radius: 1pt, body)
#let dA = jbox(rgb("fde3c4"), $scripts(arrow.b.double)_a$)
#let dP = jbox(rgb("e6d9f5"), $scripts(arrow.b.double)_p$)
#let dE = jbox(rgb("d5e0fa"), $scripts(arrow.b.double)_e$)
#let dH = jbox(rgb("d3efd3"), $scripts(arrow.b.double)_h$)
#let dCP = jbox(rgb("ecdcc8"), $scripts(arrow.b.double)_"cP"$)
#let dCB = jbox(rgb("ecdcc8"), $scripts(arrow.b.double)_"cB"$)
#let dCR = jbox(rgb("dcdcdc"), $scripts(arrow.b.double)_"cR"$)
#let smir = $attach(arrow.r.long, br: "mir")$
#let ssea = $attach(arrow.r.long, br: "sea")$
#let sC = $attach(arrow.r, br: "c")$
#let sPr = $attach(arrow.r, br: "p")$
#let emit = $plus.o$
#let dr = $class("normal", ast)$
// The size, in bytes, of the allocation a pointer points into.
#let sz = $italic("sz")$

// ---------------------------------------------------------------------
// Example: stepwise post-state tables and side-by-side listings.
// ---------------------------------------------------------------------
#let statetable(caption, header, cols, ..rows, placement: auto, size: 7.3pt, pad: 3.2pt) = figure(
  kind: table,
  placement: placement,
  caption: caption,
  {
    set text(size: size)
    set par(first-line-indent: 0pt, justify: false, leading: 0.42em)
    table(
      columns: cols,
      align: left + horizon,
      inset: (x: 3.5pt, y: pad),
      stroke: (x, y) => (
        top: 0.45pt + rule,
        bottom: 0.45pt + rule,
        left: if x > 0 { 0.45pt + rule } else { none },
      ),
      fill: (x, y) => if y == 0 { accent } else if calc.even(y) { rgb("f6f8fa") } else { none },
      thead(..header),
      ..rows.pos().flatten(),
    )
  },
)
// Full-configuration tables: one column per memory leaf, value over borrow
// stack; `chg` shades what the step changed.
#let chg = rgb("fdf0cf")
#let stk(body) = text(size: 0.92em, fill: rgb("4d5963"), body)
#let nocell = text(fill: rgb("9aa5ad"))[---]
// The place a leaf column holds, under its byte range in a table header.
#let plc(body) = text(weight: "regular", size: 0.95em, body)
// A walkthrough: one labelled item per statement or label group.
#let walk(..items) = block(width: 100%, above: 0.8em, below: 0.9em, {
  set par(first-line-indent: 0pt)
  grid(
    columns: (auto, 1fr),
    column-gutter: 7pt,
    row-gutter: 0.75em,
    ..items.pos().map(((l, b)) => (text(font: "Libertinus Sans", size: 7.6pt, weight: "semibold", fill: accent, l), b)).flatten()
  )
})
// A prose-style two/three-column table in the same dress (appendix).
#let proptable(caption, header, cols, ..rows, placement: none) = statetable(
  caption, header, cols, ..rows, placement: placement, size: 7.7pt)
#let listing(title, body) = block(
  width: 100%,
  inset: (x: 6pt, y: 5pt),
  fill: rgb("f7f7f7"),
  stroke: (left: 1.5pt + accent),
  {
    set align(left)
    set par(first-line-indent: 0pt, leading: 0.5em)
    set text(size: 8pt)
    text(font: "Libertinus Sans", size: 6.4pt, weight: "semibold", fill: accent, title)
    linebreak()
    body
  },
)

// Rule names ----------------------------------------------------------
#let sb-own = rn[sb-own]
#let sb-read = rn[sb-read]
#let sb-use = rn[sb-use-mut]
#let sb-refm = rn[sb-ref-mut]
#let sb-refs = rn[sb-ref-shared]
#let sb-refr = rn[sb-ref-raw]
#let sb-die = rn[sb-die]
#let sb-range = rn[sb-range]

#let m-local = rn[plc-local]
#let m-proj = rn[plc-proj]
#let m-deref = rn[plc-deref]
#let m-pbound = rn[prep-bound]
#let m-palloc = rn[prep-alloc]
#let m-const = rn[e-const]
#let m-copy = rn[e-copy]
#let m-move = rn[e-move]
#let m-ref = rn[e-ref]
#let m-assgn = rn[assgn]
#let m-halt = rn[halt]

#let t-load = rn[rval-load]
#let t-alloc = rn[rval-alloc]
#let t-borrow = rn[rval-borrow]
#let t-assgn = rn[exec-assgn]
#let t-store = rn[exec-store]
#let t-storec = rn[exec-storec]
#let t-die = rn[exec-die]
#let t-halt = rn[exec-halt]

#let c-rbound = rn[root-bound]
#let c-ralloc = rn[root-alloc]
#let c-local = rn[place-local]
#let c-assoc = rn[place-assoc]
#let c-proj0 = rn[place-proj-0]
#let c-projd = rn[place-proj-n]
#let c-deref = rn[place-deref]
#let c-blocal = rn[bplace-local]
#let c-bproj = rn[bplace-proj]
#let c-bderef = rn[bplace-deref]
#let c-const = rn[rhs-const]
#let c-copy = rn[rhs-copy]
#let c-move = rn[rhs-move]
#let c-ref = rn[rhs-ref]
#let c-assign = rn[stmt-assign]
#let c-halt = rn[stmt-halt]
#let c-pempty = rn[prog-empty]
#let c-pstep = rn[prog-step]

#show: acmart.with(
  format: "acmsmall",
  font-size: 10pt,
  title: "A Borrow-Aware Compiler from MIRLite to OSEA-IR",
  authors: (),
  abstract: [
    MIRLite gives typed Rust-like places an operational semantics on
    byte-addressed memory: every integer has its width, every aggregate its
    byte layout, and every pointer byte carries its provenance. Its compiler
    lowers each statement to OSEA-IR with explicit reads, retags, writes, and
    borrow retirement. We present Stacked Borrows, both languages, and the
    compiler in one format: a grammar, a table of named rules, and the
    stepwise execution of one five-statement program that allocates a
    nested tuple, writes a nested field, borrows that field, and writes
    through the borrow. We then state the forward simulation that relates
    source and target memory byte by byte, locals, and per-byte permission
    stacks, and replay the same program as a simulation. The simulation is
    mechanized in Lean 4 for every MIRLite program, under two conditions on
    the byte layouts that a decidable check discharges for the layouts Rust
    gives.
  ],
  keywords: ("borrow semantics", "compiler correctness", "Lean", "Stacked Borrows"),
  anonymous: true,
  review: true,
  screen: true,
  nonacm: true,
  print-folios: true,
  print-ccs: false,
  print-acm-reference: false,
)
#set math.equation(numbering: none)

= Introduction

The compiler in this paper connects two views of the same memory operation.
MIRLite says _which typed place_ a Rust-like statement accesses. OSEA-IR says
_which reads, retags, writes, and borrow retirements_ implement that access.
The proof relates their executions without demanding that their permission
stacks be literally equal: the target is allowed to introduce short-lived
tags that have no source counterpart. @sec:compiler names them route tags.

Memory is byte-addressed, as in Rust's own interpreter. Every local has a
_byte layout_: an integer occupies its width in bytes, a pointer eight, and
an aggregate places its fields at byte offsets inside a block that may
contain padding. A memory $mu$ maps each address to an _abstract byte_,
uninitialized or a concrete byte that may carry pointer provenance. A value
is read and written _leaf by leaf_: the leaves of a layout are its integers
and pointers, each decoded from, or encoded into, its own bytes. A pointer
value $"ptr"(b,o,e,sz,t)$ denotes address $b+o$ in an allocation with base
$b$ and size $sz$ bytes, claims $e$ bytes from there, and carries the
provenance tag $t$. A permission state $Pi$ records one borrow stack per
byte.

@sec:opsem formalizes the compilation. It
(1) fixes the permission model, per-byte Stacked Borrows, and threads it
through every memory operation (@sec:perm);
(2) defines MIRLite, the typed source language (@sec:mirlite);
(3) defines OSEA-IR, a register machine whose instructions expose the
permission events a MIRLite statement leaves implicit (@sec:oseair);
(4) presents the compiler between them (@sec:compiler); and
(5) states the forward simulation that the compiler satisfies
(@sec:correctness).
@sec:mech records what is mechanized, and @sec:surface extends every table
from the constructs shown in the main text to the full executable surface.

#takeaway([READING GUIDE], [
  Subsections @sec:perm[] to @sec:compiler[] share one layout. _Syntax_ is a
  single figure: grammar, semantic domains, types. _Semantics_ is a single
  table of named rules, read as premises, conclusion, name. The _example_ is
  a stepwise table giving the state after each instruction, and a
  walkthrough that names the rule each row fires. From
  @sec:mirlite on the example is one program, read once more in
  @sec:correctness as a simulation.
])

= Compiling MIRLite to OSEA-IR with ownership <sec:opsem>

This section formalizes the compilation from MIRLite to OSEA-IR and the
sense in which it preserves ownership. The order is bottom-up. Stacked
Borrows comes first (@sec:perm), because both languages are defined over
it. MIRLite (@sec:mirlite) and OSEA-IR (@sec:oseair) follow, then the
compiler between them (@sec:compiler), then its correctness
(@sec:correctness). Each subsection ends with an example. The example of
@sec:perm is a command sequence on a single byte; from @sec:mirlite on it
is one MIRLite program, introduced there and carried through the rest of
the section.

== Stacked Borrows <sec:perm>

#figure(
  kind: image,
  caption: [A Stacked Borrows command sequence on the one byte at address $a$, with the stack after each command.],
  text(size: 7.8pt)[
    $Pi(a)=[] quad
     attach(arrow.r.long, t: "own"(a)) quad ["Own"(t)] quad
     attach(arrow.r.long, t: "ref"("mutable",a,t)) quad ["MutRef"(u),"Own"(t)] quad
     attach(arrow.r.long, t: "useMut"(a,u)) quad ["MutRef"(u),"Own"(t)] quad
     attach(arrow.r.long, t: "die"(a,u)) quad ["Own"(t)]$
  ],
) <fig:sb-example>

The Stacked Borrows model of Jung et al. formalizes Rust's ownership and
borrowing rules for safe and unsafe code. It is orthogonal to the rest of a
memory model: it is added to a language by threading a permission state
through the memory operations. We use that to give MIRLite and OSEA-IR the
_same_ permission semantics. Formally, both languages are parameterized by
a _permission model_, an abstract state $Pi$ with partial operations
`own`, `read`, `useMut`, `ref`, and `die`. Each returns a new state or
fails; a failure is undefined behavior and aborts the execution. The
correctness result instantiates the model with the per-byte Stacked Borrows
of this subsection, as Miri does. The full executable language uses four
further operations, for deallocation, exposed provenance, and protector
frames; they are in @sec:surface-perm.

A permission state is $Pi=("stacks","NextTag","frames","exposed","retired")$. The
component `stacks` is a partial map from byte addresses to _borrow
stacks_; `NextTag` is the next fresh tag; `frames`, `exposed`, and
`retired` are the protector frames, the list of exposed tags, and the list
of tags that `die` has ended, which only the full language reads
(@sec:surface-perm). We write $Pi(a)$ for the
stack at $a$ and leave the other four components implicit when a rule does
not change them. A borrow stack is a list of _items_, topmost first,

#align(center)[
  $iota ::= "Own"(t) | "MutRef"(t) | "Ref"(t) | "RawPtr"(m',t) | "Disabled"(t),$
]

where $t$ is the item's tag and $m'$ a mutability flag. The top of the stack
is the most recently derived permission. A new item is derived from an
existing one by a _retag_, and the _retag kind_

#align(center)[
  $k ::= "shared" | "mutable" | "raw-const" | "raw-mut" | "two-phase"$
]

says which item it pushes: a shared reference $"Ref"$, a mutable reference
$"MutRef"$, a read-only or mutable raw pointer $"RawPtr"("false",dot)$ or
$"RawPtr"("true",dot)$, or a reserved mutable borrow. The kinds `shared`
and `mutable` are Rust's `&T` and `&mut T`, and `raw-const` and `raw-mut`
are its raw pointers `*const T` and `*mut T`. A `raw-const` retag acts on
the stack exactly as a `shared` one does, but pushes a differently named
item; the name matters because related stacks must agree item by item
(@def:permsim). A retag also takes a
protector flag $c$ and an interior-mutability mask $m$, a list of booleans
with one entry per byte of the retagged range. Both are inert in
the main text, where $c="false"$ and $m$ marks no byte, and so is
`two-phase`; all three are defined in @sec:surface-perm. @tab:sb gives the
rules. A rule $⟨ "op", Pi ⟩ #dA Pi'$ acts on one byte $a$; "$u$ fresh"
means $u=Pi."NextTag"$, and the conclusion increments the counter.
@fig:sb-example runs four of them: #sb-own pushes the owning item of a new
allocation, #sb-refm derives a mutable borrow with a fresh tag $u$ from its
parent $t$, #sb-use validates a write through $u$, and #sb-die pops $u$'s
item, which is how a borrow is retired. After the four commands the stack
is what it was after the first; only the tag counter remembers that $u$
existed. That observation is what makes a route tag unobservable at the
next statement boundary, and it is why the simulation of @sec:correctness
compares tag counters by an inequality.

#ruletable(
  [Stacked Borrows rules at one byte $a$. $x$ and $y$ range over lists of items, $x$ being the part of the stack above the granting item; $"tag"(iota)$ is the tag an item carries; $"dis"(x)$ replaces each $"MutRef"(u)$ in $x$ by $"Disabled"(u)$. In #sb-refs, $iota'$ is the item that a retag of kind $k$ pushes. No rule applies when a removed or disabled item is protected (@sec:surface-perm).],
  ir(sb-own,
    [$Pi(a) in {bot, []}$, #h(3pt) $t$ fresh],
    [$⟨ "own"(a), Pi ⟩ #dA (Pi[a |-> ["Own"(t)]], t)$]),
  ir(sb-read,
    [$Pi(a) = x plus.double (iota :: y)$, #h(3pt) $"tag"(iota)=t$, \ $iota != "Disabled"(t)$],
    [$⟨ "read"(a,t), Pi ⟩ #dA Pi[a |-> "dis"(x) plus.double (iota :: y)]$]),
  ir(sb-use,
    [$Pi(a) = x plus.double (iota :: y)$, #h(3pt) $"tag"(iota)=t$, \ $iota in {"Own"(t), "MutRef"(t)}$],
    [$⟨ "useMut"(a,t), Pi ⟩ #dA Pi[a |-> iota :: y]$]),
  ir(sb-refm,
    [$⟨ "useMut"(a,t), Pi ⟩ #dA Pi_1$, #h(3pt) $u$ fresh],
    [$⟨ "ref"("mutable",a,t), Pi ⟩ #dA$ \ $quad (Pi_1[a |-> "MutRef"(u) :: Pi_1(a)], u)$]),
  ir(sb-refs,
    [$⟨ "read"(a,t), Pi ⟩ #dA Pi_1$, #h(3pt) $u$ fresh, \ $(k, iota') in {("shared", "Ref"(u)),$ \ $quad ("raw-const", "RawPtr"("false",u))}$],
    [$⟨ "ref"(k,a,t), Pi ⟩ #dA$ \ $quad (Pi_1[a |-> iota' :: Pi_1(a)], u)$]),
  ir(sb-refr,
    [$Pi(a) = x plus.double (iota :: y)$, #h(3pt) $"tag"(iota)=t$, \ $iota != "Disabled"(t)$, #h(3pt) $u$ fresh],
    [$⟨ "ref"("raw-mut",a,t), Pi ⟩ #dA$ \ $quad (Pi[a |-> x plus.double ("RawPtr"("true",u) :: iota :: y)], u)$]),
  ir(sb-die,
    [$Pi(a) = iota :: y$, #h(3pt) $"tag"(iota)=u$, \ $iota != "Own"(u)$],
    [$⟨ "die"(a,u), Pi ⟩ #dA Pi[a |-> y]$]),
  ir(sb-range,
    [$⟨ "op"(a+j, dots), Pi_j ⟩ #dA Pi_(j+1)$ for $0 <= j < n$, \ one fresh tag shared by all $n$ bytes],
    [$"op"(Pi_0, a, n, dots) = Pi_n$]),
) <tab:sb>

Three points of the model matter later. A read through $t$ does not remove
the mutable borrows above $t$: #sb-read _disables_ them in place, because
removing them would merge the raw-pointer groups on either side. A shared or
raw-constant retag is a read through its parent followed by a push
(#sb-refs). A raw-mutable retag performs no access and inserts its item directly above
its parent (#sb-refr), so sibling raw pointers share one group instead of
invalidating each other. And every operation of the interface ranges over
$n$ bytes from $a$ (#sb-range): $"own"(Pi,a,n)=(Pi',t)$,
$"read"(Pi,a,n,t)=Pi'$, $"useMut"(Pi,a,n,t)=Pi'$,
$"ref"(Pi,a,n,t,k,c,m)=(Pi',u)$, and $"die"(Pi,a,n,t)=Pi'$. The per-byte
granularity is what makes the width of a borrow observable, down to a
one-byte field inside a wider one, and hence what the compiler must get
right in @sec:compiler.

In the mechanization the operations are `sb_own`, `sb_read`, `sb_write`,
`sb_ref`, and `sb_die` in `src/obseq3/sb.lean`; the paper writes `useMut`
for `sb_write` to keep the source-level reading. The layer acts on address
ranges and never asks what an address unit is.

== MIRLite <sec:mirlite>

#grammarfig(
  [Grammar, semantic domains, and types of MIRLite. Every line is headed $X in.rev x$: the metavariable $x$ ranges over the set $X$. With $::=$ the line is a production: $X$ is generated by the constructors on the right. With $=$ the set $X$ is built from other sets: $times$ is a product, $harpoon.rt$ a partial map, $arrow.r$ a total one, and $X^*$ the lists over $X$; $"Perm"$ is the set of permission states of @sec:perm. With nothing on the right it declares a further metavariable over a set defined elsewhere. Retag kinds $k$, flags $c$, and masks $m$ are those of @sec:perm, repeated here. The main text covers these forms; @fig:surface-grammar has the rest.],
  panel([Terms], bnf(
    prod($"Program"$, $"Stmt"^* thick "halt"$),
    prod($"Stmt" in.rev s$, $d := e thick | thick "halt"$),
    prod($"Place" in.rev p$, $ell thick | thick p.q thick | thick #dr p$),
    decl($"Place" in.rev d$),
    defn($"Local" in.rev ell$, $NN$),
    prod($"Path" in.rev q$, $epsilon thick | thick f.q$),
    decl($NN in.rev f$),
    prod($"Expr" in.rev e$, $"const"(w) thick | thick "copy"(p) thick | thick "move"(p)$, $"ref"(k,c,m,p)$),
    prod($"Kind" in.rev k$, $"shared" | "mutable"$, $"raw-const" | "raw-mut"$, $"two-phase"$),
    defn($"Flag" in.rev c$, $"Bool"$),
    defn($"Mask" in.rev m$, $"Bool"^*$),
  )),
  [
    #panel([Semantic domains], bnf(
      defn($"State" in.rev S$, $NN times "Env" times "Mem" times "Perm"$),
      defn($"Env" in.rev E$, $"Local" harpoon.rt NN times "Tag"$),
      defn($"Mem" in.rev mu$, $(NN arrow.r "Byte") times "Allocs" times NN times NN^*$),
      prod($"Byte" in.rev alpha$, $"uninit" thick | thick "init"(x, pi)$),
      prod($"Prov" in.rev pi$, $bot thick | thick (b,sz,e,t)$),
      prod($"Value" in.rev v$, $"undef" thick | thick "word"(w)$, $"ptr"(b,o,e,sz,t)$),
      decl($NN in.rev i, a, b, o, e, sz, w$),
      defn($"Tag" in.rev t, u$, $NN$),
      decl($"Perm" in.rev Pi$),
    ))
    #panel([Types and byte layouts], bnf(
      prod($"Layout" in.rev tau$, $"Int" theta thick | thick "Ptr" tau$, $(tau_0,dots,tau_(n-1))$),
      decl($"Layout" in.rev sigma$),
      defn($"IntTy" in.rev theta$, $NN times "Bool"$),
      defn($"Ctx" in.rev Gamma$, $"Layout"^*$),
      prod($"BLayout" in.rev beta$, $"int"(n) thick | thick "ptr"(beta)$, $"tup"(overline(beta), overline(o), n, "al")$),
      prod($"Scalar" in.rev kappa$, $"int"(n) thick | thick "ptr"$),
      defn($"LayEnv" in.rev Lambda$, $"Local" arrow.r "BLayout"$),
    ))
  ],
) <fig:mir-grammar>

MIRLite is a typed, sequential language for the memory-level part of Rust
that matters to borrow reasoning (@fig:mir-grammar). A program is a list of
statements. A statement assigns an expression to a place, or halts. A
_place_ is a local $ell$, a projection $p.q$ of a place along a path, or a
dereference $#dr p$. Both $p$ and $d$ range over places; we write $d$ when
the place is the _destination_ of an assignment, as in $d := e$, and $p$
otherwise. An _expression_ is a constant, a copy or a move of a place, or
a reference to a place. A move is MIR's `move` operand: like Miri, the
semantics reads the source through a fresh mutable borrow that it retires
at once (#m-move), so a move invalidates the shared borrows of the moved
place where a copy only reads it. We do not model control flow in the main
text; the guarded assignment of the full language is in @sec:surface.

*Types and layouts.* A _layout type_ $tau$ is the static type of a place:
an integer $"Int" theta$ of integer type $theta$, a width in bits and a
signedness; a pointer $"Ptr" tau$ to a $tau$; or a tuple. A _byte layout_
$beta$ says where the bytes of a value of that type lie: an integer of $n$
bytes, a thin pointer of eight bytes to a $beta$, or a tuple whose fields
$overline(beta)$ lie at the byte offsets $overline(o)$ inside a block of
$n$ bytes aligned to $"al"$. Its size $|beta|$ is $n$, eight, or $n$, and
its _leaves_ are the scalars it holds, with their offsets:

#align(center)[
  $"leaves"("int"(n))=[(0,"int"(n))] quad
   "leaves"("ptr"(beta))=[(0,"ptr")] quad
   "leaves"("tup"(overline(beta),overline(o),n,"al"))=
     plus.double_(j) [(o_j + o', kappa) | (o',kappa) in "leaves"(beta_j)].$
]

A scalar has size $|"int"(n)|=n$ and $|"ptr"|=8$. Alignment is
$"al"("int"(n))=n$, $"al"("ptr"(beta))=8$, and a tuple's own $"al"$. The
_C layout_ of fields $overline(beta)$ places them in order, each at the
next multiple of its alignment, and rounds the size up to the largest
field alignment: `(u8, u32)` has its fields at offsets 0 and 4 and size 8.
The layout type and the
byte layout are two halves of one Rust type: the type says what a place
holds, the layout where its bytes are. Keeping them apart lets the source
take rustc's own field offsets for `repr(Rust)` structs, which reorder
fields. A _layout environment_ $Lambda$ gives every local a byte layout,
and every place gets one statically: $Lambda(ell)$ for a local, the layout
of the field that $q$ selects for $p.q$, and $beta$ for $#dr p$ when
$Lambda(p)="ptr"(beta)$. The byte offset of a projection,
$"off"_Lambda (p,q)$, is the sum of the field offsets along $q$ in
$Lambda(p)$. The theorem of @sec:correctness holds for every $Lambda$
whose integer and pointer places have one-leaf layouts of the right size
(@def:layoutwf).

A _local_ $ell$ is a program variable, the counterpart of a MIR local such
as `_0`. A context $Gamma$ lists the layout types of a program's locals, a
local is an index into that list, and $ell:tau$ means that entry $ell$ of
$Gamma$ is $tau$. We write $x$ and $y$ for the locals 0 and 1 of the
running program. A _path_ $q$ is a list of tuple-field indices, read left
to right: $epsilon$ selects the whole region and $f.q$ selects field $f$
and then follows $q$; it is typed, $q:sigma arrow.r tau$, when following
it through a $sigma$ selects a $tau$. Places are indexed by the layout
type they select: $Gamma tack ell:tau$ if $ell:tau in Gamma$;
$Gamma tack p.q:tau$ if $Gamma tack p:sigma$ and $q:sigma arrow.r tau$;
and $Gamma tack #dr p:tau$ if $Gamma tack p:"Ptr" tau$. Expressions and
statements are indexed the same way: $"const"(w)$ has any integer type,
the one its destination has; $"copy"(p)$ and $"move"(p)$ have the type of
$p$; $"ref"(k,c,m,p)$ has $"Ptr" tau$ when $Gamma tack p:tau$; and
$d:=e$ requires $d$ and $e$ to have the same type, so a `u8` is never
copied into a `u64` without a cast.

*Reference formation.* $"ref"(k,c,m,p)$ carries the retag kind $k$,
protector flag $c$, and mask $m$ of @sec:perm and hands them to the
permission model (#m-ref). The mask a program writes has one entry per
leaf; $"bytes"_beta (m)$ gives every byte of $beta$ the entry of the leaf
it belongs to. The kind is not limited to Rust references: a MIRLite
program can form raw pointers and two-phase borrows as well.

*Semantic domains.* A _value_ $v$ is the value of one leaf: undefined, a
word $w$, or a pointer; $overline(v)$ is a list of values, one per leaf. A
pointer $"ptr"(b,o,e,sz,t)$ has five fields. The _base_ $b$ and _size_
$sz$, in bytes, identify the allocation $[b,b+sz)$ it points into, and
every access through the pointer is checked against those bounds. The
_offset_ $o$ locates the pointer inside that allocation, so the address it
denotes is $b+o$; pointer arithmetic changes $o$ and nothing else. The
_extent_ $e$ is the number of bytes the pointer claims from there, the
referent's size for a thin pointer and the slice's length for a slice
reference (@sec:surface). The _tag_ $t$ is its provenance, the identity
under which the permission model of @sec:perm admits or rejects the
access. Two pointers to the same address with different tags are
different values, and only one of them may be allowed to write.

A memory $mu$ is a total map from addresses to _bytes_, together with the
table of allocated ranges, the bump-allocation watermark, and the list of
freed bases. A byte is uninitialized or a concrete byte $x$ that may carry
a _provenance_ $pi$, the base, size, extent, and tag of the pointer it is
part of. Values meet bytes at the leaves. Encoding $"enc"_kappa (v)$ turns
`undef` into $|kappa|$ uninitialized bytes, a word into its $|kappa|$
little-endian bytes without provenance (the word must fit), and
$"ptr"(b,o,e,sz,t)$ into the little-endian bytes of the address $b+o$,
every one carrying $(b,sz,e,t)$. Decoding $"dec"_kappa$ inverts it: an
integer leaf is the little-endian value of its bytes, with any provenance
stripped; a pointer leaf is a pointer when its eight bytes carry one
common provenance; and any uninitialized byte makes the leaf `undef`. A
typed read and write of a value of layout $beta$ at address $a$ are

#align(center)[
  $"rd"_beta (mu,a) = ["dec"_kappa (mu[a+o..a+o+|kappa|)) | (o,kappa) in "leaves"(beta)],$ \
  $"wr"_beta (mu,a,overline(v)) = mu[a..a+|beta|) |-> "uninit", "then" a+o |-> "enc"_kappa (v_j) "for the" j"-th leaf" (o,kappa),$
]

so padding becomes uninitialized, as a typed copy does in MiniRust; the
write fails when $overline(v)$ has the wrong number of values or a word
does not fit its leaf. The environment $E$ maps a local either to no
binding or to an allocation base and its owning tag. A local is allocated
when it is first written: one contiguous block of $|Lambda(ell)|$ bytes
aligned to $"al"(Lambda(ell))$, with a fresh owning tag on the borrow
stack of every byte, padding included. Its fields are bytes of that block
at their offsets, so a borrow of a field retags only the field's bytes. A state is
$S=(i,E,mu,Pi)$ with $i$ the program counter. @tab:mir gives the rules;
they use three judgments, which we introduce before the interpreter.

#ruletable(
  [MIRLite semantics. $S.i$, $S.E$, $S.mu$, and $S.Pi$ are the components of a state $S=(i,E,mu,Pi)$, and $S[Pi |-> Pi']$ is $S$ with its permission state replaced by $Pi'$. $Gamma$ and $Lambda$ are fixed throughout; $P$ is the program being run. "$b$ live" means that $b$ is not a freed base of $S.mu$. All rules describe successful branches. An unbound local in a read, a freed or out-of-bounds access, a read of an uninitialized leaf, or a rejection by the permission model is an error and has no successor.],
  ir(m-local,
    [$S.E(ell)=(a,t)$],
    [$S tack ell #dP (⟨a,t,a,|Lambda(ell)|⟩, S.Pi)$]),
  ir(m-proj,
    [$S tack p #dP (⟨a,t,b,sz⟩, Pi')$],
    [$S tack p.q #dP (⟨a+"off"_Lambda (p,q),t,b,sz⟩, Pi')$]),
  ir(m-deref,
    [$S tack p #dP (⟨a,t,b,sz⟩, Pi_1)$, #h(3pt) $b$ live, #h(3pt) $b <= a$, #h(3pt) $a+8 <= b+sz$, \ $"read"(Pi_1,a,8,t)=Pi_2$, #h(3pt) $"dec"_"ptr" (S.mu[a..a+8))="ptr"(b',o',e',sz',t')$],
    [$S tack #dr p #dP (⟨b'+o',t',b',sz'⟩, Pi_2)$]),
  ir(m-pbound,
    [$"lookup"(S,d)$ is defined],
    [$"prepare"(S,d)=S$]),
  ir(m-palloc,
    [$"lookup"(S,d)$ undefined, #h(3pt) $"root"(d)=ell$, #h(3pt) $S.E(ell)=bot$, #h(3pt) $beta=Lambda(ell)$, \ $"alloc"(S.mu,|beta|,"al"(beta))=(b,mu')$, #h(3pt) $"own"(S.Pi,b,|beta|)=(Pi',t)$],
    [$"prepare"(S,d)=$ \ $quad (S.i, thick S.E[ell |-> (b,t)], thick mu', thick Pi')$]),
  ir(m-const,
    [],
    [$S tack "const"(w) #dE (["word"(w)], S)$]),
  ir(m-copy,
    [$S tack p #dP (⟨a,t,b,sz⟩, Pi_1)$, #h(3pt) $beta=Lambda(p)$, #h(3pt) $b$ live, \ $a+|beta| <= b+sz$, #h(3pt) $"read"(Pi_1,a,|beta|,t)=Pi_2$, \ $overline(v)="rd"_beta (S.mu,a)$, #h(3pt) $"undef" in.not overline(v)$],
    [$S tack "copy"(p) #dE (overline(v), S[Pi |-> Pi_2])$]),
  ir(m-move,
    [$S tack p #dP (⟨a,t,b,sz⟩, Pi_1)$, #h(3pt) $beta=Lambda(p)$, #h(3pt) $b$ live, #h(3pt) $a+|beta| <= b+sz$, \ $"ref"(Pi_1,a,|beta|,t,"mutable","false",[])=(Pi_2,u)$, \ $"read"(Pi_2,a,|beta|,u)=Pi_3$, #h(3pt) $"die"(Pi_3,a,|beta|,u)=Pi_4$, \ $overline(v)="rd"_beta (S.mu,a)$, #h(3pt) $"undef" in.not overline(v)$],
    [$S tack "move"(p) #dE (overline(v), S[Pi |-> Pi_4])$]),
  ir(m-ref,
    [$S tack p #dP (⟨a,t,b,sz⟩, Pi_1)$, #h(3pt) $beta=Lambda(p)$, \ $|beta|=0$ or ($b$ live and $a+|beta| <= b+sz$), \ $"ref"(Pi_1,a,|beta|,t,k,c,"bytes"_beta (m))=(Pi_2,u)$],
    [$S tack "ref"(k,c,m,p) #dE$ \ $quad (["ptr"(b,a-b,|beta|,sz,u)], S[Pi |-> Pi_2])$]),
  ir(m-assgn,
    [$P(S.i) = (d := e)$, #h(3pt) $beta=Lambda(d)$, #h(3pt) $"prepare"(S,d)=S_1$, \ $S_1 tack e #dE (overline(v), S_2)$, #h(3pt) $S_2 tack d #dP (⟨a,t,b,sz⟩, Pi_3)$, #h(3pt) $b$ live, \ $a+|beta| <= b+sz$, #h(3pt) $"useMut"(Pi_3,a,|beta|,t)=Pi_4$, \ $"wr"_beta (S_2.mu,a,overline(v))=mu'$],
    [$S smir$ \ $quad (S.i+1, thick S_2.E, thick mu', thick Pi_4)$]),
  ir(m-halt,
    [$P(S.i) = "halt"$ or $P(S.i)=bot$],
    [$S smir S$]),
) <tab:mir>

*Place resolution ($#dP$).* The judgment
$S tack p #dP (⟨a,t,b,sz⟩,Pi')$ reads: in state $S$, the well-typed
place $p$ resolves to $⟨a,t,b,sz⟩$, and the permission state becomes
$Pi'$. The four components of a _resolved place_ are the address $a$ the
place denotes, the tag $t$ through which it is to be accessed, and the
base $b$ and size $sz$ of the allocation it lies in. It is to a place what
a list of values is to an expression, the result of evaluating it, and it
is never stored. The state is on the left because resolution consults all
of it: the environment for a local, memory and permissions for a
dereference. It does not write memory, but it can change the permission
state. #m-local reads the environment. #m-proj is typed address
arithmetic in bytes: it preserves provenance, bounds, and permissions.
#m-deref changes provenance, because the pointer _value_, not the place
holding it, identifies the referent; loading that value is an eight-byte
`read` through the tag of the place that holds it, and all eight bytes
must lie inside the allocation. Nested dereferences thread these
permission changes from the inside out. A separate _pure lookup_,
$"lookup"(S,p)$, follows the same address calculation but only decodes the
pointer bytes, with neither a bounds check nor a `read`. It is used only
to decide whether an assignment root must be allocated.

*Expression evaluation ($#dE$).* The judgment
$S tack e #dE (overline(v),S')$ produces one value per leaf of the
expression's layout. #m-copy and #m-ref resolve their place and then act on
its entire byte range: one `read`, or one `ref`, of width $|beta|$. A copy
that would read an uninitialized leaf is undefined behavior, as in Miri.
#m-move reads through a mutable borrow of the range that it retires at
once. The pointer built by #m-ref carries the fresh tag $u$, the
allocation's base and size, and the referent's size as its extent, so
later bounds checks are against the whole allocation. A reference to a
zero-sized place touches no byte: as in Miri, it needs no live, in-bounds
memory, so it may be formed through a dangling pointer.

*Interpreter ($smir$).* A step fetches $P(i)$. #m-assgn runs four phases in
a fixed order: prepare the destination's root, evaluate the expression,
resolve the destination, write. Preparation (#m-pbound, #m-palloc) allocates
the root local of $d$ when it is unbound: the bump allocator returns a
fresh base $b$ aligned to the layout's alignment, `own` a fresh tag $t$
over its $|beta|$ bytes, and $E$ is extended. A destination rooted through
a dereference is never allocated implicitly; that case is an error.
Crucially, _the whole expression is evaluated before the destination is
resolved_. Hence $"copy"(p)$ materializes its values before a destination
access can invalidate a tag that $p$ needs. The write encodes the values
at the _destination's_ layout and validates a `useMut` over its whole
range, padding included. The conclusion takes its environment from $S_2$,
the state after the expression, so allocation during preparation and any
effect of the expression survive. We write
$S attach(arrow.r.double.long, t: P, b: n) S'$ for $n$ steps; `halt` and a
missing statement are fixed points (#m-halt), so extra fuel is harmless.

*Example.* The running program of this paper declares a nested tuple $x$
and a pointer $y$, and is small enough to execute by hand:

#align(center, box(width: 74%, listing(
  [MIRLITE #h(6pt) $Gamma = [x : ("u64",("u64","u64")), thick y : "Ptr" "u64"]$],
  [
    0: #h(3pt) $x.0 := "const"(5)$ \
    1: #h(3pt) $x.1.0 := "const"(42)$ \
    2: #h(3pt) $y := "ref"("mutable", "false", [], x.1.0)$ \
    3: #h(3pt) $#dr y := "const"(7)$ \
    4: #h(3pt) $"halt"$
  ],
)))

Here `u64` is $"Int"(64,"false")$, and $Lambda$ is the C layout: $x$ is
$beta_x = "tup"(["int"(8), "tup"(["int"(8),"int"(8)],[0,8],16,8)],[0,8],24,8)$,
24 bytes with $x.1.0$ at byte offset $8+0=8$, and $y$ is
$"ptr"("int"(8))$. Statement 0 allocates $x$, because an assignment to an
unbound root allocates it. Statement 1 writes the eight bytes of $x.1.0$ in
the middle of $x$; it is the statement for which the compiler of
@sec:compiler must introduce, and then retire, a tag the source never sees.
Statement 2 allocates $y$ and stores a mutable reference to the field just
written. Statement 3 writes through that reference. Execution starts from
the empty state: the bump allocator's watermark is 1, so that no
allocation is ever at address 0, and tags are minted from 1 upward, tag 0
being reserved (@sec:surface-perm). The program thus touches 32 bytes: $x$
occupies $[8,32)$, its base aligned up to 8, and $y$ occupies $[32,40)$.
All concrete addresses, tags, registers, and labels in this section are
those of the mechanized semantics running this program.

#statetable(
  [The MIRLite configuration after every statement of the running program. A column is one leaf, eight bytes: its decoded value over the borrow stack that each of its bytes carries (the eight are equal throughout this run). "---" is unallocated memory, shading marks what the statement changed, and "next" is $Pi."NextTag"$.],
  ([after statement], [$E$], [$[8,16)$ \ #plc[$x.0$]], [$[16,24)$ \ #plc[$x.1.0$]], [$[24,32)$ \ #plc[$x.1.1$]], [$[32,40)$ \ #plc[$y$]], [next]),
  (24%, 11%, 11%, 17%, 11%, 19%, 7%),
  placement: none,
  size: 7pt,
  pad: 2.4pt,
  ([_initially_], [---], [#nocell], [#nocell], [#nocell], [#nocell], [1]),
  ([0: #h(3pt) $x.0 := "const"(5)$], table.cell(fill: chg)[$x |-> (8,1)$], table.cell(fill: chg)[$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], table.cell(fill: chg)[2]),
  ([1: #h(3pt) $x.1.0 := "const"(42)$], [$x |-> (8,1)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(42)$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], [2]),
  ([2: #h(3pt) $y := "ref"("mutable",dots,x.1.0)$], table.cell(fill: chg)[$x |-> (8,1)$ \ $y |-> (32,2)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(42)$ \ #stk[$["MutRef"(3),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"ptr"(8,8,8,24,3)$ \ #stk[$["Own"(2)]$]], table.cell(fill: chg)[4]),
  ([3: #h(3pt) $#dr y := "const"(7)$], [$x |-> (8,1)$ \ $y |-> (32,2)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(7)$ \ #stk[$["MutRef"(3),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"ptr"(8,8,8,24,3)$ \ #stk[$["Own"(2)]$]], [4]),
  ([4: #h(3pt) $"halt"$], [$x |-> (8,1)$ \ $y |-> (32,2)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"word"(7)$ \ #stk[$["MutRef"(3),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"ptr"(8,8,8,24,3)$ \ #stk[$["Own"(2)]$]], [4]),
) <tab:mir-example>

@tab:mir-example gives the whole configuration after each statement; the
program counter, not shown, is $k+1$ after statement $k$, and `halt`
leaves it at 4. Read a row against the one above it: the shaded entries
are exactly what the rules below change.

#walk(
  ([0], [$x$ is unbound, so #m-palloc allocates the 24 bytes $[8,32)$, binds
    $x |-> (8,1)$, and #sb-own gives each byte the stack $["Own"(1)]$.
    #m-const produces $["word"(5)]$. #m-local and #m-proj resolve $x.0$ to
    $⟨8,1,8,24⟩$. #m-assgn validates a `useMut` of the eight bytes $[8,16)$
    through tag 1, which #sb-use accepts without changing the stacks, and
    encodes 5 there; bytes $[16,32)$ stay uninitialized and decode to
    `undef`.]),
  ([1], [Preparation is #m-pbound: nothing is allocated. Two applications of
    #m-proj resolve $(x.q_1).q_0$ to $⟨16,1,8,24⟩$: offset 8 for field 1,
    then 0 for its field 0. #m-assgn writes the bytes $[16,24)$ through the
    owner's tag. There is no source retag, so their stacks do not change,
    and the sibling $x.1.1$, bytes $[24,32)$, is untouched.]),
  ([2], [#m-palloc allocates $y$ at address 32 with owning tag 2, _before_
    the expression is evaluated. #m-ref resolves $x.1.0$ as in statement 1,
    and #sb-refm pushes $"MutRef"(3)$ on its eight bytes only. The pointer
    $"ptr"(8,8,8,24,3)$, to address 16 with extent 8, is encoded into
    $[32,40)$: the little-endian bytes of 16, each carrying the provenance
    $(8,24,8,3)$. The tag counter moves from 2 to 4: one tag for $y$, one
    for the reference.]),
  ([3], [#m-deref resolves $y$ to $⟨32,2,32,8⟩$, performs an eight-byte
    `read` of $[32,40)$ through tag 2 (#sb-read, which changes nothing
    here), decodes the pointer, and returns $⟨16,3,8,24⟩$, the address and
    tag _loaded from memory_. #m-assgn writes 7 through tag 3, which is on
    top of the stacks of $[16,24)$, so they do not change either.]),
  ([4], [#m-halt: the configuration is a fixed point.]),
)

#source([Formalization of the typed syntax, values, and source transition system: `src/obseq3/syntax.lean`, `src/obseq3/values.lean`, and `src/obseq3/mirlite.lean`; bytes and layouts: `src/obseq3/bytemem.lean` and `src/obseq3/bytelayout.lean`.])

== OSEA-IR <sec:oseair>

#grammarfig(
  [Grammar and semantic domains of OSEA-IR (left, top right), and the state of the compiler (bottom right). Bytes $alpha$, byte layouts $beta$, and masks are those of @fig:mir-grammar. @fig:surface-grammar has the remaining instructions.],
  panel([Terms], bnf(
    defn($"Program" in.rev Q$, $NN harpoon.rt "Instr"$),
    prod($"Instr" in.rev I$, $r := h$, $"store"_beta (r_s, r_p)$, $"storec"_beta (overline(v), r_p)$, $"die"(r, n)$, $"halt"$),
    prod($"Rhs" in.rev h$, $"load"_beta (r)$, $"alloc"_beta$, $"borrow"(k,c,m,n,r,delta)$),
    prod($"Register" in.rev r$, $"R"_0 | "R"_1 | dots$),
  )),
  [
    #panel([Semantic domains], bnf(
      defn($"State" in.rev T$, $NN times "RegFile" times "Mem" times "Perm"$),
      defn($"RegFile" in.rev R$, $"Register" harpoon.rt "Value"^*$),
      defn($"Mem" in.rev mu$, $(NN arrow.r "Byte") times "Allocs" times NN times NN^*$),
      prod($"Value" in.rev v$, $"undef" thick | thick "dat"(w)$, $"ptr"(b,o,e,sz,t)$),
    ))
    #panel([Compiler state], bnf(
      defn($"CState" in.rev C$, $NN times NN times "Code" times "LocalMap"$),
      defn($"Code" in.rev K$, $NN harpoon.rt "Instr"$),
      defn($"LocalMap" in.rev L$, $"Local" harpoon.rt "Register" times "Layout"$),
      defn($"Cleanup" in.rev D$, $("Register" times NN)^*$),
    ))
  ],
) <fig:oseair-grammar>

OSEA-IR is a register machine that exposes the memory and permission events
implicit in a MIRLite statement (@fig:oseair-grammar). A source place is
gone: an instruction names a register holding a concrete pointer, a byte
offset, and a number of bytes. Consequently one source step may need
several target steps and may create short-lived tags with no source
counterpart. A program $Q$ is a _partial_ map from labels to instructions,
which lets the compiler extend code without renumbering an earlier
fragment. Instructions are register assignments $r := h$, stores of a
register or of a constant through a pointer, the retirement `die` of a
borrow, and `halt`. A right-hand side $h$ loads through a pointer,
allocates, or borrows. Every load, store, and allocation carries the byte
layout of what it moves, so the target knows where each leaf lies exactly
as the source does.

*Semantic domains.* Target values mirror source values one to one, with
`dat` for a machine word; the pointer fields have the same meaning as at
the source. A register holds a list of values, one per leaf of what was
loaded into it; the register file is a finite shadowing map. Memory is the
same byte memory as at the source, read and written with the same
$"rd"_beta$ and $"wr"_beta$, and the permission state is the same Stacked
Borrows instance. A target state is $T=(j,R,mu,Pi)$. @tab:osea gives the
rules.

#ruletable(
  [OSEA-IR semantics. $T.R$, $T.mu$, and $T.Pi$ are components of a state $T=(j,R,mu,Pi)$, and $T[dots |-> dots]$ replaces components, as in @tab:mir; the instruction rules write the state out as a tuple instead. $Q$ is the program being run. Every rule that reads a pointer from $R(r)$ requires the register to hold exactly one pointer; "$b$ live" is as in @tab:mir.],
  ir(t-load,
    [$T.R(r)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $a=b+o$, #h(3pt) $b$ live, \ $a+|beta| <= b+sz$, #h(3pt) $"read"(T.Pi,a,|beta|,t)=Pi'$, \ $overline(v)="rd"_beta (T.mu,a)$, #h(3pt) $"undef" in.not overline(v)$],
    [$T tack "load"_beta (r) #dH (overline(v), T[Pi |-> Pi'])$]),
  ir(t-alloc,
    [$"alloc"(T.mu,|beta|,"al"(beta))=(b,mu')$, \ $"own"(T.Pi,b,|beta|)=(Pi',u)$],
    [$T tack "alloc"_beta #dH$ \ $quad (["ptr"(b,0,|beta|,|beta|,u)], T[mu |-> mu', Pi |-> Pi'])$]),
  ir(t-borrow,
    [$T.R(r)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $a=b+o+delta$, \ $n=0$ or ($b$ live and $a+n <= b+sz$), \ $"ref"(T.Pi,a,n,t,k,c,m)=(Pi',u)$],
    [$T tack "borrow"(k,c,m,n,r,delta) #dH$ \ $quad (["ptr"(b,o+delta,n,sz,u)], T[Pi |-> Pi'])$]),
  ir(t-assgn,
    [$Q(j) = (r := h)$, \ $(j,R,mu,Pi) tack h #dH (overline(v), (j,R,mu_1,Pi_1))$],
    [$(j,R,mu,Pi) ssea$ \ $quad (j+1, R[r |-> overline(v)], mu_1, Pi_1)$]),
  ir(t-store,
    [$Q(j) = "store"_beta (r_s,r_p)$, #h(3pt) $R(r_s)=overline(v)$, \ $R(r_p)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $a=b+o$, #h(3pt) $b$ live, \ $a+|beta| <= b+sz$, #h(3pt) $"useMut"(Pi,a,|beta|,t)=Pi'$, \ $"wr"_beta (mu,a,overline(v))=mu'$],
    [$(j,R,mu,Pi) ssea (j+1, R, mu', Pi')$]),
  ir(t-storec,
    [$Q(j) = "storec"_beta (overline(v),r_p)$, \ $R(r_p)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $a=b+o$, #h(3pt) $b$ live, \ $a+|beta| <= b+sz$, #h(3pt) $"useMut"(Pi,a,|beta|,t)=Pi'$, \ $"wr"_beta (mu,a,overline(v))=mu'$],
    [$(j,R,mu,Pi) ssea (j+1, R, mu', Pi')$]),
  ir(t-die,
    [$Q(j) = "die"(r,n)$, #h(3pt) $R(r)=["ptr"(b,o,e,sz,t)]$, \ $"die"(Pi,b+o,n,t)=Pi'$],
    [$(j,R,mu,Pi) ssea (j+1, R, mu, Pi')$]),
  ir(t-halt,
    [$Q(j) = "halt"$ or $Q(j)=bot$],
    [$T ssea T$]),
) <tab:osea>

*RHS evaluation ($#dH$).* The judgment
$T tack h #dH (overline(v),T')$ evaluates a right-hand side to a list of
values and a state. It may update memory or permissions but does not
advance $j$. #t-load checks liveness and the complete byte range, reads it
through the pointer's tag, and decodes it leaf by leaf, failing on an
uninitialized leaf exactly as #m-copy does. #t-borrow retags $n$ bytes at
offset $delta$ from the pointer and returns the same pointer, moved by
$delta$, claiming $n$ bytes, and carrying the fresh tag; like #m-ref it checks
liveness and bounds only when $n != 0$; offsets are
natural numbers, so there is no negative-offset case. #t-alloc is the only
rule of the main text that changes both memory and permissions.

*Interpreter ($ssea$).* #t-assgn evaluates its right-hand side _before_
inserting the returned entry. The two stores share one write-through-pointer
helper: extract one pointer from $r_p$, check liveness and the range,
`useMut`, encode, advance. They differ in where the values come from: a
register for #t-store, the instruction for #t-storec. The encoding is the
store's layout, so a store whose values do not fit its leaves fails.
#t-die has no separate range check: its admissibility is exactly that of
the permission operation. There is no global well-formedness premise on
register files; the instruction that consumes a register checks the shape
it needs, which keeps malformed programs executable with explicit errors.
We write $T attach(arrow.r.double.long, t: Q, b: n) T'$ for exactly $n$
steps. Iteration does not stop early at a fixed point (#t-halt), which
makes the target step count of the simulation existential without a
separate reflexive-transitive closure.

*Example.* @tab:osea-example executes the code the compiler emits for the
running program (@fig:compile-example), one group of labels per source
statement. Compare each group's last row with the corresponding row of
@tab:mir-example: the bytes agree, the stacks agree up to the tags, and the
tag counter runs ahead.

#statetable(
  [The OSEA-IR configuration after every instruction of the compiled running program, in the format of @tab:mir-example (memory leaves decoded as there). The $R$ column shows the binding the instruction adds; registers are never removed, so the register file is the union of the rows above. After label $k$ the program counter is $k+1$. $beta_x$ is $x$'s layout, $"i8"$ abbreviates $"int"(8)$; $"mut"$ abbreviates $"mutable","false"$ with a mask that marks no byte. Labels 0--1, 2--4, 5--7, 8--9, and 10 are source statements 0 to 4.],
  ([after instruction], [$R$ gains], [$[8,16)$ \ #plc[$x.0$]], [$[16,24)$ \ #plc[$x.1.0$]], [$[24,32)$ \ #plc[$x.1.1$]], [$[32,40)$ \ #plc[$y$]], [next]),
  (28%, 18%, 8%, 16%, 8%, 16%, 6%),
  size: 7pt,
  placement: none,
  ([_initially_], [---], [#nocell], [#nocell], [#nocell], [#nocell], [1]),
  ([0: #h(3pt) $"R"_0 := "alloc"_(beta_x)$], table.cell(fill: chg)[$"R"_0 |-> "ptr"(8,0,24,24,1)$], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], table.cell(fill: chg)[2]),
  ([1: #h(3pt) $"storec"_"i8" (["dat"(5)], "R"_0)$], [---], table.cell(fill: chg)[$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], [2]),
  ([2: #h(3pt) $"R"_1 := "borrow"("mut",8,"R"_0,8)$], table.cell(fill: chg)[$"R"_1 |-> "ptr"(8,8,8,24,2)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["MutRef"(2),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], table.cell(fill: chg)[3]),
  ([3: #h(3pt) $"storec"_"i8" (["dat"(42)], "R"_1)$], [---], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(42)$ \ #stk[$["MutRef"(2),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], [3]),
  ([4: #h(3pt) $"die"("R"_1, 8)$], [---], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(42)$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [#nocell], [3]),
  ([5: #h(3pt) $"R"_2 := "alloc"_("ptr"("i8"))$], table.cell(fill: chg)[$"R"_2 |-> "ptr"(32,0,8,8,3)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"word"(42)$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"undef"$ \ #stk[$["Own"(3)]$]], table.cell(fill: chg)[4]),
  ([6: #h(3pt) $"R"_3 := "borrow"("mut",8,"R"_0,8)$], table.cell(fill: chg)[$"R"_3 |-> "ptr"(8,8,8,24,4)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(42)$ \ #stk[$["MutRef"(4),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(3)]$]], table.cell(fill: chg)[5]),
  ([7: #h(3pt) $"store"_("ptr"("i8")) ("R"_3, "R"_2)$], [---], [$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"word"(42)$ \ #stk[$["MutRef"(4),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"ptr"(8,8,8,24,4)$ \ #stk[$["Own"(3)]$]], [5]),
  ([8: #h(3pt) $"R"_4 := "load"_("ptr"("i8")) ("R"_2)$], table.cell(fill: chg)[$"R"_4 |-> "ptr"(8,8,8,24,4)$], [$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"word"(42)$ \ #stk[$["MutRef"(4),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"ptr"(8,8,8,24,4)$ \ #stk[$["Own"(3)]$]], [5]),
  ([9: #h(3pt) $"storec"_"i8" (["dat"(7)], "R"_4)$], [---], [$"word"(5)$ \ #stk[$["Own"(1)]$]], table.cell(fill: chg)[$"word"(7)$ \ #stk[$["MutRef"(4),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"ptr"(8,8,8,24,4)$ \ #stk[$["Own"(3)]$]], [5]),
  ([10: #h(3pt) $"halt"$], [---], [$"word"(5)$ \ #stk[$["Own"(1)]$]], [$"word"(7)$ \ #stk[$["MutRef"(4),"Own"(1)]$]], [$"undef"$ \ #stk[$["Own"(1)]$]], [$"ptr"(8,8,8,24,4)$ \ #stk[$["Own"(3)]$]], [5]),
) <tab:osea-example>

#walk(
  ([0--1], [#t-alloc allocates $[8,32)$ and issues #sb-own, so $"R"_0$ holds
    the owner's pointer with tag 1. #t-storec encodes 5 into $[8,16)$
    through it. The state equals the source's after statement 0.]),
  ([2--4], [One source write takes three instructions, and their permission
    trace is @fig:sb-example at every byte of $[16,24)$, with $t=1$ and
    $u=2$. #t-borrow issues #sb-refm on those eight bytes alone and mints
    tag 2; #t-storec writes through tag 2; #t-die issues #sb-die, after
    which their stacks are again $["Own"(1)]$. The memory and the stacks
    now equal the source's after statement 1, but the tag counter is 3
    where the source's is 2.]),
  ([5--7], [#t-alloc allocates $y$, #t-borrow mints the reference, and
    #t-store stores it. Because the counter ran ahead, $y$'s owning tag is
    3 here and 2 at the source, and the stored reference carries tag 4 here
    and 3 at the source: the bytes of $[32,40)$ are the same address bytes
    on both sides, with provenance tags 4 and 3.]),
  ([8--9], [#t-load reads $[32,40)$ through tag 3 and leaves
    $"ptr"(8,8,8,24,4)$ in $"R"_4$; #t-storec writes $[16,24)$ through the
    loaded tag 4.]),
  ([10], [#t-halt. $"R"_1$ still holds a pointer with the dead tag 2;
    registers are not observable, so the simulation of @sec:correctness
    ignores it.]),
)

#source([Formalization of target values, RHS evaluation, instruction stepping, and fuelled execution: `src/obseq3/oseair.lean` (registers and values: `src/obseq3/values.lean`).])

== Compiler <sec:compiler>

The compiler is a state-passing translation from typed MIRLite syntax to
OSEA-IR code, parameterized by the layout environment $Lambda$ the source
runs on. Its obligation is to preserve the source evaluation order while
introducing explicit loads, retags, stores, and the retirement of the tags
it introduces. A compiler state is $C=(n_r,n_l,K,L)$
(@fig:oseair-grammar, bottom right): $n_r$ and $n_l$ are the next fresh
register and label, $K$ is the emitted code map, and $L$ maps a source
local to a register and its layout type. Write $C emit [I_0,dots,I_(n-1)]$
for the state that installs the list at labels $[n_l, n_l+n)$ and advances
$n_l$ by $n$, and "$r$ fresh in $C$" for $r="R"_(n_r)$ with $n_r$
advanced. Every compiler computation is monotone: counters do not
decrease, code below the old $n_l$ is unchanged, and every old entry of $L$
remains. A cleanup list $D$ records borrows to retire; $"cleanup"(D)$
reverses $D$ and maps each entry $(r,n)$ to $"die"(r,n)$. @tab:compile
gives the rules; every offset and length in them is in bytes and comes
from $Lambda$.

#ruletable(
  [Compilation rules. $"root"(d)$ is the local reached from $d$ through projections and dereferences. In #c-proj0 and #c-projd the base $b$ is not itself a projection (#c-assoc applies first). $beta_d = Lambda(d)$ is the destination's layout; #c-ref passes $m' = "bytes"_(Lambda(p))(m)$.],
  cols: (40%, 46%, 14%),
  ir(c-rbound,
    [$"root"(d)=ell$, #h(3pt) $L(ell)$ defined],
    [$C tack "root"(d) arrow.r C$]),
  ir(c-ralloc,
    [$"root"(d)=ell:tau$, #h(3pt) $L(ell)=bot$, #h(3pt) $r$ fresh in $C$],
    [$C tack "root"(d) arrow.r$ \ $quad (C emit [r := "alloc"_(Lambda(ell))])[L(ell) |-> (r,tau)]$]),
  ir(c-local,
    [$L(ell)=(r,tau)$],
    [$C scripts(tack)_k ell #dCP (r, [], C)$]),
  ir(c-assoc,
    [$C scripts(tack)_k b.(q dot p) #dCP (r, D, C')$],
    [$C scripts(tack)_k (b.q).p #dCP (r, D, C')$]),
  ir(c-proj0,
    [$"off"_Lambda (b,q)=0$, #h(3pt) $C scripts(tack)_k b #dCP (r_b, D_b, C')$],
    [$C scripts(tack)_k b.q #dCP (r_b, D_b, C')$]),
  ir(c-projd,
    [$delta="off"_Lambda (b,q)>0$, #h(3pt) $n=|Lambda(b.q)|$, \ $C scripts(tack)_k b #dCP (r_b, D_b, C_1)$, #h(3pt) $r_f$ fresh in $C_1$, \ $I = (r_f := "borrow"(k,"false",[],n,r_b,delta))$],
    [$C scripts(tack)_k b.q #dCP$ \ $quad (r_f, D_b plus.double [(r_f,n)], C_1 emit [I])$]),
  ir(c-deref,
    [$C scripts(tack)_"shared" p #dCP (r_p, D_p, C_1)$, #h(3pt) $r$ fresh in $C_1$],
    [$C scripts(tack)_k #dr p #dCP (r, [],$ \ $quad C_1 emit [r := "load"_("ptr"(Lambda(#dr p))) (r_p)] emit "cleanup"(D_p))$]),
  ir(c-blocal,
    [$L(ell)=(r_b,tau)$, #h(3pt) $r$ fresh in $C$],
    [$C scripts(tack)_(k,c,m) ell #dCB$ \ $quad (r, C emit [r := "borrow"(k,c,m,|Lambda(ell)|,r_b,0)])$]),
  ir(c-bproj,
    [$C scripts(tack)_k b #dCP (r_b, D_b, C_1)$, #h(3pt) $r$ fresh in $C_1$],
    [$C scripts(tack)_(k,c,m) b.q #dCB (r, C_1 emit$ \ $quad [r := "borrow"(k,c,m,|Lambda(b.q)|,r_b,"off"_Lambda (b,q))])$]),
  ir(c-bderef,
    [$C scripts(tack)_"shared" p #dCP (r_p, D_p, C_1)$, \ $r_l, r$ fresh in $C_1$],
    [$C scripts(tack)_(k,c,m) #dr p #dCB (r, C_1 emit [r_l := "load"_("ptr"(Lambda(#dr p))) (r_p)]$ \ $quad emit "cleanup"(D_p) emit [r := "borrow"(k,c,m,|Lambda(#dr p)|,r_l,0)])$]),
  ir(c-const,
    [],
    [$C tack "const"(w) #dCR$ \ $quad (lambda r_d. ["storec"_(beta_d) (["dat"(w)], r_d)], C)$]),
  ir(c-copy,
    [$C scripts(tack)_"shared" p #dCP (r_s, D_s, C_1)$, #h(3pt) $r_v$ fresh in $C_1$],
    [$C tack "copy"(p) #dCR (lambda r_d. ["store"_(beta_d) (r_v, r_d)],$ \ $quad C_1 emit [r_v := "load"_(Lambda(p)) (r_s)] emit "cleanup"(D_s))$]),
  ir(c-move,
    [$C scripts(tack)_("mutable","false",[]) p #dCB (r_m, C_1)$, \ $r_v$ fresh in $C_1$],
    [$C tack "move"(p) #dCR (lambda r_d. ["store"_(beta_d) (r_v, r_d)],$ \ $quad C_1 emit [r_v := "load"_(Lambda(p)) (r_m), "die"(r_m,|Lambda(p)|)])$]),
  ir(c-ref,
    [$C scripts(tack)_(k,c,m') p #dCB (r_v, C_1)$],
    [$C tack "ref"(k,c,m,p) #dCR$ \ $quad (lambda r_d. ["store"_(beta_d) (r_v, r_d)], C_1)$]),
  ir(c-assign,
    [$C tack "root"(d) arrow.r C_1$, #h(3pt) $C_1 tack e #dCR (F, C_2)$, \ $C_2 scripts(tack)_"mutable" d #dCP (r_d, D_d, C_3)$],
    [$C tack d := e sC$ \ $quad C_3 emit F(r_d) emit "cleanup"(D_d)$]),
  ir(c-halt,
    [],
    [$C tack "halt" sC C emit ["halt"]$]),
  ir(c-pempty,
    [],
    [$C tack [] sPr C$]),
  ir(c-pstep,
    [$C tack s sC C_1$, #h(3pt) $C_1 tack P sPr C'$],
    [$C tack s :: P sPr C'$]),
) <tab:compile>

*Establishing roots.* Writing an unbound root must mirror source
preparation. #c-rbound emits nothing; #c-ralloc allocates the root local of
the destination at its byte layout and records its register. For a
dereference the root is the pointer local. The source never allocates a
pointee implicitly and fails instead, so a forward simulation never
observes that case. Read lowering does not allocate a missing local:
resolving a read requires that the root already exist, and the compiler is
_checked_, returning an error for such a program.

*Place-to-register compilation ($#dCP$).* The judgment
$C scripts(tack)_k p #dCP (r,D,C')$ lowers place $p$, leaves a pointer to
it in $r$, and returns a cleanup list. Its index $k$ is the retag kind of
any borrow the lowering emits: reads lower their place with $k="shared"$
and assignment destinations with $k="mutable"$. #c-local is a lookup. A
zero-offset projection reuses the base pointer (#c-proj0): it denotes the
same address and needs no narrower pointer. A projection at a nonzero byte
offset emits a borrow of the _final selected size_ (#c-projd). A
dereference loads the eight-byte pointer (#c-deref) and retires the
borrows that were needed to reach it, but it returns an empty cleanup
list: the loaded tag belongs to the source program and must not be
retired.

#definition("Route borrow")[
  A _route borrow_ is the `borrow` instruction emitted by #c-projd to
  obtain a pointer to a projected subregion of a place that the compiled
  code already holds a pointer to. Its fresh tag is a _route tag_. A route
  borrow is unprotected, has an empty mask, and spans exactly the bytes of
  the layout selected by the place. Its register and size are recorded as
  an entry $(r,n)$ of the cleanup list $D$, and the tag is retired by
  $"die"(r,n)$ before the next source-statement boundary. A route tag is
  never stored to memory by the compiled code and has no source
  counterpart.
] <def:route>

Route tags are the only tags the compiled code mints that the source does
not, apart from the borrow that #c-move retires within the same statement,
as the source does. Every other target retag corresponds to a source `ref`
and produces a tag that the source program also stores.

*Reassociation.* A place may contain nested projections, but emitting a
borrow for each syntactic layer would change the accessed ranges. #c-assoc
reassociates adjacent paths before any borrow is emitted: for
$q:sigma_0 arrow.r sigma$ and $p:sigma arrow.r tau$ the composed path
$q dot p : sigma_0 arrow.r tau$ selects the same field, and
$"off"_Lambda (b,q dot p) = "off"_Lambda (b,q) + "off"_Lambda (b.q,p)$.
Reassociation stops at a dereference, because an offset cannot be moved
across a memory-loaded pointer. For $x.1.0$, lowering without #c-assoc
would borrow the sixteen-byte field $x.1$ and then reuse its zero-offset
subfield, retagging $[16,32)$. With it, the compiler emits one eight-byte
borrow at the composed offset 8 and leaves the sibling $x.1.1$ alone.

*Escaping borrows ($#dCB$).* Reference formation needs the distinct
judgment $C scripts(tack)_(k,c,m) p #dCB (r,C')$. It follows the same path
reassociation but _always_ ends in a $"borrow"(k,c,m,|beta|,dots)$,
including at offset zero (#c-blocal, #c-bproj), and for a dereference it
first loads the stored pointer and then borrows the pointed-to range
(#c-bderef). Its final tag is not a route tag and is never retired: it
escapes in the pointer value the program stores, and the correctness proof
extends the source-to-target tag map with it. The mask a reference carries
is the source's, expanded to one entry per byte.

*Expression-to-instructions compilation ($#dCR$).*
The judgment $C tack e #dCR (F,C')$ emits all the work that precedes the
destination and returns a _store function_ $F$ that awaits the destination
register. #c-const emits nothing. #c-copy materializes the copied values in
a register _before_ the destination is lowered. This is what realizes the
source rule's order, evaluate, then resolve the destination, then write,
when both resolutions have observable permission effects. #c-move does the
same through a mutable borrow that it retires after the load, the events
of #m-move. #c-ref retains the escaping tag. Every store is at the
destination's layout $beta_d$, as the source writes at it. Every
expression of the full language has the same shape (@sec:surface).

*Compilation judgments ($sC$, $sPr$).* #c-assign is the only assignment
rule, for every destination: the emitted intervals concatenate as

#align(center)[
#box(width: 98%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"root"(d) ; quad "pre-code of" e ; quad "lowering of" d ; quad F(r_d) ; quad "cleanup"(D_d).$
]]

#c-pempty and #c-pstep fold statement compilation from left to right from
the initial state $C_"init"=(0,0,emptyset,emptyset)$; the target program is
the final code map, or the first compiler error. For source statement
index $i$, compiling the prefix $P[0..i)$ from $C_0$ produces a state $C_i$
whose next label $C_i.n_l$ is the target entry label of statement $i$.
Monotonicity gives the two facts simulation needs,

#align(center)[
  $C_i.n_l <= C_(i+1).n_l quad and quad
  forall j<C_i.n_l. thick C_(i+1).K(j)=C_i.K(j),$
]

so compiling later statements cannot change a fragment already emitted. No
fixed instruction-per-statement ratio is assumed.

#figure(
  kind: image,
  caption: [Compilation of the running program. Each row is one source statement and the labelled instructions emitted for it; $"i8"$ abbreviates $"int"(8)$, and $[0]^8$ is the mask that marks none of the eight bytes.],
  {
    set text(size: 7.6pt)
    set par(first-line-indent: 0pt, justify: false, leading: 0.5em)
    let hd(t) = text(font: "Libertinus Sans", size: 6.4pt, weight: "semibold", fill: accent, upper(t))
    table(
      columns: (40%, 60%),
      align: left + horizon,
      inset: (x: 5pt, y: 3.4pt),
      stroke: (x, y) => (
        top: if y > 0 { 0.45pt + rule } else { none },
        left: if x == 0 { 1.5pt + accent } else { 0.45pt + rule },
      ),
      fill: (x, y) => if y == 0 { none } else { rgb("f7f7f7") },
      hd[MIRLite], hd[OSEA-IR],
      [0: #h(3pt) $x.0 := "const"(5)$],
      [0: #h(3pt) $"R"_0 := "alloc"_(beta_x)$ \ 1: #h(3pt) $"storec"_"i8" (["dat"(5)], "R"_0)$],
      [1: #h(3pt) $x.1.0 := "const"(42)$],
      [2: #h(3pt) $"R"_1 := "borrow"("mutable","false",[],8,"R"_0,8)$ \ 3: #h(3pt) $"storec"_"i8" (["dat"(42)], "R"_1)$ \ 4: #h(3pt) $"die"("R"_1, 8)$],
      [2: #h(3pt) $y := "ref"("mutable","false",[],x.1.0)$],
      [5: #h(3pt) $"R"_2 := "alloc"_("ptr"("i8"))$ \ 6: #h(3pt) $"R"_3 := "borrow"("mutable","false",[0]^8,8,"R"_0,8)$ \ 7: #h(3pt) $"store"_("ptr"("i8")) ("R"_3, "R"_2)$],
      [3: #h(3pt) $#dr y := "const"(7)$],
      [8: #h(3pt) $"R"_4 := "load"_("ptr"("i8")) ("R"_2)$ \ 9: #h(3pt) $"storec"_"i8" (["dat"(7)], "R"_4)$],
      [4: #h(3pt) $"halt"$],
      [10: #h(3pt) $"halt"$],
    )
  },
) <fig:compile-example>

*Example.* We compile the running program from $C_"init"$
(@fig:compile-example), tracking $(n_r,n_l,L)$. Statement 0: $L(x)=bot$, so
#c-ralloc emits label 0, an allocation at $beta_x=Lambda(x)$, and sets
$L(x)=("R"_0,tau_x)$; #c-const has no pre-code; $x.0$ has byte offset
zero, so #c-proj0 and #c-local return $("R"_0,[])$ and emit nothing;
$F("R"_0)$ is label 1, a store at the destination's layout $"int"(8)$. The
state is $(1,2,{x |-> "R"_0})$. Statement 1: #c-rbound\; #c-assoc rewrites
$(x.q_1).q_0$ to $x.(q_1 dot q_0)$ with byte offset $8+0=8$ and selected
size $|"int"(8)|=8$; #c-projd emits the route borrow at label 2 and
returns $("R"_1,[("R"_1,8)])$; the store is label 3; the cleanup is label
4. Every number is derived: the layout gives the offset and the borrow
size, the destination's layout the store, and reversing the singleton
cleanup list gives the `die`. Statement 2: #c-ralloc emits label 5 for $y$
_before_ the expression, mirroring #m-palloc\; #c-ref uses #c-bproj, whose
borrow at label 6 has the shape of the route borrow of label 2, with the
source's empty mask expanded to eight bytes, but is recorded in no cleanup
list; label 7 stores it. There is no `die`. Statement 3: #c-deref lowers
$y$ by #c-local, emits the eight-byte pointer load at label 8, and returns
$("R"_4,[])$; label 9 stores through the loaded pointer. There is again no
`die`: retiring $"R"_4$'s tag would pop the program's own reference. The
final state is $(5,11,{x |-> "R"_0, y |-> "R"_2})$, and its code map is
the program that @tab:osea-example executes.

#source([Formalization of compiler state growth, checked lowering, and program compilation: `src/obseq3/compile.lean`. The listing of @fig:compile-example is the witness `g14_paper_running_example` in `src/obseq3/compile_tests.lean`.])

== Correctness <sec:correctness>

Correctness is a forward simulation of successful executions. Literal state
equality is impossible: the target has registers and introduces route
tags (@def:route). The relation instead compares source-observable memory,
local pointers, and permission stacks at source-statement boundaries. This
section defines exactly the machinery needed to state that relation
(@def:rename to @def:inv), states the simulation theorems (@thm:step to
@cor:uniform), and reads the running program as a simulation
(@tab:sim-example). The proofs are mechanized (@sec:mech) and are not
reproduced here.

=== Renaming and the byte relations

#definition("Tag renaming")[
  A _tag renaming_ is a partial map $rho_t:"Tag" arrow.r "option"("Tag")$.
  A renaming $rho'_t$ _extends_ $rho_t$, written $rho_t subset.eq rho'_t$,
  when $rho'_t$ agrees with $rho_t$ wherever $rho_t$ is defined.
] <def:rename>

The map is partial because future tags have not yet been created. Tags
genuinely require renaming: route borrows advance the target tag counter,
so a later source and target `ref` may mint different numeric tags.
Addresses, by contrast, are not renamed at all. Each machine allocates with
the same deterministic bump allocator, which never reuses an address, and
both start at the same watermark. The compiler emits exactly one target
allocation, of the same layout, for each source allocation, and in the same
order. Hence the allocators stay in lockstep (I4 below), and every block
has the same base, and every byte the same address, on both sides.

#definition("Byte and memory simulation")[
  Under $rho_t$, a source byte $alpha$ is simulated by a target byte
  $alpha'$, written $alpha approx alpha'$, when $alpha="uninit"$, or
  $alpha="init"(x,pi)$ and $alpha'="init"(x,pi')$ where either
  $pi=pi'=bot$ or $pi=(b,sz,e,t)$ and $pi'=(b,sz,e,t')$ with
  $rho_t (t)=t'$. Source memory $mu_s$ is simulated by target memory
  $mu_t$ when $mu_s (a) approx mu_t (a)$ at every address $a$, and the two
  allocators are in _lockstep_ when $mu_s$ and $mu_t$ have the same
  allocation table, the same watermark, and the same freed bases.
] <def:memsim>

The relation is forward only: an uninitialized source byte refines any
target byte, because a successful source run cannot observe it, and the
target may hold bytes the source never wrote. An initialized byte is the
same byte on both sides; only the tag of its provenance is renamed. Values
inherit the relation through decoding:

#definition("Value simulation")[
  Under $rho_t$, a source value $v$ is simulated by a target value $v'$,
  written $v approx v'$, when $v="word"(w)$ and $v'="dat"(w)$; or
  $v="ptr"(b,o,e,sz,t)$ and $v'="ptr"(b,o,e,sz,t')$ with $rho_t (t)=t'$;
  or $v="undef"$.
] <def:valsim>

Related bytes decode to related values at every scalar, and a stored value
related to the target's encodes to related bytes whenever both encodings
succeed; this is what lets a load and a store move a value
between the two memories through any byte layout, including a one-byte
field inside a wider one.

=== Permission simulation

#definition("Permission simulation")[
  Let items, stacks, and states be those of the Stacked Borrows instance of
  @sec:perm. Under $rho_t$:
  - Two _items_ are related when they have the same constructor and
    $rho_t$ maps the source tag to the target tag; raw-pointer items
    additionally carry the same mutability flag.
  - Two _stacks_ are related position by position, so their lengths agree.
  - Two _stack maps_ are related when, for every byte address $a$, either
    both lack an entry at $a$ or their entries at $a$ are related stacks.
  - Two _protector frame lists_ are related as lists of related tag lists,
    and two _exposed-tag lists_, and two lists of weakly protected tags, are
    related as tag lists.
  - Two _retired-tag lists_ are related in one direction: if
    $rho_t (t)=t'$ and $t'$ is retired in the target, then $t$ is retired in
    the source; and every retired target tag is below the target's
    `NextTag`.
  Permission states $Pi_s$ and $Pi_t$ are related, written
  $Pi_s approx Pi_t$, when all of these components are related and
  $Pi_s."NextTag" <= Pi_t."NextTag"$.
] <def:permsim>

Stack-map comparison is by address lookup, not by the list position used to
implement the finite map. Disjoint operations may reorder that representation
while leaving all address observations the same.

The counter condition is an inequality rather than an equality. Suppose a
route borrow mints route tag $u$ at the target counter. Inside the
compiled fragment the target stacks contain an extra item, so the boundary
relation is not expected to hold. The store uses $u$ and `die` removes its
item. The target counter remains advanced, which is why a later pair of
corresponding source and target tags may have different numeric values.

When a source-visible reference is formed, both machines mint a tag. If they
produce $t_s$ and $t_t$, the proof extends

#align(center)[
  $rho'_t = rho_t[t_s mapsto t_t].$
]

Because both fresh tags are minted at their machine's counter, and the
boundary invariant below keeps every mapped tag strictly below both
counters, neither fresh tag is already in the old map's domain or range, so
injectivity is preserved. By contrast, a route borrow never extends
$rho_t$, since there is no source tag to use as a key.

=== The layout conditions

#definition("Layout conditions")[
  A layout environment $Lambda$ is _well formed_ when every pointer-typed
  place has an eight-byte layout, and every integer- or pointer-typed place
  $p$ has a layout whose first leaf spans it:
  $|kappa_0| = |Lambda(p)|$ for the scalar $kappa_0$ of the first leaf of
  $Lambda(p)$. Each local's layout _has its type's shape_ when
  $"Int" theta$ is laid out as $"int"(n)$ with $n$ the byte width of
  $theta$, $"Ptr" tau$ as $"ptr"(beta)$ with $beta$ of $tau$'s shape, and
  a tuple as $"tup"$ with fields of their types' shapes, offsets, size, and
  alignment unconstrained.
] <def:layoutwf>

The first condition is what the compiler relies on when it loads a pointer
in eight bytes through a borrow of the pointer's field; the second, when it
reads one leaf of a field at a nonzero offset through a borrow of the
field's size. Neither condition is about Rust: they say that the layout
table is a layout _of the program's types_. Shape agreement is decidable
per local, implies well-formedness for every place, and holds for the
uniform layout (every integer eight bytes, tuples in C layout) and, by a
check the conformance runner performs, for every program it loads with
rustc's layouts (@sec:mech).

=== The boundary invariant

#definition("Boundary invariant")[
  Let $C$ be a compiler state. Source state $S=(i,E,mu_s,Pi_s)$ and target
  state $T=(j,R,mu_t,Pi_t)$ satisfy the _boundary invariant_ at $C$ under
  $rho_t$, written $S scripts(approx)_(rho_t)^C T$, when the following nine
  clauses hold.
  #set enum(numbering: n => [(I#n)])
  + _Control alignment._ $j=C.n_l$.
  + _Bound locals._ If $E(ell)=(a,t)$ for $ell:tau$, then
    $C.L(ell)=(r,tau)$, $R(r)=["ptr"(a,0,e,|Lambda(ell)|,t')]$ for some
    $e$, $rho_t (t)=t'$, and $t$ is not the wildcard tag.
  + _Memory._ $mu_s$ is simulated by $mu_t$ (@def:memsim).
  + _Allocator lockstep._ The two allocators are in lockstep
    (@def:memsim).
  + _Permissions._ $Pi_s approx Pi_t$ (@def:permsim).
  + _Tag-map shape._ $rho_t$ is injective and maps the wildcard tag to
    itself.
  + _Tag bounds._ Every source tag in the domain of $rho_t$ lies below
    $Pi_s."NextTag"$, and every tag in its range lies below
    $Pi_t."NextTag"$.
  + _Unbound locals._ If $E$ has no binding for $ell$, then $C.L$ has no
    entry for $ell$.
  + _Register freshness._ Every register in the range of $C.L$ is below
    $C.n_r$.
] <def:inv>

The invariant is required only at source-statement boundaries and is
deliberately strict about stack shape there. The compiled fragment may push
a route tag's item inside a fragment, but `die` removes it before the
invariant is re-established. Numeric next-tag counters may still differ,
which is why tags are renamed and the target counter need only be greater.
For a program $P$, the boundary that matters after $i$ source steps is the
_prefix state_ $C_i$, the result of compiling $P[0..i)$ from $C_"init"$;
(I1) then places the target at the entry label of statement $i$.

Each clause beyond (I3) and (I5) is there because a statement of the
theorem without it is false or unprovable for some compiled fragment:
memory agreement alone cannot show that a fresh `load` register does not
overwrite a local's register (I9), and equal watermarks alone cannot show
that an unbound source local corresponds to a target fragment containing
`alloc` (I8).

=== Simulation theorems

Let `srcStep` fetch the source statement at the current PC and execute it,
and $"runS"^n$ and $"runT"^n$ iterate the two machines, treating `halt` and
a missing statement as successful fixed points. The theorems hold for
_every_ statement and expression of the full language (@sec:surface).

#theorem("One-step forward simulation")[
  Let $Lambda$ be well formed (@def:layoutwf), $s != "halt"$ a statement,
  $C$ a compiler state from which $s$ compiles to $C'$, and $Q$ a program
  that contains the code of $C'$. If
  $ S scripts(approx)_(rho_t)^C T quad "and" quad "step"(S,s)="ok"(S'), $
  then there exist $rho'_t supset.eq rho_t$, a target state $T'$, and
  $n_t$ such that
  $ Q tack T arrow.r^(n_t) T' quad "and" quad
    S' scripts(approx)_(rho'_t)^(C') T'. $
] <thm:step>

The compiler state after the step is $C'$, the state compiling $s$ left:
the invariant moves along the compilation as the source moves along the
program. Only the renaming grows. The target step count $n_t$ is
existential because fragments have different lengths.

The initial states are $S_"init"$ and $T_"init"$: empty environment,
register file, and memory, PC zero, both watermarks at 1, and both
permission states initialized. They satisfy
$S_"init" scripts(approx)_(rho_0)^(C_"init") T_"init"$ under the renaming
$rho_0$ that maps only the wildcard tag to itself.

#theorem("Compiler correctness")[
  Let $Lambda$ be well formed and $P$ a program that compiles to $Q$. If
  $"runS"^(n_s)(P,S_"init")="ok"(S')$, then there exist $rho_t$, $T'$, and
  $n_t$ with
  $ "runT"^(n_t)(Q,T_"init")="ok"(T') quad "and" quad
    S' scripts(approx)_(rho_t)^(C_(S'.i)) T'. $
] <thm:run>

#corollary("Layouts of the program's types")[
  @thm:run holds for every $Lambda$ in which each local's layout has its
  type's shape.
] <cor:agrees>

#corollary("Uniform layout")[
  @thm:run holds, with no hypothesis beyond compilation, for the uniform
  layout.
] <cor:uniform>

Let OSEA-IR#sub[B] be OSEA-IR with the permission model in which `die`
returns its state unchanged, $"runT"_B^n$ its machine, and $T^B_"init"$
its initial state. Eliding every `die`, the compiler's cleanup
instruction, never makes a valid program invalid:

#theorem("Die elision")[
  For every OSEA-IR program $Q$ and every $n$, if
  $"runT"^n (Q,T_"init")="ok"(T')$, then
  $"runT"_B^n (Q,T^B_"init")="ok"(T'')$ for some $T''$ with the same PC,
  registers, and memory as $T'$.
] <thm:die-elision>

The permission states of the two machines are related as follows.

#definition("Die-elision relation")[
  Let $E$ be a set of tags. A stack $sigma_B$ _extends_ a stack $sigma_A$
  by $E$ when $sigma_B$ is $sigma_A$ with items whose tags are in $E$, the
  _extras_, inserted at any positions, and no item $"RawPtr"("true",t)$ of
  $sigma_A$ lies directly above an extra. Permission states are related,
  $Pi_A prec.eq Pi_B$, when
  - they have the same `NextTag`, protector frames, exposed tags, and weakly
    protected tags, and $Pi_B$ has retired no tag;
  - no tag retired in $Pi_A$ is exposed in $Pi_A$;
  - at every byte address $a$, either both stacks are absent, or
    $Pi_B (a)$ extends $Pi_A (a)$ by the tags that are retired and
    unprotected in $Pi_A$, the tags of $Pi_B (a)$ are pairwise distinct and
    below `NextTag`, and the bottom item of $Pi_A (a)$ is an $"Own"$ item.
] <def:dierel>

#theorem("Die elision per operation")[
  The initial permission state is related to itself. If
  $Pi_A prec.eq Pi_B$, then:
  - if $"die"(Pi_A,a,n,u)=Pi'_A$, then $Pi'_A prec.eq Pi_B$;
  - for every other operation of the interface (@sec:perm,
    @tab:surface-perm), if it succeeds on $Pi_A$ with result $Pi'_A$ (and
    tag $u$, for `own` and `ref`), it succeeds on $Pi_B$ with the same
    arguments, with a result $Pi'_B$ (and the same tag $u$), and
    $Pi'_A prec.eq Pi'_B$.
] <thm:die-rel>

For compiled code the converse holds as well:

#theorem("Die elision for compiled code")[
  Let $P$ compile to $Q$. For every $n$, $"runT"^n (Q,T_"init")$ succeeds if
  and only if $"runT"_B^n (Q,T^B_"init")$ succeeds.
] <thm:die-iff>

Apart from @thm:die-iff, these results are preservation of successful
finite executions. They are not backward simulation, divergence
preservation, or an equivalence between source and target error
messages. Their observable consequences are the
memory and permission clauses of the final invariant, made explicit in
@cor:observe.

=== The running program as a simulation

#statetable(
  [The running program as a simulation: the boundary invariant at each source-statement boundary. $i$ is the source PC and $j=C_i.n_l$ the target label (@fig:compile-example); the $rho_t$ column shows what the step _adds_; "next" is the pair of tag counters.],
  ([$i$], [$j$], [added to $rho_t$], [next], [what the invariant records at this boundary]),
  (5%, 5%, 15%, 8%, 67%),
  placement: none,
  ([0], [0], [$0 |-> 0$], [1, 1], [Initial states: nothing is bound, and $rho_t$ fixes only the wildcard.]),
  ([1], [2], [$1 |-> 1$], [2, 2], [$x$ is bound on both sides (I2): the allocators in lockstep (I4) gave both allocations base 8, and the two owning tags form the pair $(1,1)$.]),
  ([2], [5], [---], [2, 3], [The stacks of $[16,24)$ are again related (I5): `borrow; storec; die` left the stack effect of the source's one `useMut`. Route tag 2 is in no renaming; the counters part.]),
  ([3], [8], [$2 |-> 3$, \ $3 |-> 4$], [4, 5], [$y$ is bound, and the bytes of the reference it holds are related (I3): the same address bytes, with provenance tags 3 and 4. $rho_t$ grew by two pairs that are _not_ numerically equal, which (I6) and (I7) permit.]),
  ([4], [10], [---], [4, 5], [$[16,24)$ holds the same bytes on both sides (I3): the loaded $"ptr"(8,8,8,24,3)$ and $"ptr"(8,8,8,24,4)$ were related, so both writes went through related tags to the same bytes.]),
) <tab:sim-example>

#example[
  @tab:sim-example replays @tab:mir-example against @tab:osea-example.
  Each row is an instance of the invariant that @thm:run asserts at the
  prefix state; the first is the initial relation and each later one
  follows from the previous by @thm:step.

  _Boundary 1._ Statement 0 assigns to the unbound local $x$. Source
  preparation allocates $|beta_x|=24$ bytes and obtains the owning tag 1;
  the target fragment begins with $"R"_0 := "alloc"_(beta_x)$, allocates
  the same base by (I4), and obtains tag 1. The proof extends $rho_t$ by
  $1 |-> 1$ and the local map by $x |-> ("R"_0,tau_x)$; the store writes
  the same eight bytes on both sides, establishing (I3) for $[8,16)$.

  _Boundary 2._ Statement 1 is $x.1.0 := "const"(42)$. The source resolves
  the place to address 16 and performs $"useMut"(Pi_s,16,8,1)$. The target
  performs
  $ "ref"(Pi_t,16,8,1,"mutable","false",[])=(Pi_1,2), quad
    "useMut"(Pi_1,16,8,2)=Pi_2, quad
    "die"(Pi_2,16,8,2)=Pi'_t. $
  The third event removes the route tag's item from each of the eight
  stacks, so they are again related (I5) under the _unchanged_ $rho_t$: tag
  2 has no source counterpart and never escapes. Both memories update only
  $[16,24)$, with the same bytes, so (I3) is restored and the neighbouring
  bytes are framed. (I1) advances from source PC 1 to 2 and from target
  label 2 to the next prefix label 5. The target counter is now 3 and the
  source counter 2, which the inequality of @def:permsim absorbs.

  _Boundary 3._ Statement 2 allocates $y$ on both sides, with owning tags 2
  and 3, and then forms the reference, with tags 3 and 4. Neither pair is
  an equality, and neither could be: the route borrow of the previous
  statement advanced only the target counter. This is the step at which a
  tag renaming, rather than tag equality, is forced. The stored pointers
  $"ptr"(8,8,8,24,3)$ and $"ptr"(8,8,8,24,4)$ are related by @def:valsim,
  so their encodings, the same eight address bytes with provenance tags 3
  and 4, are related byte by byte (@def:memsim); and the stacks of
  $[16,24)$, $["MutRef"(3),"Own"(1)]$ and $["MutRef"(4),"Own"(1)]$, are
  related by @def:permsim.

  _Boundary 4._ Statement 3 writes through $y$. Both machines read
  $[32,40)$ through $y$'s owning tag, related by $2 |-> 3$, and decode
  pointers related by (I3). The two writes therefore go through tags
  related by $3 |-> 4$, to the same bytes. No tag is minted and none is
  retired.

  Reassociation is semantically load-bearing at boundary 2. A route borrow
  of the intermediate field $x.1$ would retag $[24,32)$ as well, so the
  target would not simulate the source's eight-byte write in the presence
  of a borrow of the sibling $x.1.1$. The compiled path must use the
  composed offset and the final size.
] <ex:sim>

The four formal views of the program thus line up. MIRLite's typed path
selects $x.1.0$, which the layout places at byte offset 8 with size 8.
OSEA-IR begins with a pointer to $x$'s 24 bytes in $"R"_0$, which the
compiler's local map connects to $x:tau_x$. Reassociation prevents an
intermediate sixteen-byte borrow, so place lowering creates exactly one
route tag for $[16,24)$, and cleanup supplies the matching eight-byte
`die`. At each boundary, the shared addresses relate the updated bytes,
memory simulation frames their neighbours, permission simulation cancels
the route tag without adding it to $rho_t$, and prefix compilation places
the target at the next fragment exactly when the source reaches the next
statement:

#align(center)[
#box(width: 96%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"typed source range" arrow.r "reassociated target route" arrow.r
    "explicit events" arrow.r "boundary simulation".$
]]

=== Observable consequences

#corollary("Observations at a boundary")[
  If $S scripts(approx)_(rho_t)^C T$, then:
  - every initialized source byte is the same byte in the target memory, at
    the same address, with the same provenance up to the tag;
  - hence a leaf that decodes to $"word"(w)$ in the source decodes to
    $"word"(w)$ in the target, and one that decodes to
    $"ptr"(b,o,e,sz,t)$ decodes to $"ptr"(b,o,e,sz,t')$ with
    $rho_t (t)=t'$;
  - if $E(ell)=(a,t)$ for $ell:tau$, then the register $C.L(ell)$ holds
    exactly one pointer with base $a$, offset zero, size $|Lambda(ell)|$,
    and tag $rho_t (t)$;
  - the target stack at every byte address has the same length and item
    constructors as the source stack, with every source tag renamed by
    $rho_t$;
  - the target PC is the entry label $C.n_l$.
] <cor:observe>

Several asymmetries are intentional. The target may contain extra registers,
because value temporaries remain after use. An uninitialized source byte
refines any target byte, so the memory relation has no reverse guarantee.
Tag counters need not be equal, and numeric tag equality is not observable.
Finally, the invariant is required only at source-statement boundaries;
intermediate target states may contain live route tags.

These choices are the minimum abstraction needed by the actual generated
code. Strengthening to literal register equality would reject harmless
temporaries, while weakening permission stacks to ignore arbitrary target
items would no longer justify later accesses.

= Mechanization and scope <sec:mech>

#takeaway([PRECISE CLAIM], [
  The mechanized theorems are forward simulations for successful finite runs
  of every MIRLite program, every statement and expression of
  @sec:surface included, on byte-addressed memory, for every layout
  environment that is well formed (@def:layoutwf). Well-formedness holds
  outright for the uniform layout, and follows from a decidable per-local
  check that the conformance runner applies to the layouts it loads from
  rustc.
])

Every numbered definition and result of @sec:correctness is a Lean 4
declaration in `src/obseq3/proof/`:

#proptable(
  [The results of @sec:correctness and their Lean declarations.],
  ([This paper], [Lean declaration], [File]),
  (30%, 46%, 24%),
  ([@def:rename], [`TagRenameMap`, `TagRenameIncr`], [`basis.lean`]),
  ([@def:memsim], [`ByteSim`, `ByteMemSim`, `ByteAllocLockstep`], [`memsim.lean`]),
  ([@def:valsim], [`ValSim`], [`memsim.lean`]),
  ([@def:permsim], [`PermSim`], [`basis.lean`]),
  ([@def:layoutwf], [`PtrPlacesWF`, `LeafWF`; `LocalsAgree`], [`places.lean`, `leaffield.lean`; `layoutagree.lean`]),
  ([@def:inv], [`InvAtB`], [`spine.lean`]),
  ([@thm:step], [`stmt_sim`], [`coverage.lean`]),
  ([initial relation], [`InvAtB_initial`], [`program.lean`]),
  ([@thm:run], [`compile_correct_all`], [`coverage.lean`]),
  ([@cor:agrees], [`compile_correct_agrees`], [`layoutagree.lean`]),
  ([@cor:uniform], [`compile_correct_uniform`], [`coverage.lean`]),
  ([@def:dierel], [`StackSub`, `CellRel`, `Extra`, `PermSub`], [`stacksub.lean`, `cellsub.lean`, `permsub.lean`]),
  ([@thm:die-rel], [`modelSim_noDie`], [`die_elision.lean`]),
  ([@thm:die-iff], [`compiled_die_elision`], [`route_compile.lean`]),
  ([@thm:die-elision], [`die_elision`], [`die_elision.lean`]),
) <tab:lean>

The proof is about 19,700 lines and 674 theorems across the 50 files of
that directory, which also hold the Stacked Borrows lemmas it rests on.
None of it contains an admitted goal. A checked audit prints the axioms
that @thm:run, its corollaries, @thm:die-elision, and @thm:die-iff depend on and fails
if that set differs in either direction from a pinned whitelist; a second
check covers every one of the directory's 1,265 declarations. The whitelist contains exactly the
three standard Lean axioms, propositional extensionality, choice, and
quotient soundness, and no `sorryAx`.

The executable compiler is additionally validated by testing: a compiler
witness corpus of 149 programs, run on both machines at the uniform layout
(four of them are OSEA-IR programs run with and without `die`, for
@thm:die-elision)
and pinned as golden listings where the shape of the code matters; a
corpus of 206 entries, drawn from Miri's Stacked Borrows tests and
completed by local witnesses, loaded from rustc's MIR through Charon with
rustc's own layouts, whose 188 supported programs reach Miri's verdict
and, where Miri reports undefined behavior, the same statement and, with
four documented exceptions, the same reason; and a differential run that compiles each of those 188
programs and requires the same verdict from both machines, and the same
OSEA-IR verdict with every `die` elided. The layout
check of @def:layoutwf passes on all of them. The running program of this
paper is part of the witness corpus, both as a golden listing
(@fig:compile-example) and as a differential test; the states of
@tab:mir-example and @tab:osea-example are printed by the mechanized
interpreters.

#source([Invariant and simulation vocabulary: `src/obseq3/proof/basis.lean`, `memsim.lean`, `spine.lean`. Statement and whole-program forward simulations: `src/obseq3/proof/program.lean`, `coverage.lean`. Witness corpus: `src/obseq3/compile_tests.lean`; state dump of the running program: `notes/2026-09-18-paper-running-example.lean`.])

#counter(heading).update(0)
#set heading(numbering: "A.1", supplement: [Appendix])

= The full executable surface <sec:surface>

The main text presents constants, copies, moves, references, assignment,
and `halt`. This appendix extends each of its figures and tables, in the
same format, to the language the compiler and the theorem actually cover.

== Syntax

#grammarfig(
  [The remaining syntax of MIRLite (left) and OSEA-IR (right), extending @fig:mir-grammar and @fig:oseair-grammar. $d$ in `ptrOffset` and $delta$ in `offset` are integers and $i$ a boolean, set for in-bounds arithmetic; a `borrow` of length $bot$ retags the pointer's extent; $"op"$ is an integer operation at an integer type.],
  panel([MIRLite], bnf(
    prod($"Expr" in.rev e$, $dots$, $"uninit" | "alloc"("len")$, $"exposeAddr"(p) | "addr"(p)$, $"fromExposed"(p)$, $"ptrCast"(p) | "ptrOffset"(p,d,i) | "ptrOffset"(p,p_n,i)$, $"addrOf"(ell"."q)$, $"refSlice"(k,c,p)$, $"sliceLen"(p) | "subSlice"(p, p_l, p_h)$, $"binOp"("op", p_a, p_b)$),
    prod($"Stmt" in.rev s$, $dots$, $"assignIf"(p = w, thick d := e)$, $"dealloc"(p)$, $"pushProtectors" | "popProtectors"$),
    prod($"len"$, $"const"(n) | "from"(p)$),
  )),
  panel([OSEA-IR], bnf(
    prod($"Rhs" in.rev h$, $dots$, $"allocN"_beta (n) | "allocDyn"_beta (r)$, $"expose"_kappa (r) | "fromExposed"_kappa (r)$, $"offset"_kappa (r,delta,i) | "offsetBy"_(t,n) (r,r_n,i)$, $"placeAddr"(r,o,n)$, $"borrow"(k,c,m,bot,r,delta)$, $"sliceLen"_n (r) | "subSlice"_n (r, r_l, r_h)$, $"binOp"("op", r_a, r_b)$),
    prod($"Instr" in.rev I$, $dots$, $"dealloc"(r)$, $"skipIf"(r, w, n)$, $"pushProt" | "popProt"$),
  )),
) <fig:surface-grammar>

Typing follows @sec:mirlite: $"uninit"$ has any type; $"alloc"("len")$
and the pointer expressions have pointer types, with $"ptrCast"$,
$"ptrOffset"$, $"refSlice"$, $"sliceLen"$, and $"subSlice"$ taking a
pointer place; $"exposeAddr"(p)$, $"addr"(p)$, $"sliceLen"(p)$, and
$"binOp"$ have any integer type, the destination's; integer operands, slice bounds,
allocation lengths, and guard discriminants are integer places of any
width. An integer operation carries its own integer type: it wraps at that
width, compares by its signedness, and is undefined behavior on overflow
for the unchecked forms and on division by zero. An integer cast of
rustc's MIR is lowered by the loader to such an operation at the
destination's type.

The source semantics of these forms follows the pattern of @tab:mir: each
expression resolves its place, performs the permission events listed for
its target counterpart in @tab:surface-osea in the same order, and
produces values. The one-leaf expressions, `exposeAddr`, `addr`,
`fromExposed`, `ptrCast`, `ptrOffset`, and `refSlice`, read the first leaf
of their place, of scalar $kappa$, rather than the whole place. `addr`
decodes that leaf's bytes at integer type, as a pointer-to-integer
`transmute` or `ptr.addr()` does: the address, with the provenance stripped
and nothing exposed, so a pointer later rebuilt from it by `fromExposed`
may not access the allocation unless some other cast exposed it. A guarded assignment first
prepares the root of its destination, _on both paths_, then reads its
discriminant exactly as $"copy"$ does, a real read access, and performs
the assignment when the value read equals $w$.

== The permission model <sec:surface-perm>

#proptable(
  [The remaining operations of the permission interface of @sec:perm.],
  ([Operation], [Meaning]),
  (40%, 60%),
  ([$"dealloc"(Pi,a,n,t)=Pi'$], [Deallocate the $n$ bytes from $a$ through $t$ and forget their permissions. The item carrying $t$ must grant writes at every byte, and no item of those stacks may be strongly protected.]),
  ([$"expose"(Pi,t)=Pi'$], [Record $t$ as exposed, so that a later wildcard access may resolve to it. Fails if $t$ is retired.]),
  ([$"pushProt"(Pi)=Pi'$, $"popProt"(Pi)=Pi'$], [Open a protector frame; close the innermost frame, ending the protection of every tag registered in it.]),
) <tab:surface-perm>

Tags are drawn from a countable set with a distinguished _wildcard_ tag 0,
which stands for an unknown provenance recovered from an exposed integer.
Every fresh tag is minted from `NextTag` upward, so it is distinct from
all earlier ones and a tag minted later is numerically larger. The rules of
@tab:sb extend as follows. _Protectors:_ if the flag $c$ of a `ref` is set,
the fresh tag is registered in the innermost protector frame; #sb-read,
#sb-use, and #sb-die fail when an item they would disable or remove is
protected. A `Box` passed to a function is _weakly_ protected: it may be
deallocated through its own tag or one derived from it. _Masks:_ entry $i$
of the mask $m$ says whether byte $a+i$ of the retagged range lies inside
an `UnsafeCell`; a byte beyond the end of $m$ counts as unmarked. On the
bytes that $m$ marks, a shared or raw-constant retag performs no access and
inserts $"RawPtr"("true",u)$ directly above the item carrying $t$, as
#sb-refr does. The mask has one entry per byte, rather than being a single
flag, because one reference may cover both kinds of memory: in
`&(i32, Cell<i32>)` the first field is frozen and the second is not, so a
single retag pushes $"Ref"(u)$ on the first four bytes and inserts
$"RawPtr"("true",u)$ on the next four. _Two-phase:_ a two-phase retag
performs a read and inserts $"RawPtr"("true",u)$ likewise, modelling a
reservation that stays writable until activation. _Raw-pointer groups:_
#sb-use also accepts $iota="RawPtr"("true",t)$, and then keeps the
contiguous run of mutable raw-pointer items directly above $iota$, removing
only what lies above the whole group. _Wildcard:_ an access through tag 0
resolves to the topmost exposed item that grants it. This rule is a
determinization: for programs that use integer-to-pointer casts, the
theorem is a statement about it rather than about Miri's angelic choice.
_Retirement:_ a range $"die"(Pi,a,n,u)$ fails if $u$ is exposed, and
otherwise adds $u$ to `retired`, once for the whole range; `expose` fails
on a retired tag. Miri has no `die` and neither check; neither fires on
compiled code, whose died tags are route tags and move temporaries, which
are never stored and so never exposed. Together they keep a wildcard
access from resolving to an item that a `die` removed, which is what makes
`die` removable (@thm:die-elision).

== OSEA-IR

#ruletable(
  [The remaining OSEA-IR rules, extending @tab:osea. A _one-leaf read_ through $r$ at scalar $kappa$ means: $T.R(r)=["ptr"(b,o,e,sz,t)]$, $a=b+o$, $b$ live, $a+|kappa| <= b+sz$, $"read"(T.Pi,a,|kappa|,t)=Pi_1$, and the leaf is $"dec"_kappa (T.mu[a..a+|kappa|))$. $"wild"$ is the wildcard tag and $"allocOf"(mu,w)$ the allocated range containing address $w$, or $(w,0)$.],
  placement: none,
  ir(rn[rval-allocn],
    [$z = n dot |beta|$, #h(3pt) $"alloc"(T.mu,z,"al"(beta))=(b,mu')$, \ $"own"(T.Pi,b,z)=(Pi',u)$],
    [$T tack "allocN"_beta (n) #dH$ \ $quad (["ptr"(b,0,z,z,u)], T[mu |-> mu', Pi |-> Pi'])$]),
  ir(rn[rval-allocdyn],
    [$T.R(r)=["dat"(n)]$, #h(3pt) and as #rn[rval-allocn]],
    [$T tack "allocDyn"_beta (r) #dH$ \ $quad (["ptr"(b,0,z,z,u)], T[mu |-> mu', Pi |-> Pi'])$]),
  ir(rn[rval-expose],
    [one-leaf read through $r$ at $kappa$, \ leaf $="ptr"(b',o',e',sz',t')$],
    [$T tack "expose"_kappa (r) #dH$ \ $quad (["dat"(b'+o')], T[Pi |-> "expose"(Pi_1,t')])$]),
  ir(rn[rval-fromexposed],
    [one-leaf read through $r$ at $kappa$, \ leaf $="word"(w)$, #h(3pt) $"allocOf"(T.mu,w)=(b',sz')$],
    [$T tack "fromExposed"_kappa (r) #dH$ \ $quad (["ptr"(b',w-b',sz'-(w-b'),sz',"wild")], T[Pi |-> Pi_1])$]),
  ir(rn[rval-offset],
    [one-leaf read through $r$ at $kappa$, \ leaf $="ptr"(b',o',e',sz',t')$, #h(3pt) $o'+delta >= 0$, \ $i and delta != 0 => b' "live" and o' <= sz' and o'+delta <= sz'$],
    [$T tack "offset"_kappa (r,delta,i) #dH$ \ $quad (["ptr"(b',o'+delta,e',sz',t')], T[Pi |-> Pi_1])$]),
  ir(rn[rval-offsetby],
    [$T.R(r)=["ptr"(b',o',e',sz',t')]$, #h(3pt) $T.R(r_n)=["dat"(w)]$, \ $delta = "int"_t (w) dot n$, #h(3pt) $o'+delta >= 0$, \ $i and delta != 0 => b' "live" and o' <= sz' and o'+delta <= sz'$],
    [$T tack "offsetBy"_(t,n) (r,r_n,i) #dH$ \ $quad (["ptr"(b',o'+delta,e',sz',t')], T)$]),
  ir(rn[rval-placeaddr],
    [$T.R(r)=["ptr"(b,o',e,sz,t)]$],
    [$T tack "placeAddr"(r,o,n) #dH$ \ $quad (["ptr"(b,o'+o,n,sz,t)], T)$]),
  ir(rn[rval-borrow-rest],
    [$T.R(r)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $b$ live, \ $"ref"(T.Pi,b+o+delta,e,t,k,c,m)=(Pi',u)$],
    [$T tack "borrow"(k,c,m,bot,r,delta) #dH$ \ $quad (["ptr"(b,o+delta,e,sz,u)], T[Pi |-> Pi'])$]),
  ir(rn[rval-slicelen],
    [$T.R(r)=["ptr"(b,o,e,sz,t)]$],
    [$T tack "sliceLen"_n (r) #dH (["dat"(e div n)], T)$]),
  ir(rn[rval-subslice],
    [$T.R(r)=["ptr"(b,o,e,sz,t)]$, #h(3pt) $T.R(r_l)=["dat"(l)]$, \ $T.R(r_h)=["dat"(h)]$, #h(3pt) $l <= h$, #h(3pt) $h dot n <= e$],
    [$T tack "subSlice"_n (r,r_l,r_h) #dH$ \ $quad (["ptr"(b,o+l n,(h-l) n,sz,t)], T)$]),
  ir(rn[rval-binop],
    [$T.R(r_a)=["dat"(x)]$, #h(3pt) $T.R(r_b)=["dat"(y)]$, \ $"op"$ is defined on $x, y$],
    [$T tack "binOp"("op",r_a,r_b) #dH (["dat"("op"(x,y))], T)$]),
  ir(rn[exec-dealloc],
    [$Q(j)="dealloc"(r)$, #h(3pt) $R(r)=["ptr"(b,0,e,sz,t)]$, \ $"dealloc"(Pi,b,sz,t)=Pi'$],
    [$(j,R,mu,Pi) ssea$ \ $quad (j+1, R, mu[b..b+sz) |-> "uninit", b "freed", Pi')$]),
  ir(rn[exec-skipif],
    [$Q(j)="skipIf"(r,w,n)$, #h(3pt) $R(r)=["dat"(w')]$, \ $j'=j+1$ if $w'=w$, else $j'=j+1+n$],
    [$(j,R,mu,Pi) ssea (j',R,mu,Pi)$]),
  ir(rn[exec-pushprot],
    [$Q(j)="pushProt"$],
    [$(j,R,mu,Pi) ssea (j+1,R,mu,"pushProt"(Pi))$]),
  ir(rn[exec-popprot],
    [$Q(j)="popProt"$, #h(3pt) $"popProt"(Pi)=Pi'$],
    [$(j,R,mu,Pi) ssea (j+1,R,mu,Pi')$]),
) <tab:surface-osea>

The pointer right-hand sides are operational rather than mere casts, and
share a three-stage pattern: validate the register shape, perform the
permission events in source order, construct a result. They read _through
the outer pointer in the register_ before inspecting the value in memory,
one leaf at the scalar the source reads. For example, `offset` does not
change the offset of that outer pointer: it loads a pointer-valued leaf,
changes the loaded value, and returns the result in a register. This is why
the compiler can use it to implement MIRLite pointer arithmetic without
suppressing the source's read event. Its flag $i$ is Miri's in-bounds
arithmetic, set by the loader for `add`, `offset`, and a raw borrow of a
field through a raw pointer, and clear for `wrapping_add` and
`wrapping_offset`: a nonzero move must then stay within a live allocation,
both ends included and one past the end allowed, so a pointer without
provenance, whose allocation size is zero, cannot move. Both machines
check the same condition on the same pointer fields and the same freed
blocks, as one shared function. `allocDyn` takes its length from a
register that an ordinary `load` filled, which matches the source's
permission-visible length read. A deallocated block is overwritten with
uninitialized bytes and its base is recorded as freed; the bump allocator
never reuses it, and any later access through a pointer into it fails
before its permissions are consulted, as in Miri. `skipIf` touches neither
memory nor permissions: the discriminant it tests was loaded into a
register by an ordinary `load`.

OSEA-IR errors fall into several semantic classes rather than one generic
"stuck" state:

#proptable(
  [Error classes of OSEA-IR.],
  ([Class], [Typical cause], [Where detected]),
  (20%, 40%, 40%),
  ([Register shape], [Missing register, or a register that does not hold the single pointer or word the instruction needs.], [Before any memory or permission change.]),
  ([Liveness], [An access through a pointer into a freed block.], [Before the bounds check and any permission event.]),
  ([Spatial], [A complete access range exceeds its allocation, a pointer offset becomes negative or, for in-bounds arithmetic, leaves its live allocation, or a sub-slice exceeds its extent.], [Before the corresponding read/write permission event.]),
  ([Permission], [`read`, `ref`, `useMut`, `die`, `dealloc`, or a protector pop rejects the operation.], [At the permission interface; its error is propagated.]),
  ([Value], [A load decodes an uninitialized leaf; a cast or allocation observes the wrong value constructor; a store's word does not fit its leaf; an integer operation is undefined.], [After any required permission read, so that event order remains explicit.]),
) <tab:surface-errors>

The forward simulation only starts from a successful source step. It
therefore proves that the compiled fragment avoids all of these errors; it
does not claim that source and target failure messages coincide.

== Compiler

Every expression has the pre-code/store split of #c-copy, and every store
is at the destination's layout $beta_d$. In @tab:surface-expr, "lower $p$"
is $C tack_"shared" p #dCP (r_s,D_s,C_1)$; "read $p$ into $r$" is "lower
$p$; $r := "load"_(Lambda(p)) (r_s)$; $"cleanup"(D_s)$"; $r_v$ is a fresh
value register; $kappa$ is the scalar of the first leaf of $Lambda(p)$, and
$beta_kappa$ the layout of that one leaf; and the pre-code is emitted
before the destination is lowered.

#proptable(
  [Lowering of the remaining expressions, extending #c-const, #c-copy, #c-move, and #c-ref of @tab:compile. In `ptrOffset`, `sliceLen`, and `subSlice`, $beta_e$ is the pointee layout of $p$; in `alloc`, $beta_e$ is the pointee of $beta_d$.],
  ([Expression], [Pre-destination code], [Deferred store $F(r_d)$]),
  (19%, 50%, 31%),
  ([`uninit`], [None.], [$"storec"_(beta_d) (["undef"]^(n), r_d)$, $n$ the leaves of $beta_d$]),
  ([`alloc(const(n))`], [$r_v := "allocN"_(beta_e) (n)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`alloc(from(p))`], [Read $p$ into $r_n$; $r_v := "allocDyn"_(beta_e) (r_n)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`exposeAddr(p)`], [Lower $p$; $r_v := "expose"_kappa (r_s)$; $"cleanup"(D_s)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`addr(p)`], [Lower $p$; $r_v := "load"_("int"(|kappa|)) (r_s)$; $"cleanup"(D_s)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`fromExposed(p)`], [Lower $p$; $r_v := "fromExposed"_kappa (r_s)$; $"cleanup"(D_s)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`ptrCast(p)`], [Lower $p$; $r_v := "load"_(beta_kappa) (r_s)$; $"cleanup"(D_s)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`ptrOffset(p,d,i)`], [Lower $p$; $r_v := "offset"_kappa (r_s, d dot |beta_e|, i)$; $"cleanup"(D_s)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`ptrOffset(p,`$p_n$`,i)`], [Read $p$, $p_n$ into $r, r_n$; $r_v := "offsetBy"_(t,|beta_e|) (r,r_n,i)$, $t$ the type of $p_n$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`addrOf(`$ell"."q$`)`], [$r_v := "placeAddr"(R_ell, "off"_Lambda (ell,q), |Lambda(ell"."q)|)$, $R_ell$ the register of $ell$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`refSlice(k,c,p)`], [Lower $p$; $r_v := "load"_(beta_kappa) (r_s)$; $"cleanup"(D_s)$; then $r_v := "borrow"(k,c,[],bot,r_v,0)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`sliceLen(p)`], [Read $p$ into $r$; $r_v := "sliceLen"_(|beta_e|) (r)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`subSlice(p,`$p_l$`,`$p_h$`)`], [Read $p$, $p_l$, $p_h$ into $r, r_l, r_h$; $r_v := "subSlice"_(|beta_e|) (r,r_l,r_h)$.], [$"store"_(beta_d) (r_v, r_d)$]),
  ([`binOp(op,`$p_a$`,`$p_b$`)`], [Read $p_a$, $p_b$ into $r_a, r_b$; $r_v := "binOp"("op",r_a,r_b)$.], [$"store"_(beta_d) (r_v, r_d)$]),
) <tab:surface-expr>

Pointer offsets are expressed by the source in pointee units, so the
compiler scales $d$ by the pointee's byte size before OSEA-IR sees it. A
count known only when the program runs is an integer place $p_n$: both
places are copy-read into registers, as for `subSlice`, and `offsetBy`
scales the word, read at its integer type $t$, when it executes.
`addrOf`$(ell"."q)$ is a pointer to a place of a local with the local's own
tag: no retag and no event, the address Miri computes for a place
projection. The loader uses it to index a local array at a run-time
index, never for `&` or `&raw`, which retag. It compiles to `placeAddr`,
which moves the pointer in the local's register without a borrow, so no
route tag appears. A
pointer cast is tag-preserving: a `borrow` would mint a new tag, whereas a
load and a store copy the pointer value unchanged while performing the
source's read and write. The placement of cleanup is semantic. In
`refSlice` the mint comes _after_ the cleanup: a mutable retag through the
loaded tag would pop a route tag still on the stack, and a shared one would
bury it, so the route's `die` would no longer find its item on top. Every
bracket the compiler opens therefore closes with its route tag on top.

#proptable(
  [Lowering of the remaining statements, extending #c-assign and #c-halt of @tab:compile.],
  ([Statement], [Emitted sequence]),
  (24%, 76%),
  ([`dealloc(p)`], [Read $p$ into $r_v$; $"dealloc"(r_v)$.]),
  ([`assignIf(p = w, d := e)`], [$"root"(d)$, before the guard; read $p$ into $r_g$; reserve the label $j_g$; compile $d := e$ by #c-assign; patch $K(j_g) = "skipIf"(r_g, w, n)$ with $n$ the number of labels the assignment emitted.]),
  ([`pushProtectors`], [$"pushProt"$]),
  ([`popProtectors`], [$"popProt"$]),
) <tab:surface-stmt>

For `assignIf`, the root of the destination is allocated before the guard
because a root allocated inside the guarded fragment would be recorded in
$L$ at compile time but would exist at run time only when the guard is
taken. The guard _reserves_ its label and is patched once the body has been
compiled, so the body is compiled exactly once and its measured length is
the skip count; no statement is compiled twice.

== What remains outside the theorem <sec:surface-open>

Every statement and expression above is inside @thm:run. What the theorem
assumes, and where the model approximates Rust, is:

- _Layouts._ The layout environment must be well formed (@def:layoutwf).
  The proof holds it as a hypothesis; for the layouts rustc gives, it is
  discharged by the decidable shape check, program by program.
- _Fat pointers._ A slice reference is one value whose extent travels in
  its provenance, not a pointer and a length in two words; the extent is
  recovered whenever the pointer's bytes are read back whole.
- _Wildcard provenance._ An access through an exposed address resolves to
  one granting item, deterministically (@sec:surface-perm).
- _Executions._ The theorems preserve successful finite runs; they say
  nothing of divergence and do not relate source and target failure
  messages.
