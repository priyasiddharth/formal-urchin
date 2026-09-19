// PLDI 2027 review layout. Build from the repository root with:
// typst compile --root . --font-path assets/fonts/acm \
//   pldi27/mirlite-oseair-correctness.typ
//
// Presentation follows oopsla26/opsem.tex: for each language, SYNTAX is one
// grammar | configuration | types figure, SEMANTICS is one
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
// Syntax: BNF panels and the grammar | configuration | types figure.
// ---------------------------------------------------------------------
// prod(lhs, alt-line, alt-line, ...): the first line is introduced by ::=,
// every further line by |.
#let prod(lhs, ..lines) = {
  let out = ()
  for (i, l) in lines.pos().enumerate() {
    out.push(if i == 0 { lhs } else { [] })
    out.push(if i == 0 { $::=$ } else { $|$ })
    out.push(l)
  }
  out
}
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

// ---------------------------------------------------------------------
// Example: stepwise post-state tables and side-by-side listings.
// ---------------------------------------------------------------------
#let statetable(caption, header, cols, ..rows, placement: auto, size: 7.3pt) = figure(
  kind: table,
  placement: placement,
  caption: caption,
  {
    set text(size: size)
    set par(first-line-indent: 0pt, justify: false, leading: 0.42em)
    table(
      columns: cols,
      align: left + horizon,
      inset: (x: 3.5pt, y: 3.2pt),
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
    MIRLite gives typed Rust-like places an operational semantics. Its compiler
    lowers each statement to OSEA-IR with explicit reads, retags, writes, and
    borrow retirement. We present Stacked Borrows, both languages, and the
    compiler in one format: a grammar, a table of named rules, and the
    stepwise execution of one five-statement program that allocates a
    nested tuple, writes a nested field, borrows that field, and writes
    through the borrow. We then state the forward simulation that relates
    source and target memory, locals, and per-cell permission stacks, and
    replay the same program as a simulation. The simulation is mechanized
    in Lean 4 and covers every MIRLite construct except heap allocation and
    deallocation.
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

We use cells as the unit of layout. Write $|tau|$ for the number of cells in a
layout $tau$. Naturals and pointers occupy one cell; a tuple occupies the sum
of its fields. A pointer value $"ptr"(b,o,n,t)$ denotes address $b+o$ in an
allocation with base $b$, extent $n$, and provenance tag $t$. A memory $mu$
maps cell addresses to words, pointers, or undefined values. A permission
state $Pi$ records the per-cell borrow stacks.

@sec:opsem formalizes the compilation. It
(1) fixes the permission model, per-cell Stacked Borrows, and threads it
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
  single figure: grammar, configuration, types. _Semantics_ is a single
  table of named rules, read as premises, conclusion, name. The _example_ is
  a stepwise table giving the state after each instruction, and a
  walkthrough that names the rule each row fires. The same program is used
  in all of them, and once more in @sec:correctness as a simulation.
])

= Compiling MIRLite to OSEA-IR with ownership <sec:opsem>

The running program declares a nested tuple $x$ and a pointer $y$, and is
small enough to execute by hand:

#align(center, box(width: 70%, listing(
  [MIRLITE #h(6pt) $Gamma = [x : ("Nat",("Nat","Nat")), thick y : "Ptr" "Nat"]$],
  [
    0: #h(3pt) $x.0 := "const"(5)$ \
    1: #h(3pt) $x.1.0 := "const"(42)$ \
    2: #h(3pt) $y := "ref"("mutable", "false", [], x.1.0)$ \
    3: #h(3pt) $#dr y := "const"(7)$ \
    4: #h(3pt) $"halt"$
  ],
)))

Statement 0 allocates $x$, because an assignment to an unbound root
allocates it. Statement 1 writes one cell in the middle of $x$; it is the
statement for which the compiler must introduce, and then retire, a tag the
source never sees. Statement 2 allocates $y$ and stores a mutable reference
to the cell just written. Statement 3 writes through that reference. Both
machines start from empty states, allocate from address 0 with a bump
allocator, and mint tags from 1 upward; tag 0 is reserved for the wildcard
of @sec:surface. All concrete addresses, tags, registers, and labels below
are those of the mechanized semantics running this program.

== Stacked Borrows <sec:perm>

#figure(
  kind: image,
  caption: [A Stacked Borrows command sequence on the one cell $a$, with the stack after each command. It is the permission trace of the compiled statement 1 at $a=1$ with $t=1$, $u=2$.],
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
correctness result instantiates the model with the per-cell Stacked Borrows
of this subsection. The full executable language uses four further
operations, for deallocation, exposed provenance, and protector frames;
they are in @sec:surface.

A permission state is $Pi=("stacks","NextTag","frames","exposed")$. The
component `stacks` is a partial map from cell addresses to _borrow
stacks_; `NextTag` is the next fresh tag; `frames` and `exposed` are the
protector frames and exposed tags of @sec:surface. We write $Pi(a)$ for the
stack at $a$ and leave the other three components implicit when a rule does
not change them. A borrow stack is a list of _items_, topmost first,

#align(center)[
  $iota ::= "Own"(t) | "MutRef"(t) | "Ref"(t) | "RawPtr"(m',t) | "Disabled"(t),$
]

where $t$ is the item's tag and $m'$ a mutability flag. The top of the stack
is the most recently derived permission. @tab:sb gives the rules. A rule
$⟨ "op", Pi ⟩ #dA Pi'$ acts on one cell $a$; "$u$ fresh" means
$u=Pi."NextTag"$, and the conclusion increments the counter. @fig:sb-example
runs four of them: #sb-own pushes the owning item of a new allocation,
#sb-refm derives a mutable borrow with a fresh tag $u$ from its parent $t$,
#sb-use validates a write through $u$, and #sb-die pops $u$'s item, which is
how a borrow is retired. After the four commands the stack is what it was
after the first; only the tag counter remembers that $u$ existed. That
observation is @lem:cancel, on which the correctness proof turns.

#ruletable(
  [Stacked Borrows rules at one cell $a$. $x$ and $y$ range over lists of items, $x$ being the part of the stack above the granting item; $"tag"(iota)$ is the tag an item carries; $"dis"(x)$ replaces each $"MutRef"(u)$ in $x$ by $"Disabled"(u)$. No rule applies when a removed or disabled item is protected (@sec:surface).],
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
    [$⟨ "op"(a+j, dots), Pi_j ⟩ #dA Pi_(j+1)$ for $0 <= j < n$, \ one fresh tag shared by all $n$ cells],
    [$"op"(Pi_0, a, n, dots) = Pi_n$]),
) <tab:sb>

Three points of the model matter later. A read through $t$ does not remove
the mutable borrows above $t$: #sb-read _disables_ them in place, because
removing them would merge the raw-pointer groups on either side. A
raw-mutable retag performs no access and inserts its item directly above
its parent (#sb-refr), so sibling raw pointers share one group instead of
invalidating each other. And every operation of the interface ranges over
$n$ cells from $a$ (#sb-range): $"own"(Pi,a,n)=(Pi',t)$,
$"read"(Pi,a,n,t)=Pi'$, $"useMut"(Pi,a,n,t)=Pi'$,
$"ref"(Pi,a,n,t,k,c,m)=(Pi',u)$, and $"die"(Pi,a,n,t)=Pi'$. The per-cell
granularity is what makes the width of a borrow observable, and hence what
the compiler must get right in @sec:compiler.

In the mechanization the operations are `sb_own`, `sb_read`, `sb_write`,
`sb_ref`, and `sb_die` in `src/obseq3/sb.lean`; the paper writes `useMut`
for `sb_write` to keep the source-level reading.

== MIRLite <sec:mirlite>

#grammarfig(
  [Grammar, configuration, and types of MIRLite. The main text covers these forms; @fig:surface-grammar has the rest.],
  panel([Terms], bnf(
    prod($"Program"$, $"Stmt"^* thick "halt"$),
    prod($"Stmt" in.rev s$, $d := e$, $"halt"$),
    prod($"Place" in.rev p, d$, $ell$, $p.q$, $#dr p$),
    prod($"Path" in.rev q$, $epsilon$, $j.q$),
    prod($"Expr" in.rev e$, $"const"(w)$, $"copy"(p)$, $"ref"(k,c,m,p)$),
    prod($"Kind" in.rev k$, $"shared" | "mutable"$, $"raw-const" | "raw-mut"$, $"two-phase"$),
    prod($c$, $"true" | "false"$),
    prod($m$, $[c_0,dots,c_(n-1)]$),
  )),
  [
    #panel([Configuration], bnf(
      prod($"State" in.rev S$, $(i, E, mu, Pi)$),
      prod($E$, $ell harpoon.rt (a, t)$),
      prod($mu$, $a harpoon.rt v$),
      prod($"Value" in.rev v$, $"undef"$, $"word"(w)$, $"ptr"(b,o,N,t)$),
      prod($"Res"$, $"res"(a,t,b,N)$),
      prod($i, a, b, o, N$, $NN$),
      prod($"Tag" in.rev t, u$, $NN$),
    ))
    #panel([Types], bnf(
      prod($"Layout" in.rev tau, sigma$, $"Nat"$, $"Ptr" tau$, $(tau_0,dots,tau_(n-1))$),
      prod($Gamma$, $[tau_0,dots,tau_(n-1)]$),
    ))
  ],
) <fig:mir-grammar>

MIRLite is a typed, sequential language for the memory-level part of Rust
that matters to borrow reasoning (@fig:mir-grammar). A program is a list of
statements. A statement assigns an expression to a place, or halts. A
_place_ is a local $ell$, a projection $p.q$ of a place along a path, or a
dereference $#dr p$. An _expression_ is a constant, a copy of a place, or a
reference to a place. We do not model control flow in the main text; the
guarded assignment of the full language is in @sec:surface.

*Types.* A _layout_ $tau$ describes the shape of a memory region, and $|tau|$
is its width in cells:

#align(center)[
  $|"Nat"|=1 quad |"Ptr" tau|=1 quad
    |(tau_0,...,tau_(n-1))|=sum_(j=0)^(n-1)|tau_j|.$
]

The pointee of $"Ptr" tau$ is statically significant even though every
pointer occupies one cell. Both $sigma$ and $tau$ range over layouts; the
choice records a role. When a judgment involves two layouts, $sigma$ is the
region being traversed and $tau$ the region selected from it. A context
$Gamma$ lists the layouts of the locals, and a typed local $ell:tau$ is an
index $j$ with $Gamma_j=tau$. Paths are typed: $q:sigma arrow.r tau$ means
that following $q$ through a $sigma$-shaped region selects a $tau$-shaped
one, at cell offset $"off"(q)$ with $"off"(q)+|tau| <= |sigma|$. Places are
indexed by the layout they select: $Gamma tack ell:tau$ if
$ell:tau in Gamma$; $Gamma tack p.q:tau$ if $Gamma tack p:sigma$ and
$q:sigma arrow.r tau$; and $Gamma tack #dr p:tau$ if
$Gamma tack p:"Ptr" tau$. Expressions and statements are indexed the same
way: $"const"(w)$ has layout `Nat`, $"copy"(p)$ the layout of $p$,
$"ref"(k,c,m,p)$ the layout $"Ptr" tau$ when $Gamma tack p:tau$, and
$d:=e$ requires $d$ and $e$ to have the same layout. In the running program
$x.1.0$ is the nested place $(x.q_1).q_0$ with
$q_1:("Nat",("Nat","Nat")) arrow.r ("Nat","Nat")$, $"off"(q_1)=1$ and
$q_0:("Nat","Nat") arrow.r "Nat"$, $"off"(q_0)=0$.

*Reference formation.* The retag kind $k$ is not limited to Rust
references: `raw-const` and `raw-mut` create read-only and mutable
raw-pointer items, and `two-phase` creates a reserved mutable borrow.
Reference formation also takes a protector flag $c$ and an
interior-mutability mask $m$; both are inert in the main text
($c="false"$, $m=[]$) and are defined in @sec:surface.

*Configuration.* A _cell value_ is undefined, a machine word, or a pointer.
A memory $mu$ is a partial map from addresses to cell values together with
the next bump-allocation address and the list of allocated ranges. Write
$mu(a)$ for the cell at $a$, which is `undef` when the map has no entry
there; $mu[a..a+n)$ for the list of $n$ cells from $a$; and
$mu[a |-> overline(v)]$ for the memory with the cells from $a$ replaced by
the list $overline(v)$. The environment $E$ maps a local either to no
binding or to an allocation base and its owning tag. A state is
$S=(i,E,mu,Pi)$ with $i$ the program counter. @tab:mir gives the rules;
<sec:state> they use three judgments, which we introduce before the
interpreter.

#ruletable(
  [MIRLite semantics. All rules describe successful branches. An unbound local in a read, a malformed or out-of-bounds pointer, or a rejection by the permission model is an error and has no successor.],
  ir(m-local,
    [$E(ell)=(a,t)$, #h(3pt) $ell : tau$],
    [$S tack ell #dP ("res"(a,t,a,|tau|), Pi)$]),
  ir(m-proj,
    [$S tack p #dP ("res"(a,t,b,N), Pi')$],
    [$S tack p.q #dP ("res"(a+"off"(q),t,b,N), Pi')$]),
  ir(m-deref,
    [$S tack p #dP ("res"(a,t,b,N), Pi_1)$, #h(3pt) $b <= a < b+N$, \ $"read"(Pi_1,a,1,t)=Pi_2$, #h(3pt) $mu(a)="ptr"(b',o',N',t')$],
    [$S tack #dr p #dP ("res"(b'+o',t',b',N'), Pi_2)$]),
  ir(m-pbound,
    [$"lookup"(S,d)$ is defined],
    [$"prepare"(S,d)=S$]),
  ir(m-palloc,
    [$"lookup"(S,d)$ undefined, #h(3pt) $"root"(d)=ell:tau$, #h(3pt) $E(ell)=bot$, \ $"alloc"(mu,|tau|)=(b,mu')$, #h(3pt) $"own"(Pi,b,|tau|)=(Pi',t)$],
    [$"prepare"(S,d)=(i, E[ell |-> (b,t)], mu', Pi')$]),
  ir(m-const,
    [],
    [$S tack "const"(w) #dE (["word"(w)], S)$]),
  ir(m-copy,
    [$S tack p #dP ("res"(a,t,b,N), Pi_1)$, #h(3pt) $p:tau$, \ $a+|tau| <= b+N$, #h(3pt) $"read"(Pi_1,a,|tau|,t)=Pi_2$],
    [$S tack "copy"(p) #dE (mu[a..a+|tau|), S[Pi |-> Pi_2])$]),
  ir(m-ref,
    [$S tack p #dP ("res"(a,t,b,N), Pi_1)$, #h(3pt) $p:tau$, \ $a+|tau| <= b+N$, #h(3pt) $"ref"(Pi_1,a,|tau|,t,k,c,m)=(Pi_2,u)$],
    [$S tack "ref"(k,c,m,p) #dE$ \ $quad (["ptr"(b,a-b,N,u)], S[Pi |-> Pi_2])$]),
  ir(m-assgn,
    [$P(i) = (d := e)$, #h(3pt) $"prepare"(S,d)=S_1$, \ $S_1 tack e #dE (overline(v), S_2)$, #h(3pt) $S_2 tack d #dP ("res"(a,t,b,N), Pi_3)$, \ $a+"len"(overline(v)) <= b+N$, #h(3pt) $"useMut"(Pi_3,a,"len"(overline(v)),t)=Pi_4$],
    [$(i,E,mu,Pi) smir$ \ $quad (i+1, E_2, mu_2[a |-> overline(v)], Pi_4)$]),
  ir(m-halt,
    [$P(i) = "halt"$ or $P(i)=bot$],
    [$S smir S$]),
) <tab:mir>

*Place resolution ($#dP$).* The judgment
$S tack p #dP ("res"(a,t,b,N),Pi')$ turns a well-typed place into a
_resolved place_: current address $a$, access tag $t$, allocation base $b$,
and allocation extent $N$. It does not write memory, but it can change the
permission state. #m-local reads the environment. #m-proj is typed address
arithmetic: it preserves provenance, bounds, and permissions. #m-deref
changes provenance, because the pointer _value_, not the place holding it,
identifies the referent; loading that value is a one-cell `read` through
the tag of the place that holds it. Nested dereferences thread these
permission changes from the inside out. A separate _pure lookup_,
$"lookup"(S,p)$, follows the same address calculation but only inspects the
pointer cell, with neither a bounds check nor a `read`. It is used only to
decide whether an assignment root must be allocated.

*Expression evaluation ($#dE$).* The judgment
$S tack e #dE (overline(v),S')$ produces exactly $|tau|$ cells for an
expression of layout $tau$. #m-copy and #m-ref resolve their place and then
act on the entire selected range: one `read`, or one `ref`, of width
$|tau|$. Reading an absent but permitted cell yields `undef`. The pointer
built by #m-ref carries the fresh tag $u$ and the allocation's base and
extent, so later bounds checks are against the whole allocation.

*Interpreter ($smir$).* A step fetches $P(i)$. #m-assgn runs four phases in
a fixed order: prepare the destination's root, evaluate the expression,
resolve the destination, write. Preparation (#m-pbound, #m-palloc) allocates
the root local of $d$ when it is unbound: the bump allocator returns a
fresh base $b$, `own` a fresh tag $t$, and $E$ is extended. A destination
rooted through a dereference is never allocated implicitly; that case is
an error. Crucially, _the whole expression is evaluated before the
destination is resolved_. Hence $"copy"(p)$ materializes its cells before
a destination access can invalidate a tag that $p$ needs. $E_2$ and $mu_2$
in the conclusion are the environment and memory of $S_2$. We write
$S attach(arrow.r.double.long, t: P, b: n) S'$ for $n$ steps; `halt` and a
missing statement are fixed points (#m-halt), so extra fuel is harmless.

#statetable(
  [Stepwise execution of the running program in MIRLite: the state after each statement. $E$, $mu$, and the stacks are cumulative; a dash means unchanged. "next" is $Pi."NextTag"$.],
  ([Statement], [$E$], [$mu$], [$Pi$]),
  (23%, 17%, 25%, 35%),
  ([0: #h(3pt) $x.0 := "const"(5)$],
   [$x |-> (0,1)$],
   [$0 |-> "word"(5)$],
   [$0,1,2 |-> ["Own"(1)]$; next 2]),
  ([1: #h(3pt) $x.1.0 := "const"(42)$],
   [---],
   [$1 |-> "word"(42)$],
   [---]),
  ([2: #h(3pt) $y := "ref"("mutable",dots,x.1.0)$],
   [$y |-> (3,2)$],
   [$3 |-> "ptr"(0,1,3,3)$],
   [$3 |-> ["Own"(2)]$, \ $1 |-> ["MutRef"(3),"Own"(1)]$; next 4]),
  ([3: #h(3pt) $#dr y := "const"(7)$],
   [---],
   [$1 |-> "word"(7)$],
   [---]),
  ([4: #h(3pt) $"halt"$], [---], [---], [---]),
) <tab:mir-example>

*Example.* @tab:mir-example executes the running program from the empty
state. Statement 0: $x$ is unbound, so #m-palloc allocates the three cells
$[0,3)$ and #sb-own gives each the item $"Own"(1)$; #m-const produces
$["word"(5)]$; #m-local and #m-proj resolve $x.0$ to
$"res"(0,1,0,3)$; and #m-assgn writes cell 0 after a `useMut` through tag
1, which #sb-use accepts without changing the stack. Statement 1:
preparation is #m-pbound. Two applications of #m-proj resolve $(x.q_1).q_0$
to $"res"(1,1,0,3)$; the inner, zero-offset projection changes neither the
address nor the provenance. There is no source retag: both projections are
structural, and the write uses the owner's tag directly. Cell 2, the
sibling $x.1.1$, is untouched. Statement 2: #m-palloc allocates $y$ at
address 3 with owning tag 2, _before_ the expression is evaluated; #m-ref
resolves $x.1.0$ as before and #sb-refm pushes $"MutRef"(3)$ on cell 1
only; the pointer $"ptr"(0,1,3,3)$ is stored in $y$. Statement 3: #m-deref
resolves $y$ to $"res"(3,2,3,1)$, performs a one-cell `read` of cell 3
through tag 2 (#sb-read, no change), and returns
$"res"(1,3,0,3)$, the address and tag _loaded from memory_. #m-assgn then
writes 7 through tag 3, which is on top of cell 1's stack.

#source([Formalization of the typed syntax and source transition system: `src/obseq3/syntax.lean` and `src/obseq3/mirlite_semantics.lean`.])

== OSEA-IR <sec:oseair>

#grammarfig(
  [Grammar and configuration of OSEA-IR (left, top right), and the state of the compiler (bottom right). @fig:surface-grammar has the remaining instructions.],
  panel([Terms], bnf(
    prod($"Program" in.rev Q$, $j harpoon.rt "Instr"$),
    prod($"Instr" in.rev I$, $r := h$, $"store"_theta (r_s, r_p)$, $"storec"_theta (overline(v), r_p)$, $"die"(r, n)$, $"halt"$),
    prod($"Rhs" in.rev h$, $"load"_theta (r)$, $"alloc"_theta$, $"borrow"(k,c,m,n,r,delta)$),
    prod($"Register" in.rev r$, $"R"_0 | "R"_1 | dots$),
  )),
  [
    #panel([Configuration], bnf(
      prod($"State" in.rev T$, $(j, R, mu_t, Pi_t)$),
      prod($R$, $r harpoon.rt (theta, overline(v))$),
      prod($mu_t$, $a harpoon.rt v$),
      prod($"Value" in.rev v$, $"undef"$, $"dat"(w)$, $"ptr"(b,o,s,t)$),
      prod($"Type" in.rev theta$, $"NatTy" | "PTy"$, $"TupTy"([theta_0,dots,theta_(n-1)])$),
    ))
    #panel([Compiler state], bnf(
      prod($C$, $(n_r, n_l, K, L)$),
      prod($K$, $j harpoon.rt "Instr"$),
      prod($L$, $ell harpoon.rt (r, tau)$),
      prod($D$, $[(r_0,n_0),dots]$),
    ))
  ],
) <fig:oseair-grammar>

OSEA-IR is a register machine that exposes the memory and permission events
implicit in a MIRLite statement (@fig:oseair-grammar). A source place is
gone: an instruction names a register holding a concrete pointer, an
offset, and a number of cells. Consequently one source step may need several
target steps and may create short-lived tags with no source counterpart. A
program $Q$ is a _partial_ map from labels to instructions, which lets the
compiler extend code without renumbering an earlier fragment. Instructions
are register assignments $r := h$, stores of a register or of a constant
through a pointer, the retirement `die` of a borrow, and `halt`. A
right-hand side $h$ loads through a pointer, allocates, or borrows.
<sec:target-values>

*Configuration.* Target values mirror source values, with `dat` for a
machine word; the pointer fields have the same meaning as at the source. A
register holds a runtime type and an _entire cell list_; the register file
is a finite shadowing map. Runtime types are distinct from layouts. The
erasure $floor(tau)$ maps a layout to a runtime type,

#align(center)[
  $floor("Nat")="NatTy" quad
   floor("Ptr" tau)="PTy" quad
   floor((tau_0,dots,tau_(n-1)))="TupTy"([floor(tau_0),dots,floor(tau_(n-1))]),$
]

so OSEA-IR records that a register holds a pointer but not the pointee's
layout, and $"typeSize"(floor(tau))=|tau|$. A target state is
$T=(j,R,mu_t,Pi_t)$; memory carries a bump-allocation watermark and an
allocation table as at the source, and the permission state is the same
Stacked Borrows instance. @tab:osea gives the rules.

#ruletable(
  [OSEA-IR semantics. In every rule that reads $R(r)$, the register must hold exactly one pointer; its stored runtime type $theta_r$ is immaterial.],
  ir(t-load,
    [$R(r)=(theta_r,["ptr"(b,o,s,t)])$, #h(3pt) $a=b+o$, \ $a+"typeSize"(theta) <= b+s$, \ $"read"(Pi_t,a,"typeSize"(theta),t)=Pi'_t$],
    [$T tack "load"_theta (r) #dH$ \ $quad (theta, mu_t [a..a+"typeSize"(theta)), T[Pi_t |-> Pi'_t])$]),
  ir(t-alloc,
    [$n = "typeSize"(theta)$, #h(3pt) $"alloc"(mu_t,n)=(b,mu'_t)$, \ $"own"(Pi_t,b,n)=(Pi'_t,u)$],
    [$T tack "alloc"_theta #dH$ \ $quad ("PTy", ["ptr"(b,0,n,u)], T[mu_t |-> mu'_t, Pi_t |-> Pi'_t])$]),
  ir(t-borrow,
    [$R(r)=(theta_r,["ptr"(b,o,s,t)])$, #h(3pt) $a=b+o+delta$, \ $a+n <= b+s$, #h(3pt) $"ref"(Pi_t,a,n,t,k,c,m)=(Pi'_t,u)$],
    [$T tack "borrow"(k,c,m,n,r,delta) #dH$ \ $quad ("PTy", ["ptr"(b,o+delta,s,u)], T[Pi_t |-> Pi'_t])$]),
  ir(t-assgn,
    [$Q(j) = (r := h)$, \ $(j,R,mu_t,Pi_t) tack h #dH (theta, overline(v), (j,R,mu_1,Pi_1))$],
    [$(j,R,mu_t,Pi_t) ssea$ \ $quad (j+1, R[r |-> (theta,overline(v))], mu_1, Pi_1)$]),
  ir(t-store,
    [$Q(j) = "store"_theta (r_s,r_p)$, #h(3pt) $R(r_s)=(theta,overline(v))$, \ $R(r_p)=(theta_p,["ptr"(b,o,s,t)])$, #h(3pt) $a=b+o$, \ $a+"len"(overline(v)) <= b+s$, #h(3pt) $"useMut"(Pi_t,a,"len"(overline(v)),t)=Pi'_t$],
    [$(j,R,mu_t,Pi_t) ssea$ \ $quad (j+1, R, mu_t [a |-> overline(v)], Pi'_t)$]),
  ir(t-storec,
    [$Q(j) = "storec"_theta (overline(v),r_p)$, #h(3pt) $"len"(overline(v))="typeSize"(theta)$, \ $R(r_p)=(theta_p,["ptr"(b,o,s,t)])$, #h(3pt) $a=b+o$, \ $a+"len"(overline(v)) <= b+s$, #h(3pt) $"useMut"(Pi_t,a,"len"(overline(v)),t)=Pi'_t$],
    [$(j,R,mu_t,Pi_t) ssea$ \ $quad (j+1, R, mu_t [a |-> overline(v)], Pi'_t)$]),
  ir(t-die,
    [$Q(j) = "die"(r,n)$, #h(3pt) $R(r)=(theta_r,["ptr"(b,o,s,t)])$, \ $"die"(Pi_t,b+o,n,t)=Pi'_t$],
    [$(j,R,mu_t,Pi_t) ssea (j+1, R, mu_t, Pi'_t)$]),
  ir(t-halt,
    [$Q(j) = "halt"$ or $Q(j)=bot$],
    [$T ssea T$]),
) <tab:osea>

*RHS evaluation ($#dH$).* The judgment
$T tack h #dH (theta,overline(v),T')$ evaluates a right-hand side to a
runtime type, a cell list, and a state. It may update memory or
permissions but does not advance $j$. #t-load checks the complete range
and then reads it through the pointer's tag. #t-borrow retags $n$ cells at
offset $delta$ from the pointer and returns the same pointer, moved by
$delta$ and carrying the fresh tag; offsets are natural numbers, so there
is no negative-offset case, and a zero-length borrow at one past the end
is legal. #t-alloc is the only rule of the main text that changes both
memory and permissions.

*Interpreter ($ssea$).* #t-assgn evaluates its right-hand side _before_
inserting the returned entry. The two stores share one write-through-pointer
helper: extract one pointer from $r_p$, check the range, `useMut`, write,
advance. They differ in where the cells come from: #t-store checks that
$r_s$ holds exactly the runtime type $theta$, and #t-storec that the
constant has the right length. #t-die has no separate range check: its
admissibility is exactly that of the permission operation. There is no
global well-formedness premise on register files; the instruction that
consumes a register checks the shape it needs, which keeps malformed
programs executable with explicit errors. We write
$T attach(arrow.r.double.long, t: Q, b: n) T'$ for exactly $n$ steps.
Iteration does not stop early at a fixed point (#t-halt), which makes the
target step count of the simulation existential without a separate
reflexive-transitive closure.

#statetable(
  [Stepwise execution of the compiled running program in OSEA-IR: the state after each instruction. The $R$ column shows the binding added; registers are never removed. Label groups are source statements 0 to 4. $theta_x = "TupTy"(["NatTy","TupTy"(["NatTy","NatTy"])])$; $"mut"$ abbreviates $"mutable","false",[]$.],
  ([Instruction], [$R$], [$mu_t$], [$Pi_t$]),
  (31%, 21%, 19%, 29%),
  ([0: #h(3pt) $"R"_0 := "alloc"_(theta_x)$],
   [$"R"_0 |-> "ptr"(0,0,3,1)$], [---], [$0,1,2 |-> ["Own"(1)]$; next 2]),
  ([1: #h(3pt) $"storec"_"NatTy" (["dat"(5)], "R"_0)$],
   [---], [$0 |-> "dat"(5)$], [---]),
  ([2: #h(3pt) $"R"_1 := "borrow"("mut",1,"R"_0,1)$],
   [$"R"_1 |-> "ptr"(0,1,3,2)$], [---], [$1 |-> ["MutRef"(2),"Own"(1)]$; next 3]),
  ([3: #h(3pt) $"storec"_"NatTy" (["dat"(42)], "R"_1)$],
   [---], [$1 |-> "dat"(42)$], [---]),
  ([4: #h(3pt) $"die"("R"_1, 1)$],
   [---], [---], [$1 |-> ["Own"(1)]$]),
  ([5: #h(3pt) $"R"_2 := "alloc"_"PTy"$],
   [$"R"_2 |-> "ptr"(3,0,1,3)$], [---], [$3 |-> ["Own"(3)]$; next 4]),
  ([6: #h(3pt) $"R"_3 := "borrow"("mut",1,"R"_0,1)$],
   [$"R"_3 |-> "ptr"(0,1,3,4)$], [---], [$1 |-> ["MutRef"(4),"Own"(1)]$; next 5]),
  ([7: #h(3pt) $"store"_"PTy" ("R"_3, "R"_2)$],
   [---], [$3 |-> "ptr"(0,1,3,4)$], [---]),
  ([8: #h(3pt) $"R"_4 := "load"_"PTy" ("R"_2)$],
   [$"R"_4 |-> "ptr"(0,1,3,4)$], [---], [---]),
  ([9: #h(3pt) $"storec"_"NatTy" (["dat"(7)], "R"_4)$],
   [---], [$1 |-> "dat"(7)$], [---]),
  ([10: #h(3pt) $"halt"$], [---], [---], [---]),
) <tab:osea-example>

*Example.* @tab:osea-example executes the code the compiler emits for the
running program (@fig:compile-example). Label 0 allocates by #t-alloc,
which issues #sb-own\; label 1 stores a constant by #t-storec through the
owner's tag. Labels 2 to 4 are one source write: #t-borrow issues #sb-refm
on cell 1 alone, minting tag 2; #t-storec writes through tag 2; and #t-die
issues #sb-die, after which cell 1's stack is again $["Own"(1)]$. The
target's only memory update is the source's one-cell update, but its tag
counter is now one ahead of the source's. Labels 5 to 7 allocate $y$, mint
the reference, and store it with #t-store: the owning tag of $y$ is 3 here
and 2 at the source, and the stored reference carries tag 4 here and 3 at
the source. Label 8 loads that pointer by #t-load, a read of cell 3 through
tag 3, and label 9 writes through the loaded tag 4. The register $"R"_1$
still holds a pointer with the dead tag 2; registers are not observable, so
the simulation of @sec:correctness ignores it.

#source([Formalization of target values, RHS evaluation, instruction stepping, and fuelled execution: `src/obseq3/oseair.lean`.])

== Compiler <sec:compiler>

The compiler is a state-passing translation from typed MIRLite syntax to
OSEA-IR code. Its obligation is to preserve the source evaluation order
while introducing explicit loads, retags, stores, and the retirement of
the tags it introduces. A compiler state is $C=(n_r,n_l,K,L)$
(@fig:oseair-grammar, bottom right): $n_r$ and $n_l$ are the next fresh
register and label, $K$ is the emitted code map, and $L$ maps a source
local to a register and a source layout; code uses the layout's erasure.
Write $C emit [I_0,dots,I_(n-1)]$ for the state that installs the list at
labels $[n_l, n_l+n)$ and advances $n_l$ by $n$, and "$r$ fresh in $C$" for
$r="R"_(n_r)$ with $n_r$ advanced. Every compiler computation is monotone:
counters do not decrease, code below the old $n_l$ is unchanged, and every
old entry of $L$ remains. A cleanup list $D$ records borrows to retire;
$"cleanup"(D)$ reverses $D$ and maps each entry $(r,n)$ to $"die"(r,n)$.
@tab:compile gives the rules.

#ruletable(
  [Compilation rules. $"root"(d)$ is the local reached from $d$ through projections and dereferences. In #c-proj0 and #c-projd the base $b$ is not itself a projection (#c-assoc applies first), and the selected place has layout $tau$.],
  cols: (40%, 46%, 14%),
  ir(c-rbound,
    [$"root"(d)=ell$, #h(3pt) $L(ell)$ defined],
    [$C tack "root"(d) arrow.r C$]),
  ir(c-ralloc,
    [$"root"(d)=ell:tau$, #h(3pt) $L(ell)=bot$, #h(3pt) $r$ fresh in $C$],
    [$C tack "root"(d) arrow.r$ \ $quad (C emit [r := "alloc"_(floor(tau))])[L(ell) |-> (r,tau)]$]),
  ir(c-local,
    [$L(ell)=(r,tau)$],
    [$C scripts(tack)_k ell #dCP (r, [], C)$]),
  ir(c-assoc,
    [$C scripts(tack)_k b.(q dot p) #dCP (r, D, C')$],
    [$C scripts(tack)_k (b.q).p #dCP (r, D, C')$]),
  ir(c-proj0,
    [$"off"(q)=0$, #h(3pt) $C scripts(tack)_k b #dCP (r_b, D_b, C')$],
    [$C scripts(tack)_k b.q #dCP (r_b, D_b, C')$]),
  ir(c-projd,
    [$delta="off"(q)>0$, #h(3pt) $C scripts(tack)_k b #dCP (r_b, D_b, C_1)$, \ $r_f$ fresh in $C_1$, \ $I = (r_f := "borrow"(k,"false",[],|tau|,r_b,delta))$],
    [$C scripts(tack)_k b.q #dCP$ \ $quad (r_f, D_b plus.double [(r_f,|tau|)], C_1 emit [I])$]),
  ir(c-deref,
    [$C scripts(tack)_"shared" p #dCP (r_p, D_p, C_1)$, #h(3pt) $r$ fresh in $C_1$],
    [$C scripts(tack)_k #dr p #dCP (r, [],$ \ $quad C_1 emit [r := "load"_"PTy" (r_p)] emit "cleanup"(D_p))$]),
  ir(c-blocal,
    [$L(ell)=(r_b,tau)$, #h(3pt) $r$ fresh in $C$],
    [$C scripts(tack)_(k,c,m) ell #dCB$ \ $quad (r, C emit [r := "borrow"(k,c,m,|tau|,r_b,0)])$]),
  ir(c-bproj,
    [$C scripts(tack)_k b #dCP (r_b, D_b, C_1)$, #h(3pt) $r$ fresh in $C_1$],
    [$C scripts(tack)_(k,c,m) b.q #dCB$ \ $quad (r, C_1 emit [r := "borrow"(k,c,m,|tau|,r_b,"off"(q))])$]),
  ir(c-bderef,
    [$C scripts(tack)_"shared" p #dCP (r_p, D_p, C_1)$, \ $r_l, r$ fresh in $C_1$],
    [$C scripts(tack)_(k,c,m) #dr p #dCB (r, C_1 emit [r_l := "load"_"PTy" (r_p)]$ \ $quad emit "cleanup"(D_p) emit [r := "borrow"(k,c,m,|tau|,r_l,0)])$]),
  ir(c-const,
    [],
    [$C tack "const"(w) #dCR$ \ $quad (lambda r_d. ["storec"_"NatTy" (["dat"(w)], r_d)], C)$]),
  ir(c-copy,
    [$C scripts(tack)_"shared" p #dCP (r_s, D_s, C_1)$, #h(3pt) $p:tau$, \ $r_v$ fresh in $C_1$],
    [$C tack "copy"(p) #dCR (lambda r_d. ["store"_(floor(tau)) (r_v, r_d)],$ \ $quad C_1 emit [r_v := "load"_(floor(tau)) (r_s)] emit "cleanup"(D_s))$]),
  ir(c-ref,
    [$C scripts(tack)_(k,c,m) p #dCB (r_v, C_1)$],
    [$C tack "ref"(k,c,m,p) #dCR$ \ $quad (lambda r_d. ["store"_"PTy" (r_v, r_d)], C_1)$]),
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
the destination and records its register. For a dereference the root is
the pointer local. The source never allocates a pointee implicitly and
fails instead, so a forward simulation never observes that case. Read
lowering does not allocate a missing local: resolving a read requires that
the root already exist, and the compiler is _checked_, returning an error
for such a program.

*Place-to-register compilation ($#dCP$).* The judgment
$C scripts(tack)_k p #dCP (r,D,C')$ lowers place $p$, leaves a pointer to it in $r$,
and returns a cleanup list. Its index $k$ is the retag kind of any borrow
the lowering emits: reads lower their place with $k="shared"$ and
assignment destinations with $k="mutable"$. #c-local is a lookup. A
zero-offset projection reuses the base pointer (#c-proj0): it denotes the
same address and needs no narrower pointer. A nonzero projection emits a
borrow of the _final selected width_ (#c-projd). A dereference loads the
pointer cell (#c-deref) and retires the borrows that were needed to reach
that cell, but it returns an empty cleanup list: the loaded tag belongs to
the source program and must not be retired.

#definition("Route borrow")[
  A _route borrow_ is the `borrow` instruction emitted by #c-projd to
  obtain a pointer to a projected subregion of a place that the compiled
  code already holds a pointer to. Its fresh tag is a _route tag_. A route
  borrow is unprotected, has an empty mask, and spans exactly the width of
  the layout selected by the place. Its register and width are recorded as
  an entry $(r,n)$ of the cleanup list $D$, and the tag is retired by
  $"die"(r,n)$ before the next source-statement boundary. A route tag is
  never stored to memory by the compiled code and has no source
  counterpart.
] <def:route>

Route tags are the only tags the compiled code mints that the source does
not. Every other target retag corresponds to a source `ref` and produces a
tag that the source program also stores.

*Flattening.* A place may contain nested projections, but emitting a borrow
for each syntactic layer would change the accessed ranges. #c-assoc fuses
adjacent paths before any borrow is emitted; it is the on-the-fly form of

```lean
def projInto : Place Γ σ → PathTo σ τ → Place Γ τ
  | .proj b q, p => .proj b (q.append p)
  | b,        p => .proj b p

def flattenPlace : Place Γ τ → Place Γ τ
  | .local l     => .local l
  | .deref p     => .deref (flattenPlace p)
  | .proj b path => projInto (flattenPlace b) path
```

where, for $q:sigma_0 arrow.r sigma$ and $p:sigma arrow.r tau$, the
composed path satisfies $q dot p:sigma_0 arrow.r tau$ and
$"off"(q dot p)="off"(q)+"off"(p)$. Flattening stops at a dereference,
because an offset cannot be moved across a memory-loaded pointer. It
preserves the selected layout and the source resolution result. For
$x.1.0$, lowering without #c-assoc would borrow the two-cell field $x.1$
and then reuse its zero-offset subfield, touching cells 1 and 2. With it,
the compiler emits one borrow of width one at the composed offset one and
leaves the sibling $x.1.1$ alone.

*Escaping borrows ($#dCB$).* Reference formation needs the distinct
judgment $C scripts(tack)_(k,c,m) p #dCB (r,C')$. It follows the same path
normalization but _always_ ends in a $"borrow"(k,c,m,|tau|,dots)$,
including at offset zero (#c-blocal, #c-bproj), and for a dereference it
first loads the stored pointer and then borrows the pointed-to range
(#c-bderef). Its final tag is not a route tag and is never retired: it
escapes in the pointer value the program stores, and the correctness proof
extends the source-to-target tag map with it.

*Expression-to-instructions compilation ($#dCR$).*
The judgment $C tack e #dCR (F,C')$ emits all the work that precedes the
destination and returns a _store function_ $F$ that awaits the destination
register. #c-const emits nothing. #c-copy materializes the copied cells in
a register _before_ the destination is lowered. This is what realizes the
source rule's order, evaluate, then resolve the destination, then write,
when both resolutions have observable permission effects. #c-ref retains
the escaping tag. Every expression of the full language has the same
shape (@sec:surface).

*Compilation judgments ($sC$, $sPr$).* #c-assign is the only assignment
rule, for every destination: the emitted intervals concatenate as

#align(center)[
#box(width: 98%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"root"(d) ; quad "pre-code of" e ; quad "lowering of" d ; quad F(r_d) ; quad "cleanup"(D_d).$
]]

#c-pstep folds statement compilation from left to right from the initial
state $C_"init"=(0,0,emptyset,emptyset)$; the target program is the final
code map, or the first compiler error. For source
statement index $i$, compiling the prefix $P[0..i)$ from $C_0$ produces a
state $C_i$ whose next label $C_i.n_l$ is the target entry label of
statement $i$. Monotonicity gives the two facts simulation needs,

#align(center)[
  $C_i.n_l <= C_(i+1).n_l quad and quad
  forall j<C_i.n_l. thick C_(i+1).K(j)=C_i.K(j),$
]

so compiling later statements cannot change a fragment already emitted. No
fixed instruction-per-statement ratio is assumed.

#figure(
  kind: image,
  caption: [Compilation of the running program. Each row is one source statement and the labelled instructions emitted for it.],
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
      [0: #h(3pt) $"R"_0 := "alloc"_(theta_x)$ \ 1: #h(3pt) $"storec"_"NatTy" (["dat"(5)], "R"_0)$],
      [1: #h(3pt) $x.1.0 := "const"(42)$],
      [2: #h(3pt) $"R"_1 := "borrow"("mutable","false",[],1,"R"_0,1)$ \ 3: #h(3pt) $"storec"_"NatTy" (["dat"(42)], "R"_1)$ \ 4: #h(3pt) $"die"("R"_1, 1)$],
      [2: #h(3pt) $y := "ref"("mutable","false",[],x.1.0)$],
      [5: #h(3pt) $"R"_2 := "alloc"_"PTy"$ \ 6: #h(3pt) $"R"_3 := "borrow"("mutable","false",[],1,"R"_0,1)$ \ 7: #h(3pt) $"store"_"PTy" ("R"_3, "R"_2)$],
      [3: #h(3pt) $#dr y := "const"(7)$],
      [8: #h(3pt) $"R"_4 := "load"_"PTy" ("R"_2)$ \ 9: #h(3pt) $"storec"_"NatTy" (["dat"(7)], "R"_4)$],
      [4: #h(3pt) $"halt"$],
      [10: #h(3pt) $"halt"$],
    )
  },
) <fig:compile-example>

*Example.* We compile the running program from $C_"init"$
(@fig:compile-example), tracking $(n_r,n_l,L)$. Statement 0: $L(x)=bot$, so
#c-ralloc emits label 0 and sets $L(x)=("R"_0,tau_x)$; #c-const has no
pre-code; $x.0$ has offset zero, so #c-proj0 and #c-local return
$("R"_0,[])$ and emit nothing; $F("R"_0)$ is label 1. The state is
$(1,2,{x |-> "R"_0})$. Statement 1: #c-rbound\; #c-assoc rewrites
$(x.q_1).q_0$ to $x.(q_1 dot q_0)$ with offset $1+0=1$ and selected width
$|"Nat"|=1$; #c-projd emits the route borrow at label 2 and returns
$("R"_1,[("R"_1,1)])$; the store is label 3; the cleanup is label 4. Every
number is derived: path composition gives the offset, the selected layout
the borrow length, erasure gives `NatTy`, and reversing the singleton
cleanup list gives the `die`. Statement 2: #c-ralloc emits label 5 for $y$
_before_ the expression, mirroring #m-palloc\; #c-ref uses #c-bproj, whose
borrow at label 6 has the same shape as the route borrow of label 2 but is
recorded in no cleanup list; label 7 stores it. There is no `die`.
Statement 3: #c-deref lowers $y$ by #c-local, emits the load at label 8,
and returns $("R"_4,[])$; label 9 stores through the loaded pointer. There
is again no `die`: retiring $"R"_4$'s tag would pop the program's own
reference. The final state is $(5,11,{x |-> "R"_0, y |-> "R"_2})$, and its
code map is the program that @tab:osea-example executes.

#source([Formalization of compiler state growth, checked lowering, and program compilation: `src/obseq3/compile.lean`. Flattening and its semantic preservation are in `src/obseq3/proof/spine.lean`. The listing of @fig:compile-example is the witness `g14_paper_running_example` in `src/obseq3/compile_tests.lean`.])

== Correctness <sec:correctness>

Correctness is a forward simulation of successful executions. Literal state
equality is impossible: the target has registers and introduces route
tags (@def:route). The relation instead compares source-observable memory, local pointers,
and permission stacks at source-statement boundaries. This section defines
the relation (@def:rename to @def:inv), states the two lemmas the proof
turns on (@lem:mono and @lem:cancel), and then states the simulation
theorems (@thm:step to @cor:closed).

=== Renamings and value simulation

#definition("Renamings")[
  An _address renaming_ is a partial map $rho_a:NN arrow.r "option"(NN)$
  and a _tag renaming_ is a partial map
  $rho_t:"Tag" arrow.r "option"("Tag")$. A renaming $rho'$ _extends_
  $rho$, written $rho subset.eq rho'$, when $rho'$ agrees with $rho$
  wherever $rho$ is defined.
] <def:rename>

The tag map is partial because future tags have not yet been created.
The address renaming is kept in the statements for generality, but the
invariant below forces it to be the identity, and total, for a reason
that combines a property of the two machines with a property of the
compiler. Each machine allocates with a deterministic bump allocator that
never reuses addresses, and both start at the same watermark. The compiler
emits exactly one target allocation, of the same size, for each source
allocation, and in the same order. Hence the two watermarks stay equal at
every statement boundary, and each fresh block receives the same base on
both sides:

#align(center)[
  $rho_a(a)=a quad "for every address" a.$
]

Totality is what gives a meaning to the degenerate pointer that an
integer-to-pointer cast of an unallocated address yields
(@sec:surface-open). Tags genuinely require renaming: route borrows advance the
target tag counter, so a later source and target `ref` may mint different
numeric tags.

#definition("Value simulation")[
  Source cell value $v$ is simulated by target value $v'$ under
  $(rho_a,rho_t)$, written $v approx v'$, when one of the following holds.
  - $v="word"(w)$ and $v'="dat"(w)$.
  - $v="ptr"(b,o,s,t)$, $v'="ptr"(b',o,s,t')$, $rho_a(b)=b'$,
    $rho_t(t)=t'$, and every address in $[b,b+s)$ is in the domain of
    $rho_a$.
  - $v="undef"$, and $v'$ is arbitrary.
] <def:valsim>

Source `undef` relates to any target value because a successful core source
run cannot observe the missing information.

#definition("Memory simulation")[
  Source memory $mu_s$ is simulated by target memory $mu_t$ under
  $(rho_a,rho_t)$ when, for every address $a$ at which $mu_s$ has a cell $v$,
  $rho_a(a)$ is defined and $v approx mu_t(rho_a(a))$.
] <def:memsim>

The relation is forward only: every present source cell has a related target
cell at its mapped address, and extra unobservable target cells are permitted.

=== Permission simulation

#definition("Permission simulation")[
  Let items, stacks, and states be those of the Stacked Borrows instance of
  @sec:perm. Under $rho_t$:
  - Two _items_ are related when they have the same constructor and
    $rho_t$ maps the source tag to the target tag; raw-pointer items
    additionally carry the same mutability flag.
  - Two _stacks_ are related position by position, so their lengths agree.
  - Two _stack maps_ are related when, for every address $a$, either both
    lack an entry at $a$ or their entries at $a$ are related stacks.
  - Two _protector frame lists_ are related as lists of related tag lists,
    and two _exposed-tag lists_ are related as tag lists.
  Permission states $Pi_s$ and $Pi_t$ are related, written
  $Pi_s approx Pi_t$, when their stack maps, protector frames, and exposed
  lists are related and $Pi_s."NextTag" <= Pi_t."NextTag"$.
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
  $rho_t' = rho_t[t_s mapsto t_t].$
]

Because both fresh tags are minted at their machine's counter, and the
boundary invariant below keeps every mapped tag strictly below both
counters, neither fresh tag is already in the old map's domain or range, so
injectivity is preserved. By contrast, a route borrow never extends
$rho_t$, since there is no source tag to use as a key.

=== The boundary invariant

#definition("Boundary invariant")[
  Let $C_0$ be a compiler state and $P$ a source program. Source state
  $S=(i,E,mu_s,Pi_s)$ and target state $T=(j,R,mu_t,Pi_t)$ satisfy the
  _boundary invariant_ under $(rho_a,rho_t)$, written
  $S approx_(rho_a,rho_t)^(C_0,P) T$, when there is a compiler state $C_i$
  such that the following ten clauses hold.
  #set enum(numbering: n => [(I#n)])
  + _Control alignment._ Compiling the prefix $P[0..i)$ from $C_0$
    succeeds with state $C_i$, and $j=C_i.n_l$.
  + _Bound locals._ If $E(ell)=(a,t)$ for $ell:tau$, then
    $L_i(ell)=(r,tau)$ and $R(r)=("PTy",["ptr"(a,0,|tau|,t')])$ with
    $rho_a(a)=a$ and $rho_t(t)=t'$, and every address of $[a,a+|tau|)$ is in
    the domain of $rho_a$.
  + _Source memory._ $mu_s$ is simulated by $mu_t$ (@def:memsim).
  + _Permissions._ $Pi_s approx Pi_t$ (@def:permsim).
  + _Address identity._ $rho_a$ is the identity wherever defined.
  + _Tag-map shape._ $rho_t$ is injective and maps the wildcard tag to
    itself.
  + _Tag bounds._ Every source tag in the domain of $rho_t$ lies below
    $Pi_s."NextTag"$, and every tag in its range lies below
    $Pi_t."NextTag"$.
  + _Allocator lockstep._ The source and target bump-allocation
    watermarks are equal, the two allocation tables are equal, and
    $rho_a$ is defined at every address.
  + _Unbound locals._ If $E$ has no binding for $ell$, then $L_i$ has no
    entry for $ell$.
  + _Register freshness._ Every register in the range of $L_i$ is below
    $C_i.n_r$.
] <def:inv>

The invariant is required only at source-statement boundaries and is
deliberately strict about stack shape there. The compiled fragment may push
a route tag's item inside a fragment, but `die` removes it before the
invariant is re-established. Numeric next-tag counters may still differ,
which is why tags are renamed and the target counter need only be greater.

Each auxiliary clause discharges a specific obligation in the step proof.

- (I1) with @lem:mono: the instruction fetched at $j$ belongs to the fragment
  compiled for statement $i$, and compiling later statements has not
  overwritten it.
- (I2) with (I9): exactly one allocation regime applies to a destination
  root. Either a corresponding target pointer register exists, or both sides
  allocate.
- (I3) with (I5): a successful source read yields related target cells at
  the same concrete range, and writes update corresponding addresses.
- (I4) with (I6): related source-visible operations accept corresponding
  tags and leave related stacks after renaming.
- (I6) with (I7): a newly minted source and target tag pair extends $rho_t$
  without overwriting or aliasing an old pair.
- (I8) with (I5): fresh roots receive the same base on both sides, which
  is what makes the identity renaming of @def:rename sound, and both
  machines resolve an integer address to the same block.
- (I10): a fresh register cannot collide with a register that the target
  uses as a source-local pointer.

Dropping any clause leaves a concrete compiler case underdetermined. Memory
agreement alone cannot show that a fresh `load` register does not overwrite
$r_x$, and equal watermarks alone cannot show that an unbound source local
corresponds to a target fragment containing `alloc`.

=== Two lemmas

The step proof relies on a fact about the compiler and a fact about the
permission model.

#lemma("Prefix monotonicity")[
  Let $C_i$ and $C_(i+1)$ be the states obtained by compiling
  $P[0..i)$ and $P[0..i+1)$ from $C_0$. Then
  $C_i.n_l <= C_(i+1).n_l$, and $C_(i+1).K(q')=C_i.K(q')$ for every label
  $q'<C_i.n_l$.
] <lem:mono>

This is the monotonicity property of @sec:compiler specialized to
consecutive prefixes. It lets the proof locate a source boundary by replaying
prefix compilation, with no fixed instruction-per-statement ratio.

#lemma("Route borrow cancellation")[
  Let $Pi$ be a permission state whose next tag is not the wildcard and is
  not protected in any frame. Suppose
  $"ref"(Pi,a,n,t,"mutable","false",[])=(Pi_1,u)$. Then there are
  $Pi_2$, $Pi_3$, and $Pi_"acc"$ with
  $ "useMut"(Pi_1,a,n,u)=Pi_2, quad
    "die"(Pi_2,a,n,u)=Pi_3, quad
    "useMut"(Pi,a,n,t)=Pi_"acc", $
  such that $Pi_3$ and $Pi_"acc"$ have the same stack map, protector frames,
  and exposed list, and $Pi_"acc"."NextTag" <= Pi_3."NextTag"$.
] <lem:cancel>

@lem:cancel is the semantic content of the compiled write pattern
`borrow; store; die`. The three target events have exactly the stack effect
of the single source `useMut` through the parent tag, and differ only in the
tag counter. That difference is absorbed by the inequality in @def:permsim.
The two side conditions are invariants of every reachable permission state:
tags are minted from one upward, and protector frames only ever contain
already-minted tags.

=== Simulation theorems


Let `srcStep` fetch the source statement at the current PC and execute
it, treating `halt` and a missing statement as successful fixed points. The
_core fragment_ consists of `halt`, the two protector-frame statements, and
assignments, plain or guarded, whose expression is _any_ expression of the
full language (@sec:surface): a constant, a copy, a reference with any
retag kind $k$, protector flag $c$, and mask $m$, an uninitialized value, a
pointer cast or offset, a slice retag, or either exposed-provenance cast.
Here "any kind" includes shared, mutable, both raw pointer kinds, and
two-phase. Only heap `alloc` and `dealloc` lie outside the fragment. A
program is _core_ when every statement in it is.

#theorem("One-step forward simulation")[
  Let $P$ be a core program, $C_0$ any compiler state, and $Q$ the result
  of compiling $P$ from $C_0$. If
  $ S approx_(rho_a,rho_t)^(C_0,P) T quad "and" quad
    "srcStep"(P,S)="ok"(S'), $
  then there exist $rho_a' supset.eq rho_a$, $rho_t' supset.eq rho_t$, a
  target state $T'$, and $n_t$ such that
  $ Q tack T arrow.r^(n_t) T' quad "and" quad
    S' approx_(rho_a',rho_t')^(C_0,P) T'. $
] <thm:step>

The compiler state in the final invariant is still $C_0$. Compilation is not
executing alongside the target. The invariant internally recompiles the
appropriate prefix to identify the next target label. Only the renamings
grow during simulation. The target step count $n_t$ is existential because
fragments have different lengths. For `halt` or a missing source statement,
$n_t=0$.

#proof[
  Case on the source statement at $i$. For `halt` or a missing statement the
  source state is unchanged, and the invariant is re-established with
  $n_t=0$ and the same renamings. For an assignment $d:=e$, (I1) and
  @lem:mono recover the emitted label interval for statement $i$, and the
  proof executes it phase by phase, following the operational order of
  @tab:mir and the compiler order of @tab:compile:

  #align(center)[
  #table(
    columns: (1fr, auto, 1fr, auto, 1fr, auto, 1fr),
    inset: 3pt,
    stroke: 0.45pt + rule,
    fill: rgb("fafbfc"),
    align: center,
    [source RHS], [→], [target pre-code], [→], [destination and store], [→], [boundary invariant],
  )
  ]

  _RHS._ For a constant, source and target stores will write related
  singleton values. For a copy, (I3) and (I5) give related reads producing
  cell lists of equal length; the target register holds that list across
  destination resolution, which is what makes the source's
  evaluate-then-resolve order simulable. For an escaping reference, (I4)
  gives corresponding `ref` events that mint a fresh tag pair
  $(t_s,t_t)$; (I6) and (I7) let $rho_t$ extend by that pair, after which
  the two pointer values are related by @def:valsim.

  _Destination._ If the root is already bound, (I2) identifies the target
  register holding its pointer. If it is unbound, (I9) guarantees the
  compiled fragment contains the matching `alloc`; (I8) gives both
  allocators the same fresh base; corresponding `own` events mint a tag
  pair; $rho_a$ already covers the block, by (I8), and $rho_t$ extends by
  the tag pair. Typed paths give exact offsets and widths. A dereference
  destination loads a pointer related by (I3). (I10) ensures the loads and
  route borrows do not overwrite a register named by $L_i$.

  _Store and cleanup._ For a nonzero-offset destination the fragment ends in
  `borrow; store; die`. @lem:cancel shows the three target permission
  events equal the single source `useMut` up to the tag counter, under the
  _unchanged_ $rho_t$. Related writes restore (I3). The final target PC is
  $C_(i+1).n_l$, which re-establishes (I1) for $i+1$; the remaining
  clauses are preserved or extended as described.
]

The sketch shows the three expressions of the main text. Every other
expression lowers to the read-then-store shape of #c-copy
(@tab:surface-expr), so abstracting the copy case over the emitted
right-hand side makes its lemmas serve them all; what remains is one
simulation lemma per right-hand side. A guarded assignment adds a control
argument, that both outcomes of the guard land on the prefix label that
follows the assignment's fragment, and the protector-frame statements
preserve the nested tag-list relation of @def:permsim.

#theorem("Forward simulation of finite runs")[
  Let $P$ be a core program, $C_"init"$ the compiler state with empty code,
  counters zero, and an empty local map, and $Q$ the result of compiling
  $P$ from $C_"init"$. If
  $ S approx_(rho_a,rho_t)^(C_"init",P) T quad "and" quad
    "runS"^(n_s)(P,S)="ok"(S'), $
  then there exist $rho_a' supset.eq rho_a$, $rho_t' supset.eq rho_t$, a
  target state $T'$, and $n_t$ such that
  $ "runT"^(n_t)(Q,T)="ok"(T') quad "and" quad
    S' approx_(rho_a',rho_t')^(C_"init",P) T'. $
] <thm:run>

#proof[
  Induction on $n_s$. Each successful source statement uses @thm:step, and
  the induction hypothesis simulates the remainder. Extension of renamings
  is transitive, so the two extensions compose; target step counts compose
  by addition. When the source encounters `halt` or the end of the program,
  its fuelled semantics stops and the proof chooses zero further target
  steps.
]

@thm:run takes the initial invariant as a premise; it does not hide
initialization inside compilation. The premise is discharged for closed
programs by the following lemma.

#lemma("Initial relation")[
  Let $S_"init"$ and $T_"init"$ be the source and target states with empty
  environment, register file, and memory, PC zero, both bump allocators at
  watermark zero, and both permission states initialized. Let $rho_a$ be
  the identity and let $rho_t$ map only the wildcard tag to itself. Then
  $S_"init" approx_(rho_a,rho_t)^(C_"init",P) T_"init"$ for every $P$.
] <lem:init>

#proof[
  Each clause has a direct witness. Compiling the empty prefix returns
  $C_"init"$, whose next label is zero, giving (I1). (I2) and (I3) are
  vacuous. The two initial permission states have identical stack maps,
  frames, and exposed lists and compatible counters, giving (I4). (I5) and
  (I8) are immediate. The wildcard-only map is injective and lies below the
  initialized counters, giving (I6) and (I7). The empty local map gives (I9)
  and (I10).
]

#corollary("Closed programs")[
  Let $P$ be a core program and $Q$ its compilation from $C_"init"$. If
  $"runS"^(n_s)(P,S_"init")="ok"(S')$, then there exist $rho_a'$,
  $rho_t'$, $T'$, and $n_t$ with
  $"runT"^(n_t)(Q,T_"init")="ok"(T')$ and
  $S' approx_(rho_a',rho_t')^(C_"init",P) T'$.
] <cor:closed>

#proof[
  @thm:run with @lem:init.
]

These results are preservation of successful finite executions. They are
not backward simulation, divergence preservation, or an equivalence between
source and target error strings. Their observable consequences are the
memory and permission clauses of the final invariant, made explicit in
@cor:observe below.

=== The running program as a simulation

#statetable(
  [The running program as a simulation: the boundary invariant at each source-statement boundary. $i$ is the source PC and $j=C_i.n_l$ the target label (@fig:compile-example); the $rho_t$ column shows what the step _adds_ ($rho_a$ is the identity throughout); "next" is the pair of tag counters.],
  ([$i$], [$j$], [added to $rho_t$], [next], [how the invariant is re-established]),
  (5%, 5%, 15%, 8%, 67%),
  ([0], [0], [$0 |-> 0$], [1, 1], [@lem:init: empty states, wildcard-only tag map.]),
  ([1], [2], [$1 |-> 1$], [2, 2], [Unbound root: (I9) puts `alloc` in the fragment, (I8) gives both allocators base 0, the two `own` events mint the pair $(1,1)$.]),
  ([2], [5], [---], [2, 3], [@lem:cancel: `borrow; storec; die` has the stack effect of the source's one `useMut`. Route tag 2 is in no renaming; the counters part.]),
  ([3], [8], [$2 |-> 3$, \ $3 |-> 4$], [4, 5], [Unbound root again, then an escaping reference: (I4) relates the two `ref` events and (I6), (I7) let $rho_t$ grow by pairs that are _not_ numerically equal.]),
  ([4], [10], [---], [4, 5], [Dereferenced destination: (I3) relates the loaded $"ptr"(0,1,3,3)$ to $"ptr"(0,1,3,4)$, so both writes go through related tags to the same cell.]),
) <tab:sim-example>

#example[
  @tab:sim-example replays @tab:mir-example against @tab:osea-example.
  Each row is one application of @thm:step, and the first is @lem:init.

  _Boundary 1._ Statement 0 assigns to the unbound local $x$. Source
  preparation allocates $|tau_x|=3$ cells and obtains the owning tag 1;
  the target fragment begins with $"R"_0 := "alloc"_(theta_x)$, allocates
  the same base by (I8), and obtains tag 1. The proof extends $rho_t$ by $1 |-> 1$ and the local map by
  $x |-> ("R"_0,tau_x)$; the store establishes (I3) for cell 0.

  _Boundary 2._ Statement 1 is $x.1.0 := "const"(42)$. The source resolves
  the place to address 1 and performs $"useMut"(Pi_s,1,1,1)$. The target
  performs
  $ "ref"(Pi_t,1,1,1,"mutable","false",[])=(Pi_1,2), quad
    "useMut"(Pi_1,1,1,2)=Pi_2, quad
    "die"(Pi_2,1,1,2)=Pi'_t. $
  @lem:cancel removes the route tag's item and recovers (I4) under the
  _unchanged_ $rho_t$: tag 2 has no source counterpart and never escapes.
  Both memories update only cell 1, where source word 42 relates to target
  `dat(42)`, so (I3) is restored and cells 0 and 2 are framed. (I1)
  advances from source PC 1 to 2 and from target label 2 to the next prefix
  label 5. The target counter is now 3 and the source counter 2, which the
  inequality of @def:permsim absorbs.

  _Boundary 3._ Statement 2 allocates $y$ on both sides, with owning tags 2
  and 3, and then forms the reference, with tags 3 and 4. Neither pair is
  an equality, and neither could be: the route borrow of the previous
  statement advanced only the target counter. This is the step at which a
  tag renaming, rather than tag equality, is forced. The stored pointers
  $"ptr"(0,1,3,3)$ and $"ptr"(0,1,3,4)$ are related by @def:valsim, and
  the stacks at cell 1, $["MutRef"(3),"Own"(1)]$ and
  $["MutRef"(4),"Own"(1)]$, by @def:permsim.

  _Boundary 4._ Statement 3 writes through $y$. Both machines read cell 3
  through $y$'s owning tag, related by $2 |-> 3$, and obtain pointers
  related by (I3). The two writes therefore go through tags related by
  $3 |-> 4$, to the same cell. No tag is minted and none is retired.

  Flattening is semantically load-bearing at boundary 2. A route borrow of
  the intermediate width two would operate on cell 2 as well, so
  @lem:cancel would not simulate the source's one-cell write in the
  presence of a borrow of the sibling $x.1.1$. The compiled path must use
  the composed offset and the final width.
] <ex:sim>

The four formal views of the program thus line up. MIRLite's typed path
has input layout $tau_x$, selected layout `Nat`, composed offset one, and
width one. OSEA-IR begins with an erased `PTy` pointer in $"R"_0$, which
the compiler's local map connects to $x:tau_x$. Flattening prevents an
intermediate two-cell borrow, so place lowering creates exactly one route
tag for cell 1, and cleanup supplies the matching one-cell `die`. At each
boundary, address identity relates the updated cell, memory simulation
frames its neighbours, permission simulation cancels the route tag
without adding it to $rho_t$, and prefix compilation places the target at
the next fragment exactly when the source reaches the next statement:

#align(center)[
#box(width: 96%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"typed source range" arrow.r "flattened target route" arrow.r
    "explicit events" arrow.r "boundary simulation".$
]]

=== Observable consequences

#corollary("Observations at a boundary")[
  If $S approx_(rho_a,rho_t)^(C_0,P) T$, then:
  - if $mu_s(a)="word"(w)$, then $mu_t(a)="dat"(w)$;
  - if $mu_s(a)="ptr"(b,o,s,t)$, then $mu_t(a)="ptr"(b,o,s,t')$ with
    $rho_t(t)=t'$ and the referent range $[b,b+s)$ mapped;
  - if $E(ell)=(a,t)$ for $ell:tau$, then the register $L_i(ell)$ holds
    `PTy` and exactly one pointer with base $a$, offset zero, size
    $|tau|$, and tag $rho_t(t)$;
  - the target stack at every address has the same length and item
    constructors as the source stack, with every source tag renamed by
    $rho_t$;
  - the target PC is the next label after compiling exactly $P[0..i)$.
] <cor:observe>

#proof[
  Clauses (I3) and (I5) give the first two items, (I2) the third, (I4) the
  fourth, and (I1) the fifth.
]

Several asymmetries are intentional. The target may contain extra registers,
because value temporaries remain after use. Source `undef` refines any target
cell, so the memory relation has no reverse-domain guarantee. Tag counters need not be
equal, and numeric tag equality is not observable. Finally, the invariant is
required only at source-statement boundaries; intermediate target states may
contain live route tags.

These choices are the minimum abstraction needed by the actual generated
code. Strengthening to literal register equality would reject harmless
temporaries, while weakening permission stacks to ignore arbitrary target
items would no longer justify later accesses.

= Mechanization and scope <sec:mech>

#takeaway([PRECISE CLAIM], [
  The mechanized theorems are forward simulations for successful finite runs
  of core programs: `halt`, the protector-frame statements, and plain or
  guarded assignments from every expression of the language. The
  executable compiler also lowers heap `alloc` and `dealloc`; those two
  statements are outside @thm:step until their simulation cases are added
  (@sec:surface-open).
])

Every numbered definition and result of @sec:correctness is a Lean 4
declaration in `src/obseq3/proof/`:

#proptable(
  [The results of @sec:correctness and their Lean declarations.],
  ([This paper], [Lean declaration], [File]),
  (30%, 46%, 24%),
  ([@def:valsim], [`MemValSim`], [`common.lean`]),
  ([@def:memsim], [`SourceMemSim`], [`common.lean`]),
  ([@def:permsim], [`PermSim`], [`common.lean`]),
  ([@def:inv], [`CompilerInv`], [`common.lean`]),
  ([core fragment], [`CoreRhs`, `CoreStmt`, `CoreProg`], [`common.lean`]),
  ([@lem:cancel], [`sb_ref_use_die_cancels`], [`keystone.lean`]),
  ([@thm:step], [`CompilerInv_step`], [`compiler.lean`]),
  ([@thm:run], [`compile_correct`], [`compiler.lean`]),
  ([@lem:init], [`CompilerInv_initial`], [`compiler.lean`]),
  ([@cor:closed], [`compile_correct_from_initial`], [`compiler.lean`]),
) <tab:lean>

None of these contains an admitted goal. A checked audit prints the axioms
that @thm:run and @cor:closed depend on and fails if that set differs in
either direction from a pinned whitelist. The whitelist contains exactly the
three standard Lean axioms, propositional extensionality, choice, and
quotient soundness, and no `sorryAx`. The last admitted case, the
reference-assignment leaves, was closed on 2026-08-31.

The executable compiler is additionally validated by testing: a compiler
witness corpus, a ULLBC conformance corpus checked against Miri verdicts,
and a differential run that compiles each conformance program and requires
the same verdict from both machines. The running program of this paper is
part of the witness corpus, both as a golden listing
(@fig:compile-example) and as a differential test; the states of
@tab:mir-example and @tab:osea-example are printed by the mechanized
interpreters. Tests cover `alloc` and `dealloc` too, but only a discharged
simulation case moves a construct inside @thm:step.

#source([Invariant and simulation vocabulary: `src/obseq3/proof/common.lean`. Statement and whole-program forward simulations: `src/obseq3/proof/compiler.lean`. Witness corpus: `src/obseq3/compile_tests.lean`; state dump of the running program: `notes/2026-09-18-paper-running-example.lean`.])

#counter(heading).update(0)
#set heading(numbering: "A.1")

= The full executable surface <sec:surface>

The main text presents constants, copies, references, assignment, and
`halt`. This appendix extends each of its figures and tables, in the same
format, to the language the compiler and the theorem actually cover.

== Syntax

#grammarfig(
  [The remaining syntax of MIRLite (left) and OSEA-IR (right), extending @fig:mir-grammar and @fig:oseair-grammar. $d$ in `offset` is an integer; a `borrow` of length $bot$ retags the rest of the allocation.],
  panel([MIRLite], bnf(
    prod($"Expr" in.rev e$, $dots$, $"uninit"$, $"exposeAddr"(p)$, $"fromExposed"(p)$, $"ptrCast"(p)$, $"ptrOffset"(p,d)$, $"refSlice"(k,c,p)$),
    prod($"Stmt" in.rev s$, $dots$, $"assignIf"(p = w, thick d := e)$, $"alloc"(d, "len")$, $"dealloc"(p)$, $"pushProtectors"$, $"popProtectors"$),
    prod($"len"$, $"const"(n) | "from"(p)$),
  )),
  panel([OSEA-IR], bnf(
    prod($"Rhs" in.rev h$, $dots$, $"allocN"_theta (n)$, $"allocDyn"_theta (r)$, $"expose"(r)$, $"fromExposed"(r)$, $"offset"(r,d)$, $"borrow"(k,c,m,bot,r,delta)$),
    prod($"Instr" in.rev I$, $dots$, $"memcpy"_theta (r_d, r_s)$, $"dealloc"(r)$, $"skipIf"(r, w, n)$, $"pushProt" | "popProt"$),
  )),
) <fig:surface-grammar>

Layout rules are as in @sec:mirlite: $"uninit"$ has any layout;
$"exposeAddr"(p)$ has layout `Nat` for a pointer place $p$ and
$"fromExposed"(p)$ a pointer layout for a `Nat` place; $"ptrCast"$,
$"ptrOffset"$, and $"refSlice"$ map pointer places to pointer layouts; the
discriminant of a guarded assignment is a `Nat` place. The source semantics
of these forms follows the pattern of @tab:mir: each expression resolves
its place, performs the permission events listed for its target
counterpart in @tab:surface-osea in the same order, and produces cells. A
guarded assignment first prepares the root of its destination, _on both
paths_, then reads its discriminant exactly as $"copy"$ does, a real read
access, and performs the assignment when the value read equals $w$.

== The permission model

#proptable(
  [The remaining operations of the permission interface of @sec:perm.],
  ([Operation], [Meaning]),
  (40%, 60%),
  ([$"dealloc"(Pi,a,n,t)=Pi'$], [Deallocate the $n$ cells from $a$ through $t$ and forget their permissions. The item carrying $t$ must grant writes at every cell, and no item of those stacks may be protected.]),
  ([$"expose"(Pi,t)=Pi'$], [Record $t$ as exposed, so that a later wildcard access may resolve to it.]),
  ([$"pushProt"(Pi)=Pi'$, $"popProt"(Pi)=Pi'$], [Open a protector frame; close the innermost frame, ending the protection of every tag registered in it.]),
) <tab:surface-perm>

Tags are drawn from a countable set with a distinguished _wildcard_ tag 0,
which stands for an unknown provenance recovered from an exposed integer.
Every fresh tag is minted from `NextTag` upward, so it is distinct from
all earlier ones and a tag minted later is numerically larger. The rules of
@tab:sb extend as follows. _Protectors:_ if the flag $c$ of a `ref` is set,
the fresh tag is registered in the innermost protector frame; #sb-read,
#sb-use, and #sb-die fail when an item they would disable or remove is
protected. _Masks:_ on cells that the mask $m$ marks as interior-mutable, a
shared or raw-constant retag performs no access and inserts
$"RawPtr"("true",u)$ directly above the item carrying $t$, as #sb-refr
does. _Two-phase:_ a two-phase retag performs a read and inserts
$"RawPtr"("true",u)$ likewise, modelling a reservation that stays writable
until activation. _Raw-pointer groups:_ #sb-use also accepts
$iota="RawPtr"("true",t)$, and then keeps the contiguous run of mutable
raw-pointer items directly above $iota$, removing only what lies above the
whole group. _Wildcard:_ an access through tag 0 resolves to the topmost
exposed item that grants it. This rule is a determinization: for programs
that use integer-to-pointer casts, the theorem is a statement about it
rather than about Miri's angelic choice.

== OSEA-IR

#ruletable(
  [The remaining OSEA-IR rules, extending @tab:osea. In the rules that read through $r$, $R(r)=(theta_r,["ptr"(b,o,s,t)])$, $a=b+o$, and $a<b+s$. $"wild"$ is the wildcard tag and $"resolve"(mu_t,n)$ looks $n$ up in the allocation table.],
  placement: none,
  ir(rn[rval-allocn],
    [$N = n dot "typeSize"(theta)$, #h(3pt) $"alloc"(mu_t,N)=(b,mu'_t)$, \ $"own"(Pi_t,b,N)=(Pi'_t,u)$],
    [$T tack "allocN"_theta (n) #dH$ \ $quad ("PTy", ["ptr"(b,0,N,u)], T[mu_t |-> mu'_t, Pi_t |-> Pi'_t])$]),
  ir(rn[rval-allocdyn],
    [$"read"(Pi_t,a,1,t)=Pi_1$, #h(3pt) $mu_t (a)="dat"(n)$, \ $N = n dot "typeSize"(theta)$, #h(3pt) $"alloc"(mu_t,N)=(b',mu'_t)$, \ $"own"(Pi_1,b',N)=(Pi_2,u)$],
    [$T tack "allocDyn"_theta (r) #dH$ \ $quad ("PTy", ["ptr"(b',0,N,u)], T[mu_t |-> mu'_t, Pi_t |-> Pi_2])$]),
  ir(rn[rval-expose],
    [$"read"(Pi_t,a,1,t)=Pi_1$, #h(3pt) $mu_t (a)="ptr"(b',o',s',t')$, \ $"expose"(Pi_1,t')=Pi_2$],
    [$T tack "expose"(r) #dH$ \ $quad ("NatTy", ["dat"(b'+o')], T[Pi_t |-> Pi_2])$]),
  ir(rn[rval-fromexposed],
    [$"read"(Pi_t,a,1,t)=Pi_1$, #h(3pt) $mu_t (a)="dat"(n)$, \ $"resolve"(mu_t,n)=(b',o',s')$],
    [$T tack "fromExposed"(r) #dH$ \ $quad ("PTy", ["ptr"(b',o',s',"wild")], T[Pi_t |-> Pi_1])$]),
  ir(rn[rval-offset],
    [$"read"(Pi_t,a,1,t)=Pi_1$, #h(3pt) $mu_t (a)="ptr"(b',o',s',t')$, \ $o'+d >= 0$],
    [$T tack "offset"(r,d) #dH$ \ $quad ("PTy", ["ptr"(b',o'+d,s',t')], T[Pi_t |-> Pi_1])$]),
  ir(rn[rval-borrow-rest],
    [$R(r)=(theta_r,["ptr"(b,o,s,t)])$, #h(3pt) $a'=b+o+delta$, \ $"ref"(Pi_t,a',s-(o+delta),t,k,c,m)=(Pi'_t,u)$],
    [$T tack "borrow"(k,c,m,bot,r,delta) #dH$ \ $quad ("PTy", ["ptr"(b,o+delta,s,u)], T[Pi_t |-> Pi'_t])$]),
  ir(rn[exec-memcpy],
    [$Q(j)="memcpy"_theta (r_d,r_s)$, #h(3pt) $n="typeSize"(theta)$, \ $R(r_d)=(theta_d,["ptr"(b_d,o_d,s_d,t_d)])$, #h(3pt) $a_d=b_d+o_d$, \ $R(r_s)=(theta_s,["ptr"(b_s,o_s,s_s,t_s)])$, #h(3pt) $a_s=b_s+o_s$, \ both ranges fit and do not overlap, \ $"read"(Pi_t,a_s,n,t_s)=Pi_1$, #h(3pt) $"useMut"(Pi_1,a_d,n,t_d)=Pi_2$],
    [$(j,R,mu_t,Pi_t) ssea$ \ $quad (j+1, R, mu_t [a_d |-> mu_t [a_s..a_s+n)], Pi_2)$]),
  ir(rn[exec-dealloc],
    [$Q(j)="dealloc"(r)$, #h(3pt) $R(r)=(theta_r,["ptr"(b,0,s,t)])$, \ $"dealloc"(Pi_t,b,s,t)=Pi'_t$],
    [$(j,R,mu_t,Pi_t) ssea$ \ $quad (j+1, R, mu_t without [b,b+s), Pi'_t)$]),
  ir(rn[exec-skipif],
    [$Q(j)="skipIf"(r,w,n)$, #h(3pt) $R(r)=(theta_r,["dat"(w')])$, \ $j'=j+1$ if $w'=w$, else $j'=j+1+n$],
    [$(j,R,mu_t,Pi_t) ssea (j',R,mu_t,Pi_t)$]),
  ir(rn[exec-pushprot],
    [$Q(j)="pushProt"$],
    [$(j,R,mu_t,Pi_t) ssea (j+1,R,mu_t,"pushProt"(Pi_t))$]),
  ir(rn[exec-popprot],
    [$Q(j)="popProt"$, #h(3pt) $"popProt"(Pi_t)=Pi'_t$],
    [$(j,R,mu_t,Pi_t) ssea (j+1,R,mu_t,Pi'_t)$]),
) <tab:surface-osea>

The pointer right-hand sides are operational rather than mere casts, and
share a three-stage pattern: validate the register shape, perform the
permission events in source order, construct a result. They read _through
the outer pointer in the register_ before inspecting the value in memory.
For example, `offset` does not change the offset of that outer pointer: it
loads a pointer-valued cell, changes the loaded value, and returns the
result in a register. This is why the compiler can use it to implement
MIRLite pointer arithmetic without suppressing the source's read event.
`allocDyn` reads its length before it allocates, which matches the
source's permission-visible length read. The bump allocator never reuses a
deallocated range. `skipIf` touches neither memory nor permissions: the
discriminant it tests was loaded into a register by an ordinary `load`.
The compiler emits no `memcpy`; the instruction remains part of the
machine.

OSEA-IR errors fall into four semantic classes rather than one generic
"stuck" state:

#proptable(
  [Error classes of OSEA-IR.],
  ([Class], [Typical cause], [Where detected]),
  (20%, 40%, 40%),
  ([Register shape], [Missing register, non-pointer singleton, or wrong source runtime type.], [Before any memory or permission change.]),
  ([Value shape], [A cast or dynamic allocation observes the wrong memory-value constructor.], [After any required permission read, so that event order remains explicit.]),
  ([Spatial], [A complete access range exceeds its allocation, a pointer offset becomes negative, or `memcpy` overlaps.], [Before the corresponding read/write permission event.]),
  ([Permission], [`read`, `ref`, `useMut`, `die`, `dealloc`, or a protector pop rejects the operation.], [At the permission interface; its error is propagated.]),
) <tab:surface-errors>

The forward simulation only starts from a successful source step. It
therefore proves that the compiled fragment avoids all of these errors for
the covered cases; it does not claim that source and target failure
messages coincide.

== Compiler

Every expression has the pre-code/store split of #c-copy. In
@tab:surface-expr, "lower $p$" is $C tack_"shared" p #dCP (r_s,D_s,C_1)$,
$r_v$ is a fresh value register, and the pre-code is emitted before the
destination is lowered.

#proptable(
  [Lowering of the remaining expressions, extending #c-const, #c-copy, and #c-ref of @tab:compile. The selected layout is $tau$; in `ptrOffset`, $p:"Ptr" sigma$.],
  ([Expression], [Pre-destination code], [Deferred store $F(r_d)$]),
  (19%, 50%, 31%),
  ([`uninit`], [None.], [$"storec"_(floor(tau)) (["undef"]^(|tau|), r_d)$]),
  ([`exposeAddr(p)`], [Lower $p$; $r_v := "expose"(r_s)$; $"cleanup"(D_s)$.], [$"store"_"NatTy" (r_v, r_d)$]),
  ([`fromExposed(p)`], [Lower $p$; $r_v := "fromExposed"(r_s)$; $"cleanup"(D_s)$.], [$"store"_"PTy" (r_v, r_d)$]),
  ([`ptrCast(p)`], [Lower $p$; $r_v := "load"_"PTy" (r_s)$; $"cleanup"(D_s)$.], [$"store"_"PTy" (r_v, r_d)$]),
  ([`ptrOffset(p,d)`], [Lower $p$; $r_v := "offset"(r_s, d dot |sigma|)$; $"cleanup"(D_s)$.], [$"store"_"PTy" (r_v, r_d)$]),
  ([`refSlice(k,c,p)`], [Lower $p$; $r_v := "load"_"PTy" (r_s)$; $"cleanup"(D_s)$; then $r_v := "borrow"(k,c,[],bot,r_v,0)$.], [$"store"_"PTy" (r_v, r_d)$]),
) <tab:surface-expr>

$["undef"]^(|tau|)$ is a list of exactly $|tau|$ undefined cells. Pointer
offsets are expressed by the source in pointee units, so the compiler
scales $d$ by the pointee width before OSEA-IR sees it. A pointer cast is
tag-preserving: a `borrow` would mint a new tag, whereas a load and a store
copy the pointer value unchanged while performing the source's read and
write. The placement of cleanup is semantic. In `refSlice` the mint comes
_after_ the cleanup: a mutable retag through the loaded tag would pop a
route tag still on the stack, and a shared one would bury it, so the
route's `die` would no longer find its item on top. Every bracket the
compiler opens therefore closes with its route tag on top.

#proptable(
  [Lowering of the remaining statements, extending #c-assign and #c-halt of @tab:compile.],
  ([Statement], [Emitted sequence]),
  (24%, 76%),
  ([`alloc(d, const(n))`], [$"root"(d)$; lower $d$ mutable to $(r_d,D_d)$; fresh $r_h := "allocN"_(floor(tau)) (n)$; $"store"_"PTy" (r_h,r_d)$; $"cleanup"(D_d)$.]),
  ([`alloc(d, from(p))`], [As above, with the heap pointer obtained by: lower $p$ shared to $(r_p,D_p)$; $r_h := "allocDyn"_(floor(tau)) (r_p)$; $"cleanup"(D_p)$.]),
  ([`dealloc(p)`], [Lower $p$ shared to $(r_p,D_p)$; fresh $r_v := "load"_"PTy" (r_p)$; $"cleanup"(D_p)$; $"dealloc"(r_v)$.]),
  ([`assignIf(p = w, d := e)`], [$"root"(d)$, before the guard; lower $p$ shared to $(r_p,D_p)$; fresh $r_g := "load"_"NatTy" (r_p)$; $"cleanup"(D_p)$; reserve the label $j_g$; compile $d := e$ by #c-assign; patch $K(j_g) = "skipIf"(r_g, w, n)$ with $n$ the number of labels the assignment emitted.]),
  ([`pushProtectors`], [$"pushProt"$]),
  ([`popProtectors`], [$"popProt"$]),
) <tab:surface-stmt>

For `alloc`, destination resolution precedes the evaluation of a dynamic
length, matching the source allocation statement rather than the ordinary
assignment rule. For `assignIf`, the root of the destination is allocated
before the guard because a root allocated inside the guarded fragment
would be recorded in $L$ at compile time but would exist at run time only
when the guard is taken. The guard _reserves_ its label and is patched
once the body has been compiled, so the body is compiled exactly once and
its measured length is the skip count; no statement is compiled twice.

== What remains outside the theorem <sec:surface-open>

Two statements are executable and tested but not yet inside @thm:step.
Adding them is not "supporting the constructor"; it is preserving the ten
clauses of @def:inv through each emitted sequence. For `alloc`, the proof
must synchronize a runtime or constant length and extend both renamings
over the fresh heap block. For `dealloc`, it must relate the offset-zero
checks, the permission retirement, and the removal of the same memory
range. Neither follows merely from successful differential tests.

The rest of this appendix was on that list until it was discharged, and
how it left is instructive. `exposeAddr` and `fromExposed` compile exactly
as `copy` does, so abstracting the copy leaves over the emitted right-hand
side made every leaf, write seam, and fragment lemma serve all three; what
remained was one simulation lemma per cast. The exposure is a cons onto
the exposed list, which @def:permsim already relates positionally. The
int-to-ptr direction needed two invariant strengthenings: the two
allocation tables travel in lockstep, so both machines resolve an integer
to the same block, and the address renaming is total, which supplies the
base of the degenerate pointer an unallocated address yields. It also
needed wildcard-tagged pointers to be admissible values, and hence
accesses through the wildcard to transport: both machines pick the topmost
exposed granting item out of related stacks, so they pick corresponding
items. Pointer casts, pointer offsets, `uninit`, and slice retags then
joined through the same read-then-store family, the slice retag once its
mint had been moved out of the route bracket (@tab:surface-expr). Guarded
assignment needed the control argument about the measured skip length and
the both-paths rooting of its destination; protector frames needed push
and successful pop to preserve the nested tag-list relation of
@def:permsim, including protected tags introduced by source-visible
references.
