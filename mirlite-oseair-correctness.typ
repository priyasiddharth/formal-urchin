// PLDI 2026 review layout. Build from the repository root with:
// typst compile --font-path assets/fonts/acm mirlite-oseair-correctness.typ
#import "@preview/faithful-acmart:0.1.0": acmart
// Numbered environments. All kinds share one counter, reset per section,
// so a section reads Definition 5.1, Lemma 5.2, Theorem 5.3, ...
#let thmcnt = counter(figure.where(kind: "thmenv"))
#show heading.where(level: 1): it => { thmcnt.update(0); it }
#let thmenv(head, bodyfmt: emph) = (..args, body) => figure(
  kind: "thmenv",
  supplement: head,
  outlined: false,
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
#let smallcaps(body) = text(font: "Libertinus Sans", size: 8pt, weight: "semibold", body)
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
  [#smallcaps(title) #h(4pt) #body],
)
#let infer(name, premises, conclusion) = block(
  width: 100%,
  inset: 4pt,
  radius: 2pt,
  fill: rgb("fafbfc"),
  stroke: 0.45pt + rule,
  [
    #align(center)[#text(size: 8.4pt)[#premises]]
    #v(1pt)
    #line(length: 100%, stroke: 0.65pt + rgb("687782"))
    #v(1pt)
    #align(center)[#text(size: 8.7pt)[#conclusion]]
    #align(right)[#text(font: "Libertinus Sans", size: 6.9pt, weight: "semibold", fill: accent)[#name]]
  ],
)

#show: acmart.with(
  format: "acmsmall",
  font-size: 10pt,
  title: "A Borrow-Aware Compiler from MIRLite to OSEA-IR",
  authors: (),
  abstract: [
    MIRLite gives typed Rust-like places an operational semantics. Its compiler
    lowers each statement to OSEA-IR with explicit reads, retags, writes, and
    borrow retirement. We present both languages through their syntax and
    transition relations, derive the compiler on a running nested-field
    assignment, and state the forward simulation that relates source and
    target memory, locals, and per-cell permission stacks.
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

= Overview and running example

The compiler in this paper connects two views of the same memory operation.
MIRLite says _which typed place_ a Rust-like statement accesses. OSEA-IR says
_which reads, retags, writes, and borrow retirements_ implement that access.
The proof relates their executions without demanding that their permission
stacks be literally equal: the target is allowed to introduce short-lived
tags that have no source counterpart. @sec:compiler names them route tags.

We use cells as the unit of layout. Write $|tau|$ for the number of cells in a
layout $tau$. Naturals and pointers occupy one cell; a tuple occupies the sum
of its fields. A pointer value

#align(center)[
  $"ptr"(b,o,n,t)$
]

denotes address $b+o$ in an allocation with base $b$, extent $n$, and
provenance tag $t$. A memory $mu$ maps cell addresses to words, pointers, or
undefined values. A permission state $Pi$ records the per-cell borrow stacks.

== One example through the whole paper

Let

#align(center)[
  $x : ("Nat",("Nat","Nat")) quad s_x = x.1.0 := 42.$
]

Assume the local $x$ owns three cells beginning at address 100:

#align(center)[
  $E(x)=(100,t_x) quad mu[100..103)=["word"(5),"word"(7),"word"(9)].$
]

The outer field `.1` begins one cell into $x$ and has width two; its inner
field `.0` begins at offset zero and has width one. The composed path `.1.0`
therefore has offset 1 and selects exactly address 101. Source execution uses
$t_x$ directly to replace 7 by 42. The compiler instead emits

```text
r_f := borrow_mut r_x offset 1 length 1
store_nat 42 through r_f
die r_f length 1
```

where $r_x$ holds a pointer to $x$. The first instruction creates a fresh tag
$u$, the second writes through $u$, and the third retires $u$. The running
proof must show both executions finish with the same observable cells even
though only the target took the intermediate retag steps.

#takeaway([READING GUIDE], [
  Each of the next four sections gives the relevant syntax, defines the
  operational or translation judgment, and then instantiates it on
  $x.1.0 := 42$. The example is not decorative: it fixes every symbol needed
  to state the compiler and its correctness relation.
])

= MIRLite <sec:mirlite>

MIRLite is a typed, sequential language for the memory-level part of Rust
that matters to borrow reasoning. Its semantics is parameterized by a
_permission model_: an abstract state $Pi$ together with operations that
validate and record each memory access (@sec:perm). The core semantics
uses four of them, `own`, `read`, `ref`, and `useMut`; the full executable
language additionally uses borrow retirement, deallocation, exposed
provenance, and protector-frame operations. The correctness result
instantiates the model with per-cell Stacked Borrows.

== Notation

The following metavariables are used throughout the paper. Primed and
subscripted variants ($Pi'$, $Pi_1$, $t_x$) denote further values of the same
sort.

#table(
  columns: (21%, 79%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Symbol],
  text(fill: white, weight: "bold")[Ranges over / meaning],
  [$sigma, tau$], [Layout types. By convention $sigma$ is the layout of a region being traversed and $tau$ the layout of the region selected or produced. $|tau|$ is the width of $tau$ in cells.],
  [$Gamma$], [A typing context: an ordered list of layouts, one per local.],
  [$ell$], [A typed local: an index into $Gamma$ together with its layout $ell:tau$.],
  [$q$], [A typed projection path $q:sigma arrow.r tau$ with cell offset $"off"(q)$.],
  [$p, d$], [Places; $d$ is used when the place is an assignment destination.],
  [$e, s$], [A MIRLite expression and statement.],
  [$k, c, m$], [Retag kind, protector flag, and interior-mutability mask of a reference formation. The compiler's place-lowering judgment is indexed by the same $k$.],
  [$n$], [A natural count: a length in cells, a number of elements, or a tuple arity. $n_s$ and $n_t$ are source and target step counts.],
  [$w$], [A machine word.],
  [$v$], [A cell value: source form $"undef" | "word"(w) | "ptr"(b,o,N,t)$ (@sec:state) or target form $"undef" | "dat"(w) | "ptr"(b,o,s,t)$ (@sec:target-values). Also a list of cells, with $"len"(v)$ its length.],
  [$a, b, N, o$], [Cell address, allocation base, allocation extent, and offset within an allocation.],
  [$t, u$], [Provenance tags; $u$ is used for a freshly minted tag.],
  [$S=(i,E,mu,Pi)$], [A source state: program counter $i$, environment $E$, memory $mu$, and permission state $Pi$.],
  [$Pi$], [A permission state (@sec:perm).],
  [`own`, `read`, `ref`, `useMut`, `die`], [The permission operations on $Pi$ (@sec:perm).],
  [$theta$], [An OSEA-IR runtime type; $floor(tau)$ erases a layout to one, and $"typeSize"(theta)$ is its width in cells.],
  [$T=(j,R,mu_t,Pi_t)$], [A target state: program counter $j$, register file $R$, memory, and permission state.],
  [$r$], [A target register.],
  [$Q$], [A target program: a partial map from labels to instructions.],
  [$C=(n_r,n_l,K,L)$], [A compiler state: next register, next label, emitted code map, and local map.],
  [$rho_a, rho_t$], [Partial address and tag renamings from source to target.],
)

== Syntax <sec:syntax>

A _layout type_ describes the shape of a memory region. Metavariables
$sigma$ and $tau$ range over layouts:

#align(center)[
  $tau,sigma ::= "Nat" | "Ptr" tau | (tau_0,...,tau_(n-1)).$
]

Both letters denote layouts; the choice records a role. When a judgment
involves two layouts, $sigma$ is the layout of the region being traversed
and $tau$ is the layout of the region selected from it or produced by it.
So a path $q:sigma arrow.r tau$ walks a $sigma$-shaped region and selects a
$tau$-shaped subregion, and a place $Gamma tack p:tau$ selects a
$tau$-shaped region. When only one layout is involved it is written $tau$.

Write $|tau|$ for the number of cells in a layout. Naturals and pointers each
occupy one cell, while a tuple occupies the sum of its fields:

#align(center)[
  $|"Nat"|=1 quad |"Ptr" tau|=1 quad
    |(tau_0,...,tau_(n-1))|=sum_(j=0)^(n-1)|tau_j|.$
]

The pointee parameter of $"Ptr" tau$ is therefore statically significant even
though all pointer values occupy one cell. A context is an ordered list
$Gamma=[tau_0,...,tau_(n-1)]$. A typed local $ell:tau$ consists of an index
$j<n$ together with the fact that $Gamma_j=tau$.

Projection paths are also typed. The judgment $q:sigma arrow.r tau$ means
that following $q$ through a $sigma$-shaped region selects a $tau$-shaped
region. A path may be empty, or select a tuple field and continue recursively.
It determines a cell offset $"off"(q)$ and satisfies

#align(center)[
  $"off"(q)+|tau| <= |sigma|.$
]

Places are indexed by the layout they select. Write $Gamma tack p:tau$ for a
well-typed place:

#grid(
  columns: (1fr, 1fr, 1fr),
  column-gutter: 5pt,
  infer([local], [
    $ell:tau in Gamma$
  ], [
    $Gamma tack ell:tau$
  ]),
  infer([projection], [
    $Gamma tack p:sigma quad q:sigma arrow.r tau$
  ], [
    $Gamma tack p.q:tau$
  ]),
  infer([dereference], [
    $Gamma tack p:"Ptr" tau$
  ], [
    $Gamma tack star p:tau$
  ]),
)

The retag kind $k$ is not limited to Rust references:

#align(center)[
  $k ::= "shared" | "mutable" | "raw-const" | "raw-mut" | "two-phase".$
]

`raw-const` and `raw-mut` create read-only and mutable raw-pointer items;
`two-phase` creates a reserved mutable borrow. Reference formation also takes
a protector flag $c$ and an interior-mutability mask $m$. A protected fresh
tag is registered in the current protector frame; true entries of $m$ mark
cells lying inside `UnsafeCell`.

The expressions and statements covered by the correctness theorem are typed
by the following signatures, where $w$ ranges over machine words:

#align(center)[
#box(width: 96%, inset: 6pt, stroke: 0.5pt + rule, radius: 2pt)[
#table(
  columns: (30%, 70%),
  stroke: none,
  inset: 2pt,
  [$"const"(w)$], [$: "Expr" Gamma "Nat"$],
  [$"copy"(p)$], [$: "Expr" Gamma tau quad "if" quad Gamma tack p:tau$],
  [$"ref"(k,c,m,p)$], [$: "Expr" Gamma ("Ptr" tau) quad "if" quad Gamma tack p:tau$],
  [$d:=e$], [$: "Stmt" Gamma quad "if" quad Gamma tack d:tau quad "and" quad Gamma tack e:tau$],
  [$"halt"$], [$: "Stmt" Gamma$],
)
]]

Thus the destination and RHS of an assignment necessarily have the same
layout. The complete executable syntax also contains uninitialized values,
pointer casts and offsets, slice retags, exposed-provenance conversions,
conditional assignment, allocation, deallocation, and protector-frame
operations. Those forms use the same state model but lie outside the current
forward-simulation theorem.

== The permission interface <sec:perm>

A permission state $Pi$ records, for every allocated cell, which tags may
currently access it. The semantics of both languages manipulates $Pi$ only
through the following partial operations. Each either returns a new state,
or fails; a failure is undefined behavior and aborts the execution.

#table(
  columns: (42%, 58%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Operation],
  text(fill: white, weight: "bold")[Meaning],
  [$"own"(Pi,a,n)=(Pi',t)$], [Initialize the $n$ cells from $a$ as a fresh allocation whose owning tag is the fresh tag $t$.],
  [$"read"(Pi,a,n,t)=Pi'$], [Validate a read of the $n$ cells from $a$ through $t$.],
  [$"useMut"(Pi,a,n,t)=Pi'$], [Validate a write of the $n$ cells from $a$ through $t$.],
  [$"ref"(Pi,a,n,t,k,c,m)=(Pi',u)$], [Retag the $n$ cells from $a$: derive a fresh tag $u$ from parent $t$ with retag kind $k$, protector flag $c$, and interior-mutability mask $m$.],
  [$"die"(Pi,a,n,t)=Pi'$], [Retire tag $t$ on the $n$ cells from $a$.],
  [$"dealloc"(Pi,a,n,t)=Pi'$], [Deallocate the $n$ cells from $a$ through $t$ and forget their permissions.],
  [$"expose"(Pi,t)=Pi'$], [Record $t$ as exposed, so that a later wildcard access may resolve to it.],
  [$"pushProt"(Pi)=Pi'$, $"popProt"(Pi)=Pi'$], [Open a protector frame; close the innermost frame, ending the protection of every tag registered in it.],
)

Tags are drawn from a countable set with a distinguished _wildcard_ tag,
which stands for an unknown provenance recovered from an exposed integer.
Every fresh tag returned by `own` or `ref` is distinct from all earlier ones.

The correctness theorem instantiates this interface with per-cell Stacked
Borrows. A state is then

#align(center)[
  $Pi=("stacks","NextTag","frames","exposed"),$
]

where `stacks` is a partial map from addresses to _borrow stacks_, `NextTag`
is the next fresh tag, `frames` is a list of protector frames, each a list
of protected tags, and `exposed` is the list of exposed tags. A borrow stack
is a list of _items_,

#align(center)[
  $iota ::= "Own"(t) | "MutRef"(t) | "Ref"(t) | "RawPtr"(m',t) | "Disabled"(t),$
]

with the topmost item first and $m'$ a mutability flag. Each operation acts
cell by cell over its range. `own` requires an empty stack and pushes
$"Own"(t)$. `read` locates the item carrying $t$, disables every
mutable-reference item above it, and fails if any of those is protected.
`useMut` requires the item carrying $t$ to grant writes, pops everything
above it, and fails if a popped item is protected. `ref` depends on $k$.
A mutable retag performs a write through $t$ and pushes $"MutRef"(u)$.
A shared or raw-constant retag performs a read through $t$ and pushes
$"Ref"(u)$ or $"RawPtr"("false",u)$; on cells the mask marks as
interior-mutable it instead inserts $"RawPtr"("true",u)$ directly above the
item carrying $t$, with no access. A raw-mutable retag performs no access
and inserts $"RawPtr"("true",u)$ above the item carrying $t$, so sibling
raw pointers share one group instead of invalidating each other. A
two-phase retag performs a read and inserts $"RawPtr"("true",u)$ likewise,
modelling a reservation that stays writable until activation. If $c$ is
set, $u$ is registered in the innermost protector frame. `die` pops the
item carrying $t$ if it is on top and is neither the allocation's `Own` item
nor protected. `dealloc` requires the item carrying $t$ to grant writes at
every cell, fails if any item in one of those stacks is protected, and
removes the stacks. Fresh tags are minted from `NextTag` upward, so a tag
minted later is numerically larger.

In the mechanization the operations are `sb_own`, `sb_read`, `sb_write`,
`sb_ref`, `sb_die`, and `sb_dealloc` in `src/obseq3/sb.lean`; the paper
writes `useMut` for `sb_write` to keep the source-level reading.

== State and place semantics <sec:state>

A source _cell value_ is undefined, a machine word, or a pointer:

#align(center)[
  $v ::= "undef" | "word"(w) | "ptr"(b,o,N,t).$
]

A pointer $"ptr"(b,o,N,t)$ denotes address $b+o$ in the allocation with
base $b$ and extent $N$, and carries provenance tag $t$. A source _memory_
$mu$ consists of a partial map from addresses to cell values, the next
bump-allocation address, and the list of known allocation ranges. Write
$mu(a)$ for the cell at address $a$, which is `undef` when the map has no
entry there; $mu[a..a+n)$ for the list of $n$ cells starting at $a$; and
$mu[a mapsto v]$ for the memory with the cell at $a$ replaced by $v$.

A source state is $S=(i,E,mu,Pi)$. The program counter $i$ indexes the source
statement list. The partial environment $E$ maps a typed local either to no
binding or to an allocation base and tag. Finally, $Pi$ is the abstract
permission state.

A resolved place $"res"(a,t,b,N)$ records current address $a$, access tag $t$,
allocation base $b$, and allocation extent $N$. For a well-typed place
$Gamma tack p:tau$, write

#align(center)[
  $S tack_a p ⇓ ("res"(a,t,b,N),Pi')$
]

when resolving $p$ for an access succeeds. Resolution does not write memory,
but dereferencing a pointer is itself a read and can therefore change the
permission state. All rules in this section describe successful branches.
An unbound local, a malformed or out-of-bounds pointer, or rejection by the
permission model produces an error and therefore no successor judgment.

#grid(
  columns: (1fr, 1fr),
  column-gutter: 7pt,
  infer([local], [
    $E(ell)=(a,t)$
  ], [
    $S tack_a ell ⇓ ("res"(a,t,a,|tau|),Pi)$
  ]),
  infer([projection], [
    $S tack_a p ⇓ ("res"(a,t,b,N),Pi')$
  ], [
    $S tack_a p.q ⇓ ("res"(a+"off"(q),t,b,N),Pi')$
  ]),
)

Projection is only typed address arithmetic: it preserves provenance,
allocation bounds, and permissions. Dereference changes provenance because
the pointer _value_, not the place holding it, identifies the referent:

#infer([dereference], [
  $S tack_a p ⇓ ("res"(a,t,b,N),Pi_1)$
  #linebreak()
  $b <= a < b+N quad "read"(Pi_1,a,1,t)=Pi_2$
  #linebreak()
  $mu(a)="ptr"(b',o',N',t')$
], [
  $S tack_a star p ⇓ ("res"(b'+o',t',b',N'),Pi_2)$
])

Nested dereferences thread these permission changes from the inside out. A
separate _pure lookup_ follows the same address calculation but merely
inspects a pointer cell: it performs neither a bounds check nor `read`. It is
used for raw observations such as a conditional discriminant and for deciding
whether an assignment root must first be allocated. Ordinary reads, retags,
and writes use access resolution above.

== Preparation, expressions, and statements <sec:prep>

Before an assignment, $"prepare"(S,d)$ checks the destination using pure
lookup. If lookup succeeds, preparation returns $S$ unchanged. If it fails and
the root of $d$ is an unbound local $ell:tau$, the bump allocator reserves
$|tau|$ cells at a fresh base $b$, `own` returns a fresh tag $t$, and the
environment is extended with $E(ell)=(b,t)$. An unresolved destination rooted
through a dereference is an error: assignment never allocates an implicit
pointee.

Write $S tack e ⇓_tau (v,S')$ when expression $e$ produces a list of exactly
$|tau|$ cells. Constants have an explicit one-cell transition:

#infer([constant], [
  $quad$
], [
  $S tack "const"(w) ⇓_"Nat" (["word"(w)],S)$
])

Copy and reference formation first resolve their source place and then act on
the entire selected range. Reading an absent but permitted memory cell yields
`undef`; bounds or permission failure still produces an error.

#grid(
  columns: (1fr, 1fr),
  column-gutter: 7pt,
  infer([copy], [
    $S tack_a p ⇓ ("res"(a,t,b,N),Pi_1)$
    #linebreak()
    $a+|tau| <= b+N$
    #linebreak()
    $"read"(Pi_1,a,|tau|,t)=Pi_2$
  ], [
    $S tack "copy" p ⇓_tau (mu[a..a+|tau|),S[Pi arrow.r Pi_2])$
  ]),
  infer([reference], [
    $S tack_a p ⇓ ("res"(a,t,b,N),Pi_1)$
    #linebreak()
    $a+|tau| <= b+N$
    #linebreak()
    $"ref"(Pi_1,a,|tau|,t,k,c,m)=(Pi_2,u)$
  ], [
    $S tack "ref"(k,c,m,p) ⇓_("Ptr" tau)$
    #linebreak()
    $(["ptr"(b,a-b,N,u)],S[Pi arrow.r Pi_2])$
  ]),
)

Assignment threads the complete states returned by these phases. Write
$"write"(S,a,t,b,N,v)=S'$ for the operation that checks
$a+"len"(v)<=b+N$, applies `useMut` through $t$, replaces the selected cells,
and increments the source PC. The transition order is:

#infer([assignment], [
  $"prepare"(S,d)=S_1$
  #linebreak()
  $S_1 tack e ⇓_tau (v,S_2)$
  #linebreak()
  $S_2 tack_a d ⇓ ("res"(a,t,b,N),Pi_3)$
  #linebreak()
  $"write"(S_2[Pi arrow.r Pi_3],a,t,b,N,v)=S_3$
], [
  $S tack d:=e arrow.r S_3$
])

This formulation preserves environment and allocator changes made during
preparation and all state changes made by RHS evaluation. Crucially, the whole
RHS is evaluated before destination access resolution. Hence `copy(p)`
materializes its cells before a destination access can invalidate a tag needed
by the source.

At the program level, the current PC selects a statement. A successful
assignment advances it through `write`; `halt` and a missing statement leave
the state fixed. A fuel-bounded run repeatedly performs these steps and stops
at the first error or fixed point.

== Running source execution

Take the one-local context

#align(center)[
  $Gamma=[("Nat",("Nat","Nat"))]$
]

and let $x$ be its index-zero local. Assume $x$ was previously allocated by
`own`, so that $E(x)=(100,t_x)$ and $t_x$ is the owning tag for the three-cell
block. Let

#align(center)[
  $mu(100)="word"(5) quad mu(101)="word"(7) quad
    mu(102)="word"(9).$
]

Write $q_1$ for the path selecting the outer tuple's second field and $q_0$
for the path selecting that inner tuple's first field. Their types and offsets
are

#align(center)[
  $q_1:("Nat",("Nat","Nat")) arrow.r ("Nat","Nat")$
  #linebreak()
  $q_0:("Nat","Nat") arrow.r "Nat" quad
    "off"(q_1)=1 quad "off"(q_0)=0.$
]

The surface spelling `x.1.0` denotes the nested place $(x.q_1).q_0$; the
composed path used later is $q_1."append"(q_0)$ and has offset $1+0=1$.
Root preparation is a no-op because $x$ is already bound. The place
derivation is explicit:

#align(center)[
  $S tack_a x ⇓ ("res"(100,t_x,100,3),Pi)$
  #linebreak()
  $S tack_a x.q_1 ⇓ ("res"(101,t_x,100,3),Pi)$
  #linebreak()
  $S tack_a (x.q_1).q_0 ⇓ ("res"(101,t_x,100,3),Pi).$
]

The inner zero-offset projection changes neither the address nor provenance.
The constant transition produces $["word"(42)]$. Assume the permission model
accepts the one-cell write:

#align(center)[
  $"useMut"(Pi,101,1,t_x)=Pi_s'.$
]

If $S=(i,E,mu,Pi)$, the assignment rule therefore yields

#align(center)[
  $S tack (x.q_1).q_0 := "const"(42) arrow.r$
  #linebreak()
  $(i+1,E,mu[101 arrow.r "word"(42)],Pi_s').$
]

The visible block is now $[5,42,9]$. There is no source retag: both projections
are structural, and the write uses $t_x$ directly. Address 102, corresponding
to sibling path `.1.1`, is untouched. This single `useMut` event is the
behavior the longer target trace must simulate.

#source([Formalization of the typed syntax and source transition system: `src/obseq3/syntax.lean` and `src/obseq3/mirlite_semantics.lean`.])

= OSEA-IR <sec:oseair>

OSEA-IR is a register machine that exposes the memory and permission events
implicit in a MIRLite statement. A source place is gone: an instruction names
a register containing a concrete pointer, an offset, and a number of cells.
Consequently one source step may require several target steps and may create
short-lived tags that have no source counterpart; @sec:compiler names them
route tags and fixes exactly when they are created and retired.

== Values, runtime types, and programs <sec:target-values>

Target values and runtime types are distinct from MIRLite layouts:

#align(center)[
#box(width: 97%, inset: 6pt, stroke: 0.5pt + rule, radius: 2pt)[
#table(
  columns: (18%, 4%, 78%),
  stroke: none,
  inset: 2pt,
  [$v$], [$::=$], [$"undef" | "dat"(w) | "ptr"(b,o,s,t)$],
  [$theta$], [$::=$], [$"NatTy" | "PTy" | "TupTy"([theta_1,dots,theta_n])$],
  [$R$], [$::=$], [$[r mapsto (theta,[v_1,dots,v_n])]$],
  [$Q$], [$::=$], [$NN mapsto "option"(I)$],
)
]]

The pointer fields have the same meaning as at the source: allocation base
$b$, current offset $o$, allocation size $s$, and provenance tag $t$.
`dat` is a machine word. `undef` represents an absent or explicitly
uninitialized cell. A register entry contains a runtime type and an entire
cell list; the register file itself is a finite shadowing map.

The erasure $floor(tau)$ converts a source layout to a runtime type:

#align(center)[
  $floor("Nat")="NatTy" quad
   floor("Ptr" tau)="PTy" quad
   floor((tau_1,dots,tau_n))="TupTy"([floor(tau_1),dots,floor(tau_n)]).$
]

Thus all pointer layouts erase to `PTy`: OSEA-IR records that a register holds
a pointer, but not the pointee layout. Sizes agree,
$"typeSize"(floor(tau))=|tau|$. This distinction matters in the rules below:
a target load is indexed by $theta$, not by a source layout $tau$.

The relevant RHS and instruction syntax is:

#align(center)[
#box(width: 98%, inset: 6pt, stroke: 0.5pt + rule, radius: 2pt)[
#table(
  columns: (14%, 4%, 82%),
  stroke: none,
  inset: 2pt,
  [$h$], [$::=$], [$"load"_theta(r) | "alloc"_theta | "allocN"_theta(n)$],
  [], [], [$| "allocDyn"_theta(r) | "borrow"(k,c,m,n,r,delta)$],
  [], [], [$| "expose"(r) | "fromExposed"(r) | "offset"(r,d) | "borrowRest"(k,c,r)$],
  [$I$], [$::=$], [$r := h | "store"_theta(r_s,r_p) | "storec"_theta([v_1,dots,v_n],r_p)$],
  [], [], [$| "memcpy"_theta(r_d,r_s) | "die"(r,n) | "dealloc"(r)$],
  [], [], [$| "skipIf"(r,w,n) | "pushProt" | "popProt" | "halt"$],
)
]]

The full syntax is shown because it fixes the executable language boundary.
The correctness theorem in the final section covers a smaller core. A target
program $Q$ is a partial map from numeric labels to instructions. Partiality
lets the compiler extend code without renumbering an earlier fragment.

== Machine state and RHS evaluation

A target state is

#align(center)[
  $T=(j,R,mu_t,Pi_t).$
]

$j$ is the program counter. Target memory maps addresses to target values and
also carries a bump-allocation watermark and an allocation table. A missing
memory cell reads as `undef`. The permission state is parameterized; the
correctness result uses the same per-cell Stacked Borrows instance as
MIRLite.

Write

#align(center)[
  $T tack h ⇓ (theta,bar(v),T')$
]

when evaluating $h$ succeeds with runtime type $theta$, value cells
$bar(v)$, and state $T'$. Evaluation may update memory or permissions but
does not advance $j$. The two operations used by the running example are:

#grid(
  columns: (1fr, 1fr),
  column-gutter: 7pt,
  infer([T-Load], [
    $R(r)=(theta_r,["ptr"(b,o,s,t)])$
    #linebreak()
    $a=b+o quad b<=a quad a+"typeSize"(theta)<=b+s$
    #linebreak()
    $"read"(Pi_t,a,"typeSize"(theta),t)=Pi_t'$
  ], [
    $(j,R,mu_t,Pi_t) tack "load"_theta(r) ⇓$
    #linebreak()
    $(theta,mu_t[a..a+"typeSize"(theta)),(j,R,mu_t,Pi_t'))$
  ]),
  infer([T-Borrow], [
    $R(r)=(theta_r,["ptr"(b,o,s,t)])$
    #linebreak()
    $a=b+o+delta quad a+n<=b+s$
    #linebreak()
    $"ref"(Pi_t,a,n,t,k,c,m)=(Pi_t',u)$
  ], [
    $(j,R,mu_t,Pi_t) tack "borrow"(k,c,m,n,r,delta) ⇓$
    #linebreak()
    $("PTy",["ptr"(b,o+delta,s,u)],(j,R,mu_t,Pi_t'))$
  ]),
)

Both rules require $r$ to contain exactly one pointer; the stored runtime
type $theta_r$ is immaterial to pointer extraction. `load` checks both ends
of the complete range. `borrow` checks its upper bound; offsets are natural
words, so no separate negative-offset case exists. In particular, a
zero-length borrow at one past the end is legal and performs a zero-cell
permission operation.

Allocation illustrates an RHS that changes both memory and permissions. If
the allocator returns fresh base $b$ for $"typeSize"(theta)$ cells and

#align(center)[
  $"own"(Pi_t,b,"typeSize"(theta))=(Pi_t',u),$
]

then $"alloc"_theta$ returns
$(["ptr"(b,0,"typeSize"(theta),u)],"PTy")$. `allocN` allocates
$n dot "typeSize"(theta)$ cells. `allocDyn` first reads a `dat` value through
the pointer in its register, then allocates that many elements. This order
matches the source's permission-visible length read.

The remaining pointer RHSs are operational rather than mere casts.
`expose` reads a pointer-valued cell and exposes the stored tag;
`fromExposed` reads an integer cell and returns a wildcard-tagged pointer;
`offset` reads a stored pointer and changes its offset while preserving its
tag; and `borrowRest` reads a stored pointer and retags the remaining range
from its runtime offset to the end of its allocation. Wrong register shape,
wrong memory value, out-of-bounds arithmetic, or a failed permission call
produces an error.

== Instruction steps

We write $Q tack T arrow.r T'$ when fetching and executing one instruction
succeeds. Assignment evaluates its RHS before inserting the returned entry:

#align(center)[
#infer([T-Assgn], [
  $Q(j)=r:=h quad (j,R,mu_t,Pi_t) tack h ⇓ (theta,bar(v),(j,R_1,mu_1,Pi_1))$
], [
  $Q tack (j,R,mu_t,Pi_t) arrow.r (j+1,R_1[r mapsto (theta,bar(v))],mu_1,Pi_1)$
])
]

Stores share a helper that extracts one pointer
$"ptr"(b,o,s,t)$ from $r_p$, checks
$b+o+"len"(bar(v))<=b+s$, performs
$"useMut"(Pi_t,b+o,"len"(bar(v)),t)=Pi_t'$, writes the cells, and advances
the PC. The two store forms supply $bar(v)$ differently:

#block(breakable: false)[
#table(
  columns: (22%, 34%, 44%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Instruction],
  text(fill: white, weight: "bold")[Additional check],
  text(fill: white, weight: "bold")[Permission and memory effect],
  [$"store"_theta(r_s,r_p)$], [$R(r_s)=(theta,bar(v))$.], [`useMut` for $"len"(bar(v))$ cells, then write $bar(v)$.],
  [$"storec"_theta(bar(v),r_p)$], [$"len"(bar(v))="typeSize"(theta)$.], [The same write-through-pointer operation.],
  [$"memcpy"_theta(r_d,r_s)$], [Both registers contain pointers; complete ranges fit and do not overlap.], [`read` the source range, `useMut` the destination range, then copy.],
)
]

For $"die"(r,n)$, the register must contain one pointer and the machine
calls $"die"(Pi_t,b+o,n,t)$. On success only permissions and the PC change.
Unlike load, borrow, and store, this instruction performs no separate
allocation-range check: its admissibility is exactly that of the permission
operation. `dealloc` additionally requires offset zero, retires the whole
allocation, and removes its cells. Protector instructions update the frame
stack. `skipIf` inspects a `dat` discriminant without a permission event and
either advances one label or skips the following $n$ labels.

If $Q(j)$ is missing or is `halt`, the state is a fixed point. Define
$Q tack T arrow.r^n T'$ by exactly $n$ iterations of the step function.
Iteration does not stop early at a fixed point, so additional fuel simply
repeats it; an error aborts immediately. This convention makes the target
step count in the simulation existential without requiring a separate
reflexive-transitive-closure relation.

== Remaining operational cases

The other RHS forms use the same three-stage pattern: validate the register
shape, perform permission events in source order, then construct a result.
Writing $R(r)=(theta_r, ["ptr"(b,o,s,t)])$ and $a=b+o$, their successful behavior is:

#table(
  columns: (20%, 39%, 41%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[RHS],
  text(fill: white, weight: "bold")[Permission-visible work],
  text(fill: white, weight: "bold")[Returned register entry],
  [$"allocN"_theta(n)$], [`own` a fresh $n dot "typeSize"(theta)$-cell block.], [$"PTy"$ and one base pointer spanning the block.],
  [$"allocDyn"_theta(r)$], [`read` one cell at $a$; require `dat(n)`; then `own` a fresh $n dot "typeSize"(theta)$-cell block.], [The fresh base pointer at runtime type `PTy`.],
  [$"expose"(r)$], [`read` the pointer cell at $a$; require a stored pointer and expose its tag.], [$"NatTy"$ and `dat` of the stored pointer's current address.],
  [$"fromExposed"(r)$], [`read` the integer cell at $a$ (the place must be in bounds); resolve it against the allocation table.], [`PTy` and a pointer carrying the wildcard tag.],
  [$"offset"(r,d)$], [`read` the pointer cell at $a$; reject a negative resulting offset.], [`PTy` and the stored pointer with offset increased by $d$; preserve its tag.],
  [$"borrowRest"(k,c,r)$], [`read` the pointer cell at $a$; then `ref` its remaining $s-o$ cells with empty mask.], [`PTy` and the stored pointer carrying the fresh tag.],
)

Notice that these instructions read _through the outer pointer in the
register_ before inspecting the value in memory. For example, `offset` does
not change the offset of that outer pointer. It loads a pointer-valued cell,
changes the loaded value, and returns the result in a register. This is why
the compiler can use the same RHS to implement MIRLite pointer arithmetic
without suppressing the source read event.

The instruction-only cases have equally concrete state effects:

#table(
  columns: (19%, 81%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Instruction],
  text(fill: white, weight: "bold")[Successful transition],
  [`dealloc(r)`], [Require one pointer with offset zero; call `dealloc` on its entire allocation, remove those memory cells, and advance. The bump allocator does not reuse the range.],
  [`skipIf(r,w,n)`], [Require one pointer and $"dat"(w')$ at its current address. If $w'=w$, advance to $j+1$; otherwise advance to $j+1+n$. This inspection intentionally has no permission event, matching the source conditional.],
  [`pushProt`], [Push an empty protector frame and advance.],
  [`popProt`], [Pop the top frame if the permission model permits it, then advance.],
  [`halt`], [Return the input state unchanged.],
)

There is no global well-formedness premise saying every register cell list
matches its runtime type. Instead, the instruction that consumes a register
checks the shape it needs. A load requires a singleton pointer but ignores
the entry's stored type; `store` checks source-type equality; `storec` checks
constant length; and pointer-manipulating forms require a pointer-valued
memory cell after their read. This design keeps malformed target programs
executable with explicit errors while the compiler proves that its own
successful outputs meet the required local checks.

== Error boundaries

OSEA-IR errors fall into four semantic classes rather than one generic
“stuck” state:

#table(
  columns: (23%, 36%, 41%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Class],
  text(fill: white, weight: "bold")[Typical cause],
  text(fill: white, weight: "bold")[Where detected],
  [Register shape], [Missing register, non-pointer singleton, or wrong source runtime type.], [Before any memory or permission change.],
  [Value shape], [A cast, dynamic allocation, or branch observes the wrong memory-value constructor.], [After any required permission read, so that event order remains explicit.],
  [Spatial], [A complete access range exceeds its allocation, a pointer offset becomes negative, or `memcpy` overlaps.], [Before the corresponding read/write permission event.],
  [Permission], [`read`, `ref`, `useMut`, `die`, `dealloc`, or protector pop rejects the operation.], [At the abstract permission interface; its error is propagated.],
)

The forward simulation only starts from a successful source step. It therefore
proves that the compiled fragment avoids all of these errors for the covered
cases; it does not claim that source and target failure messages coincide.

== Running OSEA-IR execution

Let $tau_x=("Nat",("Nat","Nat"))$ and
$theta_x=floor(tau_x)$. At entry:

#align(center)[
  $T_0=(j,R_0,mu_0,Pi_0) quad
   R_0(r_x)=("PTy",["ptr"(100,0,3,hat(t)_x)])$
  #linebreak()
  $mu_0[100..103)=["dat"(5),"dat"(7),"dat"(9)].$
]

The register type is `PTy`, not the source layout $"Ptr" tau_x$. Assume the
three permission calls needed by the fragment succeed:

#align(center)[
  $"ref"(Pi_0,101,1,hat(t)_x,"mutable","false",[])=(Pi_1,u)$
  #linebreak()
  $"useMut"(Pi_1,101,1,u)=Pi_2 quad
  "die"(Pi_2,101,1,u)=Pi_3.$
]

Install the following code:

#align(center)[
#table(
  columns: (18%, 82%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  [$Q(j)$], [$r_f := "borrow"("mutable","false",[],1,r_x,1)$],
  [$Q(j+1)$], [$"storec"_"NatTy"(["dat"(42)],r_f)$],
  [$Q(j+2)$], [$"die"(r_f,1)$],
)
]

The rules determine all intermediate states:

#align(center)[
  $T_0 arrow.r
   T_1=(j+1,R_0[r_f mapsto ("PTy",["ptr"(100,1,3,u)])],mu_0,Pi_1)$
  #linebreak()
  $arrow.r T_2=(j+2,R_1,mu_0[101 mapsto "dat"(42)],Pi_2)$
  #linebreak()
  $arrow.r T_3=(j+3,R_1,mu_0[101 mapsto "dat"(42)],Pi_3).$
]

Thus $Q tack T_0 arrow.r^3 T_3$. The temporary register remains, but its
permission item has been retired. The target performs one extra `ref` and
one extra `die`; its sole memory update is the same one-cell update as the
source.

#source([Formalization of target values, RHS evaluation, instruction stepping, and fuelled execution: `src/obseq3/oseair.lean`.])

= Compiler <sec:compiler>

The compiler is a state-passing translation from typed MIRLite syntax to
OSEA-IR code. Its semantic obligation is to preserve source evaluation order
while introducing explicit loads, retags, stores, and retirement of
route tags (@def:route).

== Compiler state and translation judgments

A compiler state is

#align(center)[
  $C=(n_r,n_l,K,L).$
]

$n_r$ and $n_l$ are the next fresh register and label. $K$ is the emitted
code map, and $L$ maps a source-local index to a pair $(r,tau)$. The layout in
$L$ is a source layout; code uses its runtime erasure. A compiler computation
is monotone: counters do not decrease, code below the old $n_l$ is unchanged,
and every old local-map entry remains present.

For states $C=(n_r,n_l,K,L)$ and $C'=(n_r',n_l',K',L')$, define their emitted
interval

#align(center)[
  $"new"(C,C')=[K'(n_l),K'(n_l+1),dots,K'(n_l'-1)].$
]

This makes the translation judgments state what the executable compiler
does, without pretending that it separately returns a code list:

#align(center)[
  $C tack_k p arrow.r C';(r,D) quad
  C tack e arrow.r C';(F,D_e) quad
  C tack s arrow.r C'.$
]

The first judgment lowers place $p$, leaves its pointer in $r$, and returns
cleanup list $D$. Its index $k$ is the retag kind of @sec:syntax: any
route borrow the lowering emits, in the sense of the following definition,
uses $k$. Reads lower their place with $k="shared"$ and assignment
destinations with $k="mutable"$.

#definition("Route borrow")[
  A _route borrow_ is a `borrow` instruction emitted by place lowering to
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
tag that the source program also stores. Cleanup reverses $D$ and emits a
`die` for each entry. The expression judgment emits all
pre-destination work, returns a store function $F$ waiting for a destination
register, and records any post-store cleanup. The statement judgment emits
the complete fragment.

Compilation is checked. A local lookup may fail when lowering a read whose
root has not been established. Unsupported is retained as a future-facing
error, although the current compiler handles every executable source
constructor. Successful computations still carry the monotonicity property.

== Establishing local roots

Writing an unbound root must mirror source preparation. If $L(ell)$ is
already defined, root preparation returns its register and emits nothing. If
it is absent and $ell:tau$, the compiler chooses fresh $r$, emits

#align(center)[
  $r := "alloc"_(floor(tau)),$
]

and extends $L$ with $ell mapsto (r,tau)$. For a projected destination it
recurses to the base, and for a dereference it recurses to the pointer place.
This happens before RHS lowering, just as MIRLite allocates an unbound
assignment root before evaluating the RHS.

Read lowering does not silently allocate a missing local. This separates two
semantic facts: assignment preparation may establish a root; resolving a
source read requires that the root already exist.

== Canonical projections and flattening

A place may contain nested projections, but emitting a borrow for each
syntactic layer would change the accessed ranges. The canonical operation
fuses adjacent paths:

```lean
def projInto : Place Γ σ → PathTo σ τ → Place Γ τ
  | .proj b q, p => .proj b (q.append p)
  | b,        p => .proj b p

def flattenPlace : Place Γ τ → Place Γ τ
  | .local l     => .local l
  | .deref p     => .deref (flattenPlace p)
  | .proj b path => projInto (flattenPlace b) path
```

Here $sigma$ and $tau$ are the traversed and selected layouts of a typed
path, as in @sec:syntax; the code is not manipulating untyped field lists. If
$q:sigma_0 arrow.r sigma$ and
$p:sigma arrow.r tau$, then

#align(center)[
  $q."append"(p):sigma_0 arrow.r tau quad and quad
  "off"(q."append"(p))="off"(q)+"off"(p).$
]

Flattening stops at a dereference because an offset cannot be moved across a
memory-loaded pointer. It preserves the selected layout and the source
resolution result. The compiler implements the same normalization on the
fly: when it sees $(b.q).p$, it restarts lowering at
$b.(q."append"(p))$ before emitting any projection borrow.

== Ordinary place lowering

After reassociation, ordinary lowering is defined by the following cases.
The selected place has layout $tau$.

#table(
  columns: (20%, 42%, 38%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Place],
  text(fill: white, weight: "bold")[Translation],
  text(fill: white, weight: "bold")[Returned result],
  [$ell$], [Look up $L(ell)=(r,tau)$.], [$(r,[])$; no code.],
  [$b.q$, $"off"(q)=0$], [Lower $b$ with the same kind $k$.], [Reuse the base register and cleanup.],
  [$b.q$, $delta="off"(q)>0$], [Lower $b$ to $(r_b,D_b)$; choose fresh $r_f$; emit $r_f:="borrow"(k,"false",[],|tau|,r_b,delta)$.], [$(r_f,D_b+[(r_f,|tau|)])$.],
  [$star p$], [Lower pointer place $p$ shared; load `PTy` into fresh $r$; retire only the route tags used to reach $p$.], [$(r,[])$. The loaded tag came from memory and is not a route tag.],
)

Offset-zero projections reuse the base pointer because they denote the same
address and require no narrower pointer. Nonzero projections emit a route
borrow (@def:route), and so borrow only the _final selected width_. A
dereference loads a pointer cell. It must not retire the loaded pointer: its
tag belongs to the source program, whereas cleanup is only for route tags.

For $x.1.0$, direct recursive lowering without reassociation would first
borrow the two-cell field $x.1$ and then reuse its offset-zero subfield. That
would touch addresses 101 and 102. Flattening instead emits one borrow of
width one at composed offset one, leaving sibling $x.1.1$ untouched.

== Escaping-borrow place lowering

Reference formation needs a distinct judgment

#align(center)[
  $C tack_(k,c,m)^"borrow" p arrow.r C';(r,D).$
]

It follows the same path normalization but always emits a final
$"borrow"(k,c,m,|tau|,r_b,delta)$, including when $delta=0$. For a dereference
it first loads the stored pointer and then borrows the pointed-to range. The
returned cleanup records the fresh final tag as a description of its origin,
but compiling a reference expression deliberately does not emit that
cleanup: the tag escapes in the pointer value stored by the program.

This contrasts with a route borrow. A route tag is used for one store and
then retired before the next source-statement boundary. An escaping tag is
an observable result and must remain live; the correctness proof extends the
source-to-target tag map with its fresh pair.

== Expressions and assignment order <sec:compiler-order>

For an expression of layout $tau$, pre-lowering returns a store function
$F$. The proof-core cases are:

#block(breakable: false)[
#table(
  columns: (17%, 44%, 39%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[MIRLite RHS],
  text(fill: white, weight: "bold")[Pre-destination code],
  text(fill: white, weight: "bold")[Deferred store $F(r_d)$],
  [$n$], [No code.], [$"storec"_"NatTy"(["dat"(n)],r_d)$.],
  [$"copy" p$], [Lower $p$ shared; load $|tau|$ cells as $floor(tau)$ into fresh value register $r_v$; retire its route tags.], [$"store"_(floor(tau))(r_v,r_d)$.],
  [$"ref"(k,c,m,p)$], [Use escaping-borrow lowering and retain the resulting tag.], [$"store"_"PTy"(r_v,r_d)$.],
)
]

The copied cells are materialized in a register before destination lowering.
This is essential when source and destination resolution have observable
permission effects: it realizes the source rule's “evaluate RHS, then resolve
destination, then write” order.

For a nonlocal assignment $d:=e$, the emitted intervals concatenate as

#align(center)[
#box(width: 98%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"ensureRoot"(d) ; I_"rhs" ; I_"dst" ; F(r_d)
    ; "cleanup"(D_e) ; "cleanup"(D_d).$
]]

A local destination is simpler: root preparation directly produces its
pointer register, so the compiler performs the RHS pre-work and store through
that register. In both cases preparation precedes the RHS. For nonlocal
destinations the RHS precedes destination place lowering.

The executable compiler also lowers uninitialized values, exposed-provenance
casts, tag-preserving pointer casts, scaled pointer arithmetic, slice retags,
heap allocation, deallocation, conditionals, and protector frames. Each
translation is defined by an OSEA-IR sequence, not by a constructor-name
correspondence. For example, dynamic allocation lowers its length place
shared and emits `allocDyn`, while deallocation loads the pointer value before
emitting `dealloc`.

== Complete expression lowering

The non-core RHSs use the same pre-code/store split. In the table, `lower
shared` returns a pointer register $r_s$ and route cleanup $D_s$; $r_v$ is a
fresh value register. Every cleanup shown next to a pre-instruction is emitted
immediately after it, before destination lowering.

#table(
  columns: (21%, 45%, 34%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[MIRLite RHS],
  text(fill: white, weight: "bold")[Pre-destination code],
  text(fill: white, weight: "bold")[Deferred store],
  [`uninit`], [No code.], [$"storec"_(floor(tau))(["undef"]^|tau|,r_d)$.],
  [`exposeAddr p`], [Lower $p$ shared; emit $r_v:="expose"(r_s)$; clean $D_s$.], [$"store"_"NatTy"(r_v,r_d)$.],
  [`fromExposed p`], [Lower $p$ shared; emit $r_v:="fromExposed"(r_s)$; clean $D_s$.], [$"store"_"PTy"(r_v,r_d)$.],
  [`ptrOffset p d`], [Lower $p$ shared; emit $r_v:="offset"(r_s,d dot |tau_p|)$, where $Gamma tack p:"Ptr" tau_p$; clean $D_s$.], [$"store"_"PTy"(r_v,r_d)$.],
  [`refSlice(k,c,p)`], [Lower $p$ shared; emit $r_v:="borrowRest"(k,c,r_s)$; clean $D_s$.], [$"store"_"PTy"(r_v,r_d)$.],
  [`ptrCast p`], [Lower $p$ shared; no value register. Its route cleanup must remain live until the copy.], [$"memcpy"_"PTy"(r_d,r_s)$, then clean $D_s$.],
)

$["undef"]^|tau|$ denotes a list of exactly $|tau|$ undefined cells. Pointer
offsets are expressed by the source in pointee units, so the compiler scales
$d$ by the source pointee width before OSEA-IR sees it. A pointer cast is
tag-preserving: using `borrow` would incorrectly mint a new tag, whereas a
one-cell `memcpy` performs the required read and write while copying the
pointer value unchanged.

The placement of cleanup is semantic. In `exposeAddr`, for example, the
route tag is needed only until the RHS reads its pointer-valued cell, so
it dies before destination evaluation. In `ptrCast`, the route pointer is the
source of the eventual `memcpy`, so it survives destination evaluation and
dies after the store.

== Statements outside the proof core

The compiler is executable on all source statement forms. Their code order is:

#table(
  columns: (20%, 80%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Statement],
  text(fill: white, weight: "bold")[Emitted operational sequence],
  [`alloc d (const n)`], [Prepare the destination root; lower $d$ mutable; emit fresh $r_h:="allocN"_(floor(tau))(n)$; store `PTy` from $r_h$ through $d$; retire the destination's route tags.],
  [`alloc d (from p)`], [Prepare and lower $d$; lower length place $p$ shared; emit $r_h:="allocDyn"_(floor(tau))(r_p)$ and clean the length route; store the heap pointer through $d$; retire the destination's route tags.],
  [`dealloc p`], [Lower $p$ shared; load its `PTy` value into fresh $r_v$; retire only route tags; emit `dealloc(r_v)`.],
  [`assignIf p=w d:=e`], [Lower the discriminant shared and clean its route; emit `skipIf` whose relative skip equals the dry-run length of the compiled assignment; then emit that assignment.],
  [`pushProtectors`], [Emit `pushProt`.],
  [`popProtectors`], [Emit `popProt`.],
  [`halt`], [Emit `halt`.],
)

For a local allocation destination, root preparation already returns the
store pointer, so no separate mutable destination lowering is needed. For a
nonlocal destination, the table's order is deliberate: destination
resolution occurs before evaluating a dynamic heap length, matching the
source allocation statement rather than the ordinary assignment rule.

Conditional lowering uses a dry run only to compute the guarded fragment's
length. Both the probe and real compilation start with the same fresh-register
counter and local map, so they emit the same relative-register instruction
sequence. Only the real pass extends the code map.

== Program compilation and labels <sec:compiler-labels>

Emission installs a list contiguously at labels
$[n_l,n_l+"len"(I))$ and then advances $n_l$. Compiling a source program folds
statement compilation from left to right. If every checked statement
succeeds, the target program is the final code map; otherwise compilation
returns the first compiler error.

For source statement index $i$, compiling the prefix $P[0..i)$ from $C_0$
produces a state $C_i$. Its next label $C_i.n_l$ is the target entry label for
statement $i$. Monotonicity gives two facts needed by simulation:

#align(center)[
  $C_i.n_l <= C_(i+1).n_l quad and quad
  forall q<C_i.n_l. C_(i+1).K(q)=C_i.K(q).$
]

Thus compiling later statements cannot change an already recovered fragment.
No fixed instruction-per-statement ratio is assumed: the proof locates a
source boundary by replaying prefix compilation and lets each simulation case
choose the number of target steps in that interval.

== A dereference-lowering example

The field example contains only projections. A small dereference example
shows why pointer loads and cleanup are separate. Suppose
$p:"Ptr" tau$ is stored in local $y$, with $L(y)=(r_y,"Ptr" tau)$. Lowering
$star y$ shared first returns $r_y$, then chooses fresh $r_p$ and emits

#align(center)[
  $r_p := "load"_"PTy"(r_y).$
]

The result is $(r_p,[])$. There is no `die(r_p,1)`: the loaded pointer's tag
was stored by the source program. For projected place $(star y).q$ with
nonzero offset $delta$, lowering next emits a compiler borrow from $r_p$ of
the final field width and records only that new register in cleanup. A store
therefore executes `load; borrow; store; die`, retiring the route tag
without retiring the source pointer loaded from memory.

== Running compilation derivation

Assume compiler entry state

#align(center)[
  $C_0=(N,j,K,L) quad L(x)=(r_x,tau_x),$
]

where $tau_x=("Nat",("Nat","Nat"))$, $K$ has no code at or above $j$,
$r_f=R(N)$ is fresh, and $j$ is the next label. No allocation is emitted:
$x$ already has a local-map entry.

Flattening gives

#align(center)[
  $(x.1).0 arrow.r x.(1."append"(0)) quad
  "off"(1."append"(0))=1 quad |"Nat"|=1.$
]

The constant has no pre-code. Destination lowering is mutable, uses $r_x$ as
the base register, and emits one final-width borrow. The store function and
cleanup then determine the rest. Hence

#align(center)[
  $C_0 tack x.1.0:=42 arrow.r C_3,$
]

where $C_3$ has $n_r=N+1$, $n_l=j+3$, the same local map, and

#align(center)[
#table(
  columns: (20%, 80%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  [$K_3(j)$], [$r_f := "borrow"("mutable","false",[],1,r_x,1)$],
  [$K_3(j+1)$], [$"storec"_"NatTy"(["dat"(42)],r_f)$],
  [$K_3(j+2)$], [$"die"(r_f,1)$],
)
]

Every number is now derived: path composition gives offset one; the selected
layout gives borrow length one; erasure gives `NatTy`; the constant gives
`dat(42)`; and reversing the singleton cleanup gives the last instruction.
This is exactly the OSEA-IR execution derived in the previous section.

#source([Formalization of compiler state growth, checked lowering, and program compilation: `src/obseq3/compile.lean`. Flattening and its semantic preservation are in `src/obseq3/proof/spine.lean`.])

= Compiler correctness <sec:correctness>

Correctness is a forward simulation of successful executions. Literal state
equality is impossible: the target has registers and introduces route
tags (@def:route). The relation instead compares source-observable memory, local pointers,
and permission stacks at source-statement boundaries. This section defines
the relation (@def:rename to @def:inv), states the two lemmas the proof
turns on (@lem:mono and @lem:cancel), and then states the simulation
theorems (@thm:step to @cor:closed).

== Renamings and value simulation

#definition("Renamings")[
  An _address renaming_ is a partial map $rho_a:NN arrow.r "option"(NN)$
  and a _tag renaming_ is a partial map
  $rho_t:"Tag" arrow.r "option"("Tag")$. A renaming $rho'$ _extends_
  $rho$, written $rho subset.eq rho'$, when $rho'$ agrees with $rho$
  wherever $rho$ is defined.
] <def:rename>

Both maps are partial because future allocations and tags have not yet been
created. Address renaming turns out to be the identity on its domain, for a
reason that combines a property of the two machines with a property of the
compiler. Each machine allocates with a deterministic bump allocator that
never reuses addresses, and both start at the same watermark. The compiler
emits exactly one target allocation, of the same size, for each source
allocation, and in the same order. Hence the two watermarks stay equal at
every statement boundary, and each fresh block receives the same base on
both sides:

#align(center)[
  $rho_a(a)=a' arrow.r a'=a.$
]

The notation remains useful because allocation extends the domain by a whole
fresh block. Tags genuinely require renaming: route borrows advance the
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

== Permission simulation

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

== The boundary invariant

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
    watermarks are equal.
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
- (I8) with the block-domain part of (I2): fresh roots receive the same
  base on both sides, which is what makes the identity renaming of
  @def:rename sound, and every cell of a multi-cell or zero-sized binding
  has the domain fact needed by later pointer simulation.
- (I10): a fresh register cannot collide with a register that the target
  uses as a source-local pointer.

Dropping any clause leaves a concrete compiler case underdetermined. Memory
agreement alone cannot show that a fresh `load` register does not overwrite
$r_x$, and equal watermarks alone cannot show that an unbound source local
corresponds to a target fragment containing `alloc`.

== Two lemmas

The step proof relies on a fact about the compiler and a fact about the
permission model.

#lemma("Prefix monotonicity")[
  Let $C_i$ and $C_(i+1)$ be the states obtained by compiling
  $P[0..i)$ and $P[0..i+1)$ from $C_0$. Then
  $C_i.n_l <= C_(i+1).n_l$, and $C_(i+1).K(q')=C_i.K(q')$ for every label
  $q'<C_i.n_l$.
] <lem:mono>

This is the monotonicity property of @sec:compiler-labels specialized to
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

== Simulation theorems

Let `srcStep` fetch the source statement at the current PC and execute it,
treating `halt` and a missing statement as successful fixed points. The
_core fragment_ consists of `halt` and assignments whose RHS is a constant,
a copy, or a reference with any retag kind $k$, protector flag $c$, and mask
$m$. Here "any kind" includes shared, mutable, both raw pointer kinds, and
two-phase. A program is _core_ when every statement in it is.

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
  @sec:prep and the compiler order of @sec:compiler-order:

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
  pair; $rho_a$ extends by the identity on the whole block and $rho_t$ by
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
  nowhere defined and let $rho_t$ map only the wildcard tag to itself. Then
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

== The running example as a simulation step

#example[
  Return to $x.1.0:=42$. At the source-statement boundary assume
  $ rho_a(100)=100 quad rho_t(t_x)=hat(t)_x $
  and let the invariant supply
  $ E(x)=(100,t_x) quad
    R(r_x)=("PTy",["ptr"(100,0,3,hat(t)_x)]) $
  $ mu_s[100..103)=["word"(5),"word"(7),"word"(9)] quad
    mu_t[100..103)=["dat"(5),"dat"(7),"dat"(9)]. $

  The source derivation of @sec:mirlite resolves the flattened path to
  address 101 and performs $"useMut"(Pi_s,101,1,t_x)=Pi_s'$. The compiler
  derivation of @sec:compiler supplies the exact three-instruction fragment,
  and the target derivation of @sec:oseair is
  $ "ref"(Pi_t,101,1,hat(t)_x,"mutable","false",[])=(Pi_1,u) $
  $ "useMut"(Pi_1,101,1,u)=Pi_2 quad
    "die"(Pi_2,101,1,u)=Pi_t'. $

  @lem:cancel removes the route tag $u$'s item and recovers (I4) under the
  unchanged $rho_t$: $u$ has no source counterpart and never escapes. Both
  memories update only address 101, where source word 42 relates to target
  `dat(42)`, so (I3) is restored and addresses 100 and 102 are framed.
  (I1) advances from source PC $i$ to $i+1$ and from target label $j$ to
  the next prefix label $j+3$. Therefore
  $ (i+1,E,mu_s[101 mapsto 42],Pi_s')
    approx_(rho_a,rho_t)^(C_0,P)
    (j+3,R',mu_t[101 mapsto "dat"(42)],Pi_t'). $

  Flattening is semantically load-bearing here. A borrow of intermediate
  width two would operate on address 102 as well, so @lem:cancel would not
  simulate the source's one-cell write in the presence of a sibling borrow.
  The compiled path must use the composed offset and final width.
] <ex:sim>

The boundary assumed in @ex:sim is itself produced by an earlier application
of @thm:step. Suppose the first statement assigns a constant to an unbound
local $x:tau$. MIRLite root preparation allocates $|tau|$ cells and obtains
owning tag $t_s$; target preparation emits $r_x:="alloc"_(floor(tau))$,
allocates the same base by (I8), and obtains $t_t$. The proof extends
$rho_a$ by the identity on the entire block, extends $rho_t$ with
$t_s mapsto t_t$, and extends the local map with $x mapsto (r_x,tau)$. The
subsequent store establishes (I3) for the initialized cells. The
environment, register, memory, and tag mapping assumed in @ex:sim are
precisely these facts, not an unexplained alternate initialization.

The four formal views of $x.1.0:=42$ thus line up. MIRLite's typed path has
input layout $tau_x$, selected layout `Nat`, composed offset one, and width
one; source resolution returns base 100, address 101, size three, and tag
$t_x$, and the statement performs one mutable permission use and one cell
write. OSEA-IR begins with an erased `PTy` pointer in $r_x$, which the
compiler's local map connects to $x:tau_x$. Flattening prevents an
intermediate two-cell borrow, so place lowering creates exactly one fresh
mutable tag for address 101; constant lowering supplies `dat(42)` and
`NatTy`; cleanup supplies the matching one-cell `die`. At the boundary,
address identity relates the updated cell, memory simulation frames its
neighbours, permission simulation cancels the route tag without adding
it to $rho_t$, and prefix compilation places the target at $j+3$ exactly
when the source reaches $i+1$:

#align(center)[
#box(width: 96%, inset: 5pt, fill: pale, stroke: 0.6pt + rule, radius: 2pt)[
  $"typed source range" arrow.r "flattened target route" arrow.r
    "explicit events" arrow.r "boundary simulation".$
]]

The example explains why the compiler may add a borrow, why that borrow must
have final-field width, why it must be retired, and which invariant clauses
make the extra events unobservable at the next source boundary.

== Observable consequences

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
cell, so the memory relation has no reverse-domain guarantee. Address maps are
partial even though defined pairs are identities. Tag counters need not be
equal, and numeric tag equality is not observable. Finally, the invariant is
required only at source-statement boundaries; intermediate target states may
contain live route tags.

These choices are the minimum abstraction needed by the actual generated
code. Strengthening to literal register equality would reject harmless
temporaries, while weakening permission stacks to ignore arbitrary target
items would no longer justify later accesses.

== Extending the theorem to the executable surface

The remaining compiler cases are specified and executable, but adding them to
@thm:step requires semantic simulation arguments. The needed work is not
"support the constructor"; it is to preserve the ten clauses of @def:inv
through each emitted sequence:

#table(
  columns: (24%, 76%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[Source form],
  text(fill: white, weight: "bold")[Missing simulation obligation],
  [`uninit`], [Relate the source's $|tau|$ undefined cells to the target's explicit `undef` list after corresponding mutable writes; re-establish (I3) without demanding information from those cells.],
  [`ptrCast` / `ptrOffset`], [For casts, prove the target `memcpy` realizes the source pointer-value copy without retagging. For offsets, transport the read and show scaling by the pointee width $|tau_p|$ agrees with source cell arithmetic and failure bounds.],
  [`refSlice`], [Relate the runtime remaining lengths of stored pointers, transport the two-stage read-then-retag event order, and extend $rho_t$ at the escaping tag pair.],
  [`alloc` / `dealloc`], [For allocation, synchronize a runtime or constant length and extend both renamings over the fresh heap block. For deallocation, relate offset-zero checks, permission retirement, and removal of the same memory range.],
  [`assignIf`], [Relate the event-free discriminant lookup and show both branch outcomes land at the prefix label following either the skipped or executed assignment fragment.],
  [Protector frames], [Show push and successful pop preserve the nested tag-list relation of @def:permsim, including protected tags introduced by source-visible references.],
)

Several obligations reuse existing core machinery, but none follows merely
from successful differential tests. In particular, `assignIf` needs a control
argument about relative skip length. Listing these obligations keeps the
stated theorem boundary aligned with what is actually proved.

The two integer-pointer casts were on this list until they were
discharged. `exposeAddr` and `fromExposed` compile exactly as `copy`
does, so abstracting the copy leaves over the emitted right-hand side
made every leaf, write seam and fragment lemma serve all three; what
remained was one simulation lemma per cast. The exposure is a cons onto
the exposed list, which @def:permsim already relates positionally. The
int-to-ptr direction needed two invariant strengthenings: the two
allocation tables travel in lockstep, so both machines resolve an
integer to the same block, and the address renaming is total, which
supplies the base of the degenerate pointer an unallocated address
yields. It also needed wildcard-tagged pointers to be admissible values,
and hence accesses through the wildcard to transport: both machines pick
the topmost exposed granting item out of related stacks, so they pick
corresponding items. That last step is why the theorem, for programs
using int-to-ptr casts, is a statement about our determinized wildcard
rule rather than about Miri's angelic one.

== Scope and mechanization status

#takeaway([PRECISE CLAIM], [
  The mechanized theorems are forward simulations for successful finite runs
  of core programs: `halt` and assignments from constants, copies, and
  references. The executable compiler covers the larger syntax described
  above, but those forms are outside @thm:step until their simulation
  cases are added.
])

Every numbered definition and result of this section is a Lean 4
declaration in `src/obseq3/proof/`:

#table(
  columns: (30%, 46%, 24%),
  inset: 3pt,
  stroke: 0.45pt + rule,
  fill: (col, row) => if row == 0 { accent } else if calc.even(row) { rgb("f6f8fa") } else { white },
  text(fill: white, weight: "bold")[This paper],
  text(fill: white, weight: "bold")[Lean declaration],
  text(fill: white, weight: "bold")[File],
  [@def:valsim], [`MemValSim`], [`common.lean`],
  [@def:memsim], [`SourceMemSim`], [`common.lean`],
  [@def:permsim], [`PermSim`], [`common.lean`],
  [@def:inv], [`CompilerInv`], [`common.lean`],
  [@lem:cancel], [`sb_ref_use_die_cancels`], [`keystone.lean`],
  [@thm:step], [`CompilerInv_step`], [`compiler.lean`],
  [@thm:run], [`compile_correct`], [`compiler.lean`],
  [@lem:init], [`CompilerInv_initial`], [`compiler.lean`],
  [@cor:closed], [`compile_correct_from_initial`], [`compiler.lean`],
)

None of these contains an admitted goal. A checked audit prints the axioms
that @thm:run and @cor:closed depend on and fails if that set differs in
either direction from a pinned whitelist. The whitelist contains exactly the
three standard Lean axioms, propositional extensionality, choice, and
quotient soundness, and no `sorryAx`. The last admitted case, the
reference-assignment leaves, was closed on 2026-08-31.

The broader executable compiler is validated by testing rather than proof:
a compiler witness corpus, a ULLBC conformance corpus checked against Miri
verdicts, and a differential run that compiles each conformance program and
requires the same verdict from both machines. Those tests cover the
constructs listed in the previous subsection, but only a discharged
simulation case moves a construct inside @thm:step.

#source([Invariant and simulation vocabulary: `src/obseq3/proof/common.lean`. Statement and whole-program forward simulations: `src/obseq3/proof/compiler.lean`.])
