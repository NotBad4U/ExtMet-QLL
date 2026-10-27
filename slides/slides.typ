// Slides for λ-FQLL.  Compile from the project root so that the paper sources
// are inside the project:
//
//   typst compile --root . slides/slides.typ
//
// The inference rules, syntax and notation are imported from paper/ (as in
// paper/spreadsheet.typ), so editing a section of the paper updates the deck.

#import "@preview/metropolyst:0.1.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule

// Notation shared with the paper: ⟨⟩, x :ʳ A, Prop, ⊢_p, ⊕ˢ, ∀ˢ, ∃ˢ, rule layout.
#import "../paper/common.typ": emptyctx, tcol, tcols, prop, ent, psum, fa, ex, rule-set
// The typing rules are renamed on import: `abs`, `case`, `fix`, ... would
// otherwise shadow the math functions of the same name.
#import "../paper/calculus.typ": (
  types-syntax, sem-types,
  var as r-var, abs as r-abs, app as r-app, pair as r-pair, proj as r-proj,
  inj as r-inj, case as r-case, tensor as r-tensor, letin as r-letin,
  dirac as r-dirac, probchoice as r-probchoice, letalg as r-letalg,
  zero as r-zero, succ as r-succ, rec as r-rec, fix as r-fix, term-syntax
)
#import "../paper/logic.typ": (
  prop-eq, prop-tens, prop-imp, prop-scale, prop-dual, prop-sum, prop-hsum,
  prop-all, prop-ex,
  l-ass, l-cut, l-relax, l-weak, l-tensR, l-tensL, l-impR, l-impL, l-eqI,
  l-allI, l-exE,
)

#let colors = (
  emerald: rgb("#00A99D"),
  royalblue: cmyk(100%, 50%, 0%, 0%),
  yellow: rgb(99%, 78%, 7%),
  gray: rgb(31%, 31%, 33%),
  bulletgray: rgb(60%, 60%, 61%),
  linegray: rgb(51%, 50%, 52%),
  lightgray: rgb(85%, 85%, 86%),
)

#show: metropolyst-theme.with(
  footer-progress: false,
  config-info(
    title: [$lambda$-FQLL],
    subtitle: [A sensitivity calculus and a soft first order quantitative logic],
    author: [Alessio Coltellacci],
    institution: [IT University of Copenhagen],
    date: [2026],
    // footer: [My cool footer], // defaults to none
  ),
  main-background-color: rgb("#ffffff"),
  progress-bar-background: rgb("#d6c6b7"),
  header-background-color: rgb("#23373b"),
  accent-color: colors.emerald,
  hyperlink-color: colors.royalblue,
)

#show math.equation: set text(font: "Fira Math")
// Fira Code keeps the >>=, <<=, ||= and |= shapes behind stylistic set ss09
#show raw: set text(font: "Fira Code", features: ("ss09",))

// ---------------- local notation and helpers ----------------

#let cext = $bold("CExtMet")$
#let ext = $bold("ExtMet")$
#let cmet = $bold("CMet")$
#let PP = $bb(P)$

// Theorem-like environments, styled for the theme (no numbering on slides).
#let env(kind, title: none, body) = block(
  width: 100%,
  inset: (x: 0.8em, y: 0.6em),
  radius: 3pt,
  fill: colors.emerald.lighten(90%),
  stroke: (left: 3pt + colors.emerald),
  {
    text(weight: "medium", fill: colors.emerald.darken(25%))[#kind]
    if title != none [ #text(weight: "medium")[(#title)]]
    [.#h(0.3em)]
    body
  },
)
#let definition = env.with([Definition])
#let theorem = env.with([Theorem])
#let proposition = env.with([Proposition])
#let example = env.with([Example])

// Pointers to the Rocq development: inline at the end of a sentence, or as a
// right-aligned tag closing a theorem box.
#let rocq(..names) = text(size: 0.55em, fill: colors.gray)[
  Rocq: #names.pos().map(n => raw(n)).join(", ")
]
#let rocq-tag(..names) = {
  v(0.1em)
  align(right, rocq(..names))
}

// Small gray remark.
#let remark(body) = text(size: 0.8em, fill: colors.gray, body)

// The running example: a Markov process with three states.
#let markov = diagram(
  node-stroke: 0.8pt,
  node-shape: circle,
  node-inset: 7pt,
  spacing: (5em, 2em),
  node((0, 0), $m$, name: <m>),
  node((1, 0), $z$, name: <z>),
  node((2, 0), $n$, name: <n>),
  edge(<m>, <z>, $2 / 3$, "->"),
  edge(<n>, <z>, $1 / 2$, "->"),
  edge(<m>, <m>, $1 / 3$, "->", bend: 130deg, loop-angle: 180deg),
  edge(<n>, <n>, $1 / 2$, "->", bend: 130deg, loop-angle: 0deg),
)

// Guarded fixed points in a complete extended metric space: on the left the
// iterates of a p-contraction from a seed at finite displacement converge
// inside the seed's galaxy; on the right the successor on (ℕ, {0, ∞}) jumps
// from galaxy to galaxy and has no fixed point.  Positions are physical
// lengths (y upwards), so the layout does not depend on the labels' widths.
#let lab(body) = text(size: 0.7em, fill: colors.gray, body)
#let pt-node(pos, label, name, fill: none) = node(
  pos,
  label,
  name: name,
  shape: circle,
  inset: 3pt,
  stroke: if fill == none { none } else { 0.8pt + colors.emerald.darken(20%) },
  fill: fill,
)
#let galaxy(..pts) = node(
  enclose: pts.pos(),
  inset: 7pt,
  fill: colors.gray.lighten(85%),
  stroke: 0.6pt + colors.gray,
  corner-radius: 1em,
)
#let banach-pic = diagram(
  axes: (ltr, btt),
  node-stroke: none,
  edge-stroke: 0.8pt,
  // the galaxy of the seed
  node(
    enclose: ((-20pt, -18pt), (325pt, 112pt)),
    fill: colors.emerald.lighten(92%),
    stroke: 0.6pt + colors.emerald,
    corner-radius: 1.4em,
  ),
  node((150pt, 96pt), lab[CextMet Y]),
  pt-node((20pt, 8pt), $y$, <y0>),
  pt-node((125pt, 60pt), $f(y)$, <y1>),
  pt-node((190pt, 18pt), $f^2 (y)$, <y2>),
  pt-node((240pt, 64pt), $f^3 (y)$, <y3>),
  pt-node((300pt, 36pt), $y^n$, <ys>, fill: colors.emerald.lighten(60%)),
  edge(<y0>, <y1>, lab[$d < oo$], "->"),
  edge(<y1>, <y2>, lab[$<= p d$], "->", label-side: right),
  edge(<y2>, <y3>, lab[$<= p^2 d$], "->", label-side: right),
  edge(<y3>, <ys>, "->", stroke: (dash: "dotted")),
)

// The interpretation at a glance.  Left, the bridge: each syntactic level is
// sent by ⟦−⟧ to its counterpart in CExtMet.  Right, the sensitivity picture:
// ⟦t⟧ is non-expansive for the scaled distance, i.e. r-Lipschitz in x :ʳ A.
#let blob(pts, label, pos) = (
  node(
    enclose: pts,
    inset: 9pt,
    fill: colors.emerald.lighten(92%),
    stroke: 0.6pt + colors.emerald,
    corner-radius: 1.2em,
  ),
  node(pos, label),
)
#let interp-pic = diagram(
  axes: (ltr, btt),
  node-stroke: none,
  edge-stroke: 0.8pt,
  // column headers
  node((70pt, 125pt), lab[syntax]),
  node((330pt, 125pt), lab[#cext]),
  // row 1: types
  node((70pt, 95pt), [type $A$], name: <s1>),
  node((330pt, 95pt), [object $⟦ A ⟧$], name: <m1>),
  // row 2: contexts
  node((70pt, 55pt), [context $Gamma, x tcols(r, s) A$], name: <s2>),
  node((330pt, 55pt), $⟦ Gamma ⟧ times.o r ⟦ A ⟧$, name: <m2>),
  node((330pt, 33pt), lab[]),
  // row 3: judgements
  node((70pt, 5pt), [judgement $Gamma, x tcols(r, s) A ⊢ t : B$], name: <s3>),
  node((330pt, 5pt), $⟦ t ⟧ : ⟦ Gamma ⟧ times.o r ⟦ A ⟧ -> ⟦ B ⟧$, name: <m3>),
  node((330pt, -18pt), lab[]),
  edge(<s1>, <m1>, lab[$⟦ - ⟧$], "->"),
  edge(<s2>, <m2>, lab[$⟦ - ⟧$], "->"),
  edge(<s3>, <m3>, lab[$⟦ - ⟧$], "->"),
  // the sensitivity picture
  pt-node((500pt, 80pt), $x$, <x>),
  pt-node((500pt, 25pt), $x'$, <x1>),
  edge(<x>, <x1>, lab[$r dot d$], "-", stroke: (dash: "dotted"), label-side: right),
  ..blob((<x>, <x1>), lab[$r ⟦ A ⟧$], (500pt, 122pt)),
  pt-node((640pt, 80pt), $t(x)$, <tx>),
  pt-node((640pt, 25pt), $t(x')$, <tx1>),
  edge(<tx>, <tx1>, lab[$<= r dot d$], "-", stroke: (dash: "dotted"), label-side: left),
  ..blob((<tx>, <tx1>), lab[$⟦ B ⟧$], (640pt, 122pt)),
  edge((528pt, 52pt), (610pt, 52pt), $⟦ t ⟧$, "->"),
  node((570pt, -24pt), lab[$r$-Lipschitz in $X$]),
)

// The title slide keeps the theme's 20pt so that it fits on one page.
#title-slide()

#set text(size: 23pt)



// =====================================================================
= Quantitative Linear Logic overview
// =====================================================================

// The algebra of [0, ∞]: a table polarity × (additive | multiplicative),
// conjunctive cells in blue and disjunctive cells in emerald.
#let mr-cols = (1.8fr, 1.4fr, 4.4fr, 2.8fr)

// `u := v` above `a op b`, the symbols aligned in three columns.
#let unit-op(u, v, op) = grid(
  columns: 3, column-gutter: 0.5em, row-gutter: 0.6em, align: center,
  u, $:=$, v,
  $a$, op, $b$,
)

// A multiplicative cell: the unit and the operation, and the convention at 0 · ∞.
#let mult-cell(op, conv) = grid(
  columns: (auto, 1fr), align: horizon + center,
  unit-op($bold(1)$, $1$, op), conv,
)

// An additive cell: the soft p-sum and, as p -> +oo, the hard lattice operation.
#let soft-hard-cols = (4.6em, 4.2em, 4.6em)
#let soft-hard(u, v, soft-op, hard-op) = align(center, grid(
  columns: soft-hard-cols, align: center + horizon,
  unit-op(u, v, soft-op),
  diagram(edge((0pt, 0pt), (3.4em, 0pt), "->", label: text(size: 0.7em, $p -> +oo$))),
  unit-op(u, v, hard-op),
))

#slide(title: [The multiplicative $p$-reals])[
  #set text(size: 18pt)
  $[0, oo]_(plus.o^p, times.o)$ with the following algebraic structure on $([0, oo], <=)$:
  // "distributes over", from the multiplicative to the additive header
  #grid(
    columns: mr-cols,
    [], [],
    grid.cell(colspan: 2, align(center, diagram(
      axes: (ltr, btt),
      edge((60pt, 0pt), (-80pt, 0pt), "->", bend: -28deg, stroke: 1.2pt,
        label: text(size: 0.6em, weight: "bold")[distributes over], label-side: right),
    ))),
  )
  #v(-0.6em)
  #table(
    columns: mr-cols,
    align: center + horizon,
    inset: (x: 0.5em, y: 0.55em),
    stroke: (x, y) => if x == 0 and y == 0 { (right: 0.8pt, bottom: 0.8pt) } else { 0.8pt },
    [], [*polarity*], [*additive*], [*multiplicative*],
    // the duality, with the de Morgan arrow on the right border, between the rows
    table.cell(rowspan: 2, align: left + horizon, box(width: 100%, {
      place(right + horizon, dx: 1.3em, stack(
        dir: ltr, spacing: 0.15em,
        rotate(-90deg, reflow: true, text(size: 0.6em, weight: "medium")[de Morgan]),
        diagram(axes: (ltr, btt), edge((0pt, 30pt), (0pt, -30pt), "<->", bend: -110deg, stroke: 1.2pt)),
      ))
      [*duality* \ $a^* := 1 \/ a$]
    })),
    [*positive*],
    table.cell(fill: colors.emerald.lighten(85%), soft-hard($bot$, $0$, $plus.o^p$, $or$)),
    table.cell(fill: colors.royalblue.lighten(85%), mult-cell($times.o$, $oo times.o 0 := 0$)),
    [*negative*],
    table.cell(fill: colors.royalblue.lighten(85%), soft-hard($top$, $oo$, $plus.o^(-p)$, $and$)),
    table.cell(fill: colors.emerald.lighten(85%), mult-cell($times.o^*$, $oo times.o^* 0 := oo$)),
  )
  #v(-1.1em)
  #grid(
    columns: mr-cols,
    [], [],
    align(center, grid(
      columns: soft-hard-cols, align: center,
      $underbrace(#box(width: 4.2em), #strong[soft])$, [],
      $underbrace(#box(width: 4.2em), #strong[hard])$,
    )),
    [],
  )
  #v(-0.6em)
  where
  #pad(left: 1.2em)[
    $times.o$ and $times.o^*$ are multiplication (#text(fill: colors.royalblue, weight: "bold")[conjunctive] and #text(fill: colors.emerald, weight: "bold")[disjunctive]), \
    $plus.o^p$ is $p$-sum: $a plus.o^p b = (a^p plus.o b^p)^(1 \/ p)$, $0 < p <= oo$, \
    $plus.o^(-p)$ is harmonic $p$-sum: $a plus.o^(-p) b = (a^* plus.o^p b^*)^*$,
  ]
]

== Syntax and softness

#set text(size: 19pt)
  $
    φ, ψ ::= & t | top | bot | t =_A u | φ times.o ψ | φ times.o^* ψ | φ arrow.double ψ | r φ | φ^* \
           | & φ or^s ψ | φ and^s ψ | fa(s) (x tilde m). φ | ex(s) (x tilde m). φ 
  $
  $
    Δ | Ψ & ent(p) φ
  $
- Every variable carries a *sensitivity* and a *softness*, $x tcols(r, s) A$; a quantifier records the softness of the variable it binds
- The *softness* $s$ grades the soft connectives, interpreted by the $s$-sums:
  $
    ⟦ φ or^s ψ ⟧ &= ⟦ φ ⟧ plus.o^s ⟦ ψ ⟧ & quad ⟦ φ and^s ψ ⟧ &= ⟦ φ ⟧ plus.o^(-s) ⟦ ψ ⟧ \
                &= (⟦ φ ⟧^s plus.o ⟦ ψ ⟧^s)^(1/s)     &  quad  &= (⟦ φ ⟧^* plus.o^s ⟦ ψ )^*⟧^* 
  
  $

#remark[
  $s = oo$ is *hard*, $or^oo = max$ and $and^oo = min$; a smaller $s$ is *softer*
]

== Soft quantifiers: $s$-means

#set text(size: 19pt)
Over $exists^s$ is the $s$-mean and $forall^s$ the harmonic $s$-mean:
  $
    ex(s) (x tilde m). φ = (integral φ(x)^s dif m(x))^(1 \/ s) quad quad quad
    fa(s) (x tilde m). φ = (integral φ(x)^(-s) dif m(x))^(-1 \/ s)
  $
Facts:
- Quantifiers are dual $(fa(s) (x tilde m). φ)^* = ex(s) (x tilde m). φ)$
- $s = 1$ gives the expectation $EE_(x tilde m) [φ]$
- As $s -> oo$ they become the hard quantifiers $inf$ and $sup$



// =====================================================================
// Introduction
// =====================================================================

== Quantitative Reasoning
$
  x attach(=, br: epsilon) y " with " epsilon in bb(I) subset RR
$
- Reasoning about distances of programs
  - Sensitivity of program outputs to inputs
  - convergence
- Quantitative linear logic

#remark[
  🔓 Framework for expressing quantitative logic
]

== Example: Probabilistic Bisimilarity Distance

#set text(size: 20pt)
#align(center, markov)

- A Markov process comprises states $S$, labels $L$ and
  $ o : S -> L quad quad quad t : S -> cal(D) S $
- Bisimilarity distance: the least solution of
  $ d(s, s') = cases(cal(K)_d (t(s), t(s')) & " if " I(s) eq I(s'),infinity & "otherwise") $

- If $m$ and $n$ have the same label then
  $ d(m, n) <= 1 / 4  " read as " m attach(=, br:1/4) n $

== Quantitative Logic

- *Quantitative logic can be constructed in Extended Metric Spaces (EMet)*  
  
  with $(X, d_x : X times X -> [0, oo])$ 
  $
    d_X (x, y) &= 0 "iff" x = y \
    d_X  (x, y) &= d_X (y, x) \
    d_X (x, z) &<= d_X (x, y) + d_X (y, z)
  $
  
  - transitivity is
    $ x =_epsilon y, space y =_(epsilon') z tack.r x =_(epsilon'') z quad quad "for" epsilon'' >= epsilon + epsilon' $

  #remark[
    We write $d(x, x)$ for $d_X (x, y)$ when $X$ is implicit.

    🔓 Multiplicative Reals
  ]

== Quantitative Linear Logic (FQLL) in EMet

- Truth values in $Omega :=  overline(RR)_+ = [0, oo]$
- $Omega$ is `Prop`
- Interpretation of $x = y$ is
  $
    d_Omega : Omega arrow Omega arrow overline(RR)_+ \
    d(x,y)_Omega  = e^(-d(x, y))
  $
- So $infinity$ is $top$, $0$ is $bot$
- $phi tack.r psi$ means $phi <= psi$

#remark[
  🔓 Expressing Prop domain
]

== Two Basic Observations

#set text(size: 20pt)
- Transitivity
  $ x = y, space y = z tack.r x = z $
- Suggests comma as product ($times.o$):
  $
  e^(-d(x, y)) dot e^(-d(y, z)) <= e^(-d(x, z))
  $
#pause
- *Sensitivity* of terms needs to be tracked:
  $
    d(2x, 2y) = 2 d(x, y)
  $
- In logic:
  $ x = y tack.r.not 2x = 2y quad "but" quad 2(x = y) tack.r 2x = 2y $

== Principles of the logic

- Interpreting FOL-QLL in the category *EMet*
- Elimination for equality (Leibniz equality)
- Guarded recursion for terms and propositions:
  $
    p phi tack.r phi arrow.r.double dot tack.r phi quad quad "for" p < 1
  $
- Induction as an inference rule or an axiom schema
  #align(center, prooftree(rule(
    name: [$"(rec"_NN)$],
    $Gamma ⊢ phi(0)$,
    $Gamma, phi(n) ⊢ phi(S(n))$,
    $Gamma ⊢ forall n. thin phi(n)$,
  )))

- Consequences:
  - Equality is a congruence
  - Reasoning by couplings

== Overview

- The category #cext
- An internal $lambda$-calculus in #cext
- FQLL has internal logic
- Examples
- Conclusion

// =====================================================================
= The category #cext
// =====================================================================

== First, the Category #ext

- Objects: Extended metric spaces i.e $(X, d_X)$ with $X subset.eq overline(RR_+)$
- Morphisms: Non-expansive maps
  $ d_Y (f(x), f(y)) <= d_X (x, y) $
- Monoidal structure
  $ d_(X times.o Y) ((x, y), (x', y')) = d_X (x, x') + d_Y (y, y') $
- Monoidal closed
  $
    X multimap Y & = { f : X -> Y | f "non-expansive" } \
    d_(X multimap Y) (f, g) & = sup { d_Y (f(x), g(x)) | x in X }
  $

#remark[
  🔓 QLL $[0, oo]$, $=_epsilon$, \~ Leibniz equality, Simple Typed $lambda$-Calculus
]

== Example of #ext

The simplest example: the *$oo$-discrete metric* on any set $X$
#align(center, box(stroke: 0.6pt, inset: 8pt, $
  d(x, y) = cases(0 & "if" x = y, oo & "if" x != y)
$))
For example, take $X = {a, b, c}$. Its distance matrix is:
#align(center, table(
  columns: 4,
  align: center + horizon,
  inset: (x: 10pt, y: 5pt),
  stroke: (x, y) => (
    left: if x == 1 { 0.6pt },
    bottom: if y == 0 { 0.6pt },
  ),
  $d$, $a$, $b$, $c$,
  $a$, $0$, $oo$, $oo$,
  $b$, $oo$, $0$, $oo$,
  $c$, $oo$, $oo$, $0$,
))

== The category #cext

- Objects: complete #ext objects
Complete: every Cauchy sequence converges, i.e.
$
  "if" d(x_m, x_n) -> 0 "as" m, n -> oo "then" x_n -> x "for some" x
$
- Morphisms: non-expansive maps

#remark[
  🔓 Banach fixpoint, recursion, induction
]

== Objects of #cext

#set text(size: 20pt)
// One card per object: its name above its distance, small and light gray.
#let obj-cell(name, dist) = block(
  width: 100%,
  height: 100%,
  inset: 0.5em,
  radius: 4pt,
  fill: colors.emerald.lighten(92%),
  stroke: 0.6pt + colors.emerald.lighten(40%),
  align(center + horizon, stack(
    spacing: 0.6em,
    [*#name*],
    // a box keeps the formula on one line; the scale shrinks it to the card's width
    layout(size => {
      let f = box(text(size: 0.7em, fill: colors.gray.lighten(20%), $d(a, b) = dist$))
      let w = measure(f).width
      if w > size.width { scale(size.width / w * 100%, reflow: true, f) } else { f }
    }),
  )),
)
#grid(
  columns: (1fr, 1fr, 1fr),
  rows: (4.6em, 4.6em, 4.6em),
  gutter: 0.6em,
  obj-cell($RR$, $|a - b|$),
  obj-cell($NN$, $display(cases(0 & "if" a = b, oo & "otherwise"))$),
  obj-cell($bold(1)$, $0$),
  obj-cell($r dot X$, $r dot d_X (a, b)$),
  obj-cell($X \& Y$, $max(d_X (a_1, b_1), d_Y (a_2, b_2))$),
  obj-cell($X times.o Y$, $d_X (a_1, b_1) + d_Y (a_2, b_2)$),
  obj-cell($X + Y$, $display(cases(d_X "or" d_Y , oo ))$),
  obj-cell($X multimap Y$, $sup_(x in X) d_Y (a(x), b(x))$),
  obj-cell($cal(W) X$, "Wasserstein distance"),
)

== Scaling extended metric spaces

#set text(size: 20pt)
- Scaling of $X$ by $r in [0, oo]$, with $r dot oo = oo$ for $r > 0$ and $0 dot oo = 0$
  $ d_(X^r) (x, x') = r dot d_X (x, x') $
- A non-expansive map $r X -> Y$ is exactly an $r$-Lipschitz map $X -> Y$
#pause
#proposition(title: [Scaling properies])[
  For all $r, s in [0, oo]$,
  $ r (A times.o B) tilde.equiv r A times.o r B, quad (r s) A tilde.equiv r (s A), quad r bold(1) tilde.equiv bold(1), quad r (A + B) tilde.equiv r A + r B space (r > 0) $
]

== Guarded recursion

#set text(size: 19pt)
#align(center, banach-pic)


== Guarded recursion: Banach in the ∞ setting

#theorem(title: [Banach, extended])[
  Let $Y$ be complete,
  - given $p < 1$
  - $f : p Y -> Y$
  - and $y_0$ with $d(y_0, f(y_0)) < oo$,
  Then $f$ has a unique fixed point named $y_0$.
]

#remark[
  We can not recurse on $X + Y$ since $d_(X+Y)(a,b) = oo$ when $a ∈ X$ and $b ∈ Y$.
]

== Guarded recursion: parametric fixed points

#set text(size: 19pt)
#theorem(title: [Parametric fixed points])[
  - $F : X times.o p Y -> Y$
  - non-expansive (coercion) map $f : X -> Y$
  - and $d(f(x), F(x, f(x))) < oo$
  
  the map $"fp"(F) : X -> (1 - p) Y$ with
  $ "fp"(F)(x) = "fix"(F(x, -)) "from" f(x) $
  is non-expansive.
]

// =====================================================================
= Metric Probability Space via Wasserstein Monad
// =====================================================================


== The Wasserstein monad $cal(W)X$
Let $mu$ and $eta$ be Radon probability measure on $X$ of finite first moment.
The Wasserstein distance is given by:
$
  cal(W) & : X arrow.r X arrow.r [0, oo]  \
  cal(W)(mu,eta) & = inf_(gamma in C(mu,eta)) integral_(x,x' in X times X) d(x,x') space "d"gamma(x,x') \
            & = inf_(gamma in C(mu,eta)) EE_(x,x' ~gamma) d(x,x')
$
We assign to $cal(W)X$ (probability monad) the Wasserstein metric. 

== Monad $cal(W)X$ Operators

#set text(size: 20pt)
- Return: the Dirac measure
  $
    delta_X : X -> cal(W) X, quad quad delta_X (x)(A) = cases(1 & "if" x in A, 0 & "otherwise")
  $
- Bind: for a probability kernel $f : X -> cal(W) Y$
  #align(center)[`(μ >>= f)(B) =` $display(integral_(x ∈ X) f(x)(B) dif mu(x))$]
- Monad laws
  - `δ(x) >>= f ≡ f(x)`
  - `μ >>= δ ≡ μ`
  - `(μ >>= f) >>= g ≡ μ >>= (x |-> f(x) >>= g)`



== Interpolative barycentric algebras


A (complete) interpolative barycentric algebra in #cext:

Choice operator: $amp.inv_p : forall X, p X times.o (1 - p) X -> X$

$
  x amp.inv_p x & = x & "(idem)" \
  x amp.inv_p y & = y amp.inv_(1 - p) x & "(comm)" \
  (x amp.inv_p y) amp.inv_q z & = x amp.inv_(p q) (y amp.inv_((q - p q) / (1 - p q)) z) quad & "(assoc)"
$

#remark[
  with $p, q in [0,1]$
]

#slide(title: [Interpolative barycentric algebras])[

]

// =====================================================================
= A calculus for #cext
// =====================================================================

== Types and their interpretation

#set text(size: 19pt)
- Judgement
$
  Γ, x tcols(r, s) A tack t : B quad quad Gamma ⧺ Gamma' quad quad c Gamma
$
- Types

$
  A, B ::= & NN | "unit" | A times B | A + B | A attach(times.o, bl: r, br: s) B | A multimap_r B | cal(W) A | text(weight: "bold", fill: #colors.emerald, prop)  
$

- Terms
  #term-syntax

== The interpretation idea

#set text(size: 19pt)

#align(center, interp-pic)

== The interpretation

- Type interpretation:
  #sem-types
- Terms interpretation:
  $
    ⟦ Gamma ⊢ t : A ⟧ : ⟦ Gamma ⟧ -> ⟦ A ⟧
  $

== Typing rule: core

#set text(size: 19pt)
#align(center, rule-set(column-gutter: 2.5em, row-gutter: 2.4em, r-var, r-abs, r-app, r-tensor, r-letin))

== Operations on contexts Γ

- Sum of contexts
  $
    (Gamma, x tcols(r, s) A) ⧺ (Gamma', x tcols(r', s') A) & = (Gamma ⧺ Gamma'), x tcols(r + r', s plus.o^* s') A \
    emptyctx ⧺ emptyctx & = emptyctx
  $
- Scaling of contexts
  $
    c (Gamma, x tcols(r, s) A) & = c Gamma, x tcols(c dot r, s) A \
    c emptyctx & = emptyctx
  $
- Sensitivities add and scale; softnesses compose by harmonic sum $1 / (s plus.o^* s') = 1 / s + 1 / s'$ (unit $oo$) and ignore scaling
- $⟦ Gamma ⧺ Gamma' ⟧ -> ⟦ Gamma ⟧ times.o ⟦ Gamma' ⟧$ and $⟦ c Gamma ⟧ -> c ⟦ Gamma ⟧$ are identities on the common carrier

== Typing rules: probability and recursion

#set text(size: 19pt)
#align(center, rule-set(column-gutter: 2.5em, row-gutter: 2.4em, r-dirac, r-probchoice, r-letalg, r-fix))

== Typing rules: products, sums and numbers

#set text(size: 17pt)
#align(center, rule-set(column-gutter: 2em, row-gutter: 2.2em, r-pair, r-proj, r-inj, r-case, r-zero, r-succ, r-rec))

== Semantics

#set text(size: 17pt)
#theorem(title: [Soundness])[
  Every derivation of $Gamma ⊢ t : A$ denotes a non-expansive map $⟦ t ⟧ : ⟦ Gamma ⟧ -> ⟦ A ⟧$, by recursion on the derivation.
]

== Example: programming with processes

#set text(size: 19pt)
#align(center, markov)

- Assume a type of processes, an observation paired with a next-state distribution
  $ PP tilde.equiv A attach(times.o, bl: 1, br: 1) cal(W) PP $
- Define $m$ as
  $ m ≜ "fix" m. (a, space delta m amp.inv_(1 \/ 3) delta z) $
- Using
  $ z tcols(2 / 3, s) PP, space m tcols(1 / 3, s) PP ⊢ (a, space delta m amp.inv_(1 \/ 3) delta z) : PP $
  so that (FIX) with $r = 1 / 3$ gives $z tcols(1, s) PP ⊢ m : PP$: the process $m$ is non-expansive in $z$

// =====================================================================
= The internal quantitatice logic
// =====================================================================

== Prop in a glance

#set text(size: 18pt)
- A commutative quantale with an involution
  $ prop = ([0, oo], <=, times.o, 1, (-)^*)$
- Where
  $
    a times.o b = a b quad (0 times.o oo = 0) quad quad a^* = 1 / a quad (0^* = oo) quad quad
    a multimap b = a^* times.o^* b
  $
- $bot = 0$, $top = oo$, and $a$ is *true* iff $a >= 1$

#pause

#remark[
We can also define
  $
    prop_plus.o = ([0, oo], <=, times.o, 0, (-)^*)
  $
  with $d_prop_plus.o (a, b) = |log a - log b|$ and Napierian duality $prop_plus.o ⟷ prop$
]

== QLL sensitivity

We need to track sensitivity for 

== Typing rule for Prop operator

#set text(size: 17pt)
Since $prop$ is an object of #cext, predicates track sensitivity exactly like terms; a quantifier binds $x tcols(r, s) A$ and records its softness $s$.
#v(0.3em)
#align(center, rule-set(column-gutter: 2.2em, row-gutter: 2em, prop-eq, prop-tens, prop-imp, prop-scale, prop-dual, prop-sum, prop-all, prop-ex))

== Soft quantifiers are means

#set text(size: 19pt)
- The quantifiers are morphisms $exists^s_A, forall^s_A : r cal(W) A times.o (r A multimap prop) -> prop$, for $r, s in [0, oo]$
  $
    ex(s) (x tilde m). phi = (integral phi(x)^s dif m(x))^(1 \/ s) quad quad quad
    fa(s) (x tilde m). phi = (integral phi(x)^(-s) dif m(x))^(-1 \/ s)
  $
- $s$ is the softness of the bound variable $x tcols(r, s) A$; its sensitivity $r$ is not recorded, it is absorbed by $r cal(W) A = cal(W)(r A)$
- $s = oo$: $sup$ and $inf$ over the support of $m$, the hard quantifiers
- $s = 1$: the expectation $EE_(x tilde m) [phi]$ and its harmonic mean

== The graded entailment

#align(center, box(stroke: .5pt, inset: 6pt)[$ Delta thin | thin Psi ent(p) phi $])

== Connectives and quantifiers

#align(center, rule-set(column-gutter: 2.2em, row-gutter: 2em, l-tensR, l-tensL, l-impR, l-impL, l-eqI, l-allI, l-exE))
