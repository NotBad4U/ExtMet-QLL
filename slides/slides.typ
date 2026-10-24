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
#import "../paper/common.typ": emptyctx, tcol, prop, ent, psum, fa, ex, rule-set
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
  node((70pt, 55pt), [context $Gamma, x tcol(r) A$], name: <s2>),
  node((330pt, 55pt), $⟦ Gamma ⟧ times.o r ⟦ A ⟧$, name: <m2>),
  node((330pt, 33pt), lab[]),
  // row 3: judgements
  node((70pt, 5pt), [judgement $Gamma, x tcol(r) A ⊢ t : B$], name: <s3>),
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
  ]

== Quantitative Linear Logic (FQLL) in EMet

- Truth values in $Omega :=  overline(RR)_+ = [0, oo]$ i.e. `Prop`
- Interpretation of $x = y$ is $d(x,y)_Omega = e^(-d(x, y))$
- So $infinity$ is $top$, $0$ is $bot$
- $phi tack.r psi$ means $phi <= psi$

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

== The category #cext

- Objects: *Complete* extended metric spaces
- Morphisms: Non-expansive maps
  $ d_Y (f(x), f(y)) <= d_X (x, y) $
- Monoidal structure
  $ d_(X times.o Y) ((x, y), (x', y')) = d_X (x, x') + d_Y (y, y') $
- Monoidal closed
  $
    X multimap Y & = { f : X -> Y | f "non-expansive" } \
    d_(X multimap Y) (f, g) & = sup { d_Y (f(x), g(x)) | x in X }
  $

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
= Probability via Wasserstein Monad
// =====================================================================


== The Wasserstein monad

- Let
  $ cal(W)_p X = { mu | mu "Radon probability measure on" X }, quad p >= 1 $
  with the Wasserstein distance $W_p$
- Includes Dirac measures, finite measures, the uniform measure on $[0, 1]$, …
- Unit $delta : X -> cal(W) X$ (Dirac), join by expectation, pushforward on maps
- Scaling law: $cal(W)(r X) = r thin cal(W) X$ #rocq("wdist_scale")
- Convex combination of measures, $mu amp.inv_p nu = p mu + (1 - p) nu$,
  $ amp.inv_p : p dot cal(W) X times.o (1 - p) dot cal(W) X -> cal(W) X $

== Wasserstein distance via transport plans

#set text(size: 18pt)
- A *plan* from $mu$ to $nu$ is a probability kernel $k$ with $nu = integral k(x) thin dif mu(x)$; its cost is an iterated integral, no product measure needed:
  $ "cost"_p (mu, k) = (integral_mu integral_(k(x)) d(x, y)^p)^(1 \/ p), quad quad W_p^(->) (mu, nu) = inf_(k "plan") "cost"_p (mu, k) $
- Plans compose by Kleisli composition, which gives the triangle inequality; $W_p$ symmetrises the two directions
- Couplings $pi$ on $X times X$ with marginals $mu, nu$ give the usual $W_p (mu, nu) = inf_pi (integral d^p dif pi)^(1 \/ p)$
#theorem[
  On standard Borel spaces the plan and coupling definitions agree, by disintegration.
  #rocq-tag("wassE")
]

== Interpolative barycentric algebras

#set text(size: 19pt)
#definition[
  A (complete) interpolative barycentric algebra in #cext is a complete $X$ with non-expansive
  $amp.inv_p : p X times.o (1 - p) X -> X$, $p in (0, 1)$, such that
  $
    x amp.inv_p x & = x & "(idem)" \
    x amp.inv_p y & = y amp.inv_(1 - p) x & "(comm)" \
    (x amp.inv_p y) amp.inv_q z & = x amp.inv_(p q) (y amp.inv_((q - p q) / (1 - p q)) z) quad & "(assoc)"
  $
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
  Γ tack M attach(:, tr: r) N
$
- Types
  #types-syntax
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
    (Gamma, x tcol(r) A) ⧺ (Gamma', x tcol(s) A) & = (Gamma ⧺ Gamma'), x tcol(r + s) A \
    emptyctx ⧺ emptyctx & = emptyctx
  $
- Scaling of contexts
  $
    c (Gamma, x tcol(r) A) & = c Gamma, x tcol(c dot r) A \
    c emptyctx & = emptyctx
  $
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
  $ z tcol(2 / 3) PP, space m tcol(1 / 3) PP ⊢ (a, space delta m amp.inv_(1 \/ 3) delta z) : PP $
  so that (FIX) with $r = 1 / 3$ gives $z tcol(1) PP ⊢ m : PP$: the process $m$ is non-expansive in $z$

// =====================================================================
= The logic
// =====================================================================

== Prop in a glance

#set text(size: 18pt)
- A commutative quantale with an involution
  $ prop = ([0, oo], <=, times.o, 1, (-)^*) $
- Where
  $
    a times.o b = a b quad (0 times.o oo = 0) quad quad a^* = 1 / a quad (0^* = oo) quad quad
    a multimap b = a^* times.o^* b = sup { c | a times.o c <= b }
  $
- $bot = 0$, $top = oo$, and $a$ is *true* iff $a >= 1$

#remark[
  Via $-log$, this is the extended Lawvere quantale $([-oo, oo], >=, +, 0)$
]

// #pause
// - Log metric $d_prop (a, b) = |log a - log b|$: the operations are non-expansive!
//   $
//     times.o, multimap : prop times.o prop -> prop quad quad (-)^r : r dot prop -> prop quad (r in [0, oo]) quad quad (-)^* "an isometry"
//   $
// - Soft sums for $s in [0, oo]$, with max and min at $s = oo$:
//   $ a plus.o^s b = (a^s + b^s)^(1 \/ s), quad quad a plus.o^(-s) b = (a^(-s) + b^(-s))^(-1 \/ s) $

== Predicates as terms

#set text(size: 17pt)
Since $prop$ is an object of #cext, predicates track sensitivity exactly like terms.
#v(0.3em)
#align(center, rule-set(column-gutter: 2.2em, row-gutter: 2em, prop-eq, prop-tens, prop-imp, prop-scale, prop-dual, prop-sum, prop-all, prop-ex))

== Interpretation of predicates

#set text(size: 18pt)
- Equality is the distance, pushed through $e^(-(-))$:
  $ ⟦ t =_A u ⟧ ≜ e^(-d_(⟦ A ⟧)) ∘ (⟦ t ⟧ times.o ⟦ u ⟧) $
#align(center, diagram(
  spacing: 3.6em,
  node((0, 0), $⟦ A ⟧ times.o ⟦ A ⟧$),
  node((1, 0), $([0, oo], |a - b|)$),
  node((2, 0), $prop$),
  edge((0, 0), (1, 0), $d_(⟦ A ⟧)$, "->"),
  edge((1, 0), (2, 0), $e^(-(-))$, "->"),
  edge((0, 0), (2, 0), $e^(-d_(⟦ A ⟧))$, "->", bend: 42deg),
))
#v(0.4em)
- $⟦ phi times.o psi ⟧$, $⟦ phi multimap psi ⟧$, $⟦ phi^* ⟧$ pointwise, and $⟦ r phi ⟧ = ⟦ phi ⟧^r$
- The quantifiers are means over the reference measure $m : cal(W) A$:
  $
    ⟦ ex(s) (x tilde m). phi ⟧ & = (integral ⟦ phi ⟧ (gamma, x)^s dif ⟦ m ⟧(x))^(1 \/ s) quad quad
    ⟦ fa(s) (x tilde m). phi ⟧ & = (integral ⟦ phi ⟧ (gamma, x)^(-s) dif ⟦ m ⟧(x))^(-1 \/ s)
  $

== Soft quantifiers are means

#set text(size: 19pt)
- The quantifiers are morphisms $exists^s_A, forall^s_A : cal(W) A times.o (A multimap prop) -> prop$, for $s in [0, oo]$
  $
    ex(s) (x tilde m). phi = (integral phi(x)^s dif m(x))^(1 \/ s) quad quad quad
    fa(s) (x tilde m). phi = (integral phi(x)^(-s) dif m(x))^(-1 \/ s)
  $
- $s = oo$: $sup$ and $inf$ over the support of $m$, the hard quantifiers
- $s = 1$: the expectation $EE_(x tilde m) [phi]$ and its harmonic mean
#pause
- Laws of the means used by the logic: constants, monotonicity, change of variables along a pushforward,
  Fubini for the join, and homogeneity #rocq("wmeans")
  $ ex(s) (x tilde m). (a times.o phi) = a times.o ex(s) (x tilde m). phi $
- De Morgan: $(fa(s) (x tilde m). phi)^* = ex(s) (x tilde m). phi^*$ #rocq("psem_dual_forall", "psem_dual_exists")

== The graded entailment

#set text(size: 16pt)
#align(center, box(stroke: .5pt, inset: 6pt)[$ Delta thin | thin Psi ent(p) phi $])
- $Delta$ a discrete typing context, $Psi$ a list of predicates, $p in [0, oo]$ the *softness*
- Valid under a reference measure $mu$ on $⟦ Delta ⟧$ when the harmonic $p$-mean of the implication is true:
  $ 1 <= fa(p) (gamma tilde mu). ((times.o.big Psi) multimap phi) $
- $p = oo$ is the hard entailment on the support of $mu$, smaller $p$ is softer
- Grades form the monoid $([0, oo], plus.o^*, oo)$ with the harmonic sum $1 / (p plus.o^* q) = 1 / p + 1 / q$: Hölder conjugacy
#v(0.3em)
#align(center, rule-set(column-gutter: 2.2em, row-gutter: 2em, l-ass, l-cut, l-relax, l-weak))

== Connectives and quantifiers

#set text(size: 16pt)
Cut-like rules accumulate softness by harmonic sum; introducing $multimap$ leaves the grade untouched.
#v(0.3em)
#align(center, rule-set(column-gutter: 2.2em, row-gutter: 2em, l-tensR, l-tensL, l-impR, l-impL, l-eqI, l-allI, l-exE))

== Equality

#set text(size: 18pt)
#theorem(title: [Equality is an equivalence])[
  For $⟦ t =_A u ⟧ = e^(-d(⟦ t ⟧, ⟦ u ⟧))$:
  - reflexive, $t =_A t$ is $1$; symmetric; transitive,
    $(t =_A u) times.o (u =_A v) ⊑ (t =_A v)$ is the triangle inequality
  - true iff $⟦ t ⟧ = ⟦ u ⟧$, and $=_A : A times.o A -> prop$ is non-expansive
  - substitutive: for $g : A -> prop$ non-expansive for the log metric,
    $ (x =_A y) times.o g(x) ⊑ g(y) $
  #rocq-tag("peq_refl", "peq_sym", "peq_trans", "peq_trueP", "peq_edist_le", "peq_subst")
]

== Quantifiers are graded adjoints to reindexing

#set text(size: 18pt)
- Predicates on $X$ form a $prop$-enriched category: the hom at grade $s$ under $mu : cal(W) X$ is
  $ [phi, psi]^s_mu ≜ fa(s) (x tilde mu). (phi(x) multimap psi(x)), $
  whose truth is the validity of $phi ent(s) psi$
- Along $pi : X times Y -> X$: reindexing $pi^* phi = phi ∘ pi$, and for a kernel $m : X multimap cal(W) Y$
  $ exists^s_m psi (x) = ex(s) (y tilde m(x)). psi(x, y), quad quad forall^s_m psi (x) = fa(s) (y tilde m(x)). psi(x, y) $
  with the kernel product $mu ⋈ m$ as reference measure on $X times Y$
#theorem(title: [$exists^s ⊣ pi^* ⊣ forall^s$ at every grade $s$])[
  $ [exists^s_m psi, phi]_mu = [psi, pi^* phi]_(mu ⋈ m) quad quad quad [phi, forall^s_m psi]_mu = [pi^* phi, psi]_(mu ⋈ m) $
  #rocq-tag("qexists_adj", "qforall_adj")
]

#slide(title: [Consequences of the adjunctions], composer: (3fr, 2fr))[
  #set text(size: 17pt)
  - The rules ($forall^s$-I) and ($exists^s$-E) are invertible, with unit and counit
    $ psi ent(s) pi^* exists^s psi quad quad quad pi^* forall^s psi ent(s) psi $
  - Frobenius reciprocity, the homogeneity of the means
    $ exists^s (psi times.o pi^* phi) = exists^s psi times.o phi quad quad quad forall^s (pi^* phi multimap psi) = phi multimap forall^s psi $
  - De Morgan: each quantifier is the dual of the other
    $ (forall^s psi)^* = exists^s psi^* $
  #rocq("qforall_I", "qexists_E", "qexists_frobenius", "qforall_imp", "qforall_dual")
][
  #set text(size: 17pt)
  #align(center, diagram(
    spacing: (3.2em, 2.6em),
    node((0, 0), $X' times Y$),
    node((1, 0), $X times Y$),
    node((0, 1), $X'$),
    node((1, 1), $X$),
    edge((0, 0), (1, 0), $f times "id"$, "->"),
    edge((0, 0), (0, 1), $pi'$, "->", label-side: left),
    edge((1, 0), (1, 1), $pi$, "->"),
    edge((0, 1), (1, 1), $f$, "->", label-side: right),
  ))
  - Beck–Chevalley for a base change $f : X' -> X$, on the nose:
    $ f^* ∘ exists^s_m = exists^s_(m ∘ f) ∘ (f times "id")^* $
    #rocq("qexists_bc", "qforall_bc")
]

// =====================================================================
= Examples
// =====================================================================

// == Example of equality

// #set text(size: 19pt)
// #align(center, markov)
// $
//   m & = (a, space delta m amp.inv_(1 \/ 3) (delta z amp.inv_(1 \/ 4) delta z)) \
//   n & = (a, space delta n amp.inv_(1 \/ 3) (delta n amp.inv_(1 \/ 4) delta z))
// $
// - Will show
//   $ 1 / 4 (z = n) ⊑ (m = n), quad "i.e." quad d(m, n) <= 1 / 4 dot d(z, n) $
// - In #cmet the right-hand side is bounded by $1$; in #cext it stays a bound *relative* to $z$

// == Example of equality

// #set text(size: 17pt)
// - *Unfolding.* $"fix" x. t$ is a fixed point of $t$, so $m$ and $n$ are their right-hand sides #rocq("sem_fixP")
// - *Congruence.* Comparing the two pairs componentwise, with $delta z = delta z amp.inv_(1 \/ 4) delta z$:
//   $ 1 / 3 (m = n) times.o 2 / 3 (1 / 4 (z = n) times.o 3 / 4 (z = z)) ⊑ (m = n) $
//   and since $(z = z) = 1$ and $r(s phi) = (r s) phi$,
//   $ 1 / 3 (m = n) times.o 1 / 6 (z = n) ⊑ (m = n), quad "i.e." quad d(m, n) <= 1 / 3 d(m, n) + 1 / 6 d(z, n) $
// #pause
// - *Banach estimate.* If $a = f(a)$ and $b = g(b)$ are in the same galaxy and $f$ is an $r$-contraction, then
//   $(1 - r) dot d(a, b) <= d(f(b), g(b))$ #rocq("fixed_point_edist_le")
// - With $r = 1 / 3$: $thin 2 / 3 d(m, n) <= 1 / 6 d(z, n)$, that is $1 / 4 (z = n) ⊑ (m = n)$ #h(1fr) $square$
// - #remark[The last step is the semantic counterpart of guarded recursion for propositions: it needs $d(m, n) < oo$.]

// == Example: neural networks as terms

// #set text(size: 18pt)
// - Any object of #cext is a base type; write $RR^n$ with its $ell_2$ metric. A network is built from
//   constants whose sensitivity is their *Lipschitz constant*:
//   $
//     "aff"_(W, b) : RR^n attach(multimap, br: ||W||) RR^m quad quad quad
//     "relu" : RR^m attach(multimap, br: 1) RR^m quad quad quad
//     sigma : RR attach(multimap, br: 1 \/ 4) RR
//   $
// - Composition *multiplies* sensitivities, by (APP):
// #let comp-deriv = prooftree(rule(
//   name: [(ABS)],
//   rule(
//     name: [(APP)],
//     $emptyctx ⊢ g : B attach(multimap, br: s) C$,
//     rule(
//       name: [(APP)],
//       $emptyctx ⊢ f : A attach(multimap, br: r) B$,
//       rule(name: [(VAR)], $x tcol(1) A ⊢ x : A$),
//       $x tcol(r) A ⊢ f space x : B$,
//     ),
//     $x tcol(s r) A ⊢ g space (f space x) : C$,
//   ),
//   $emptyctx ⊢ lambda x. g space (f space x) : A attach(multimap, br: s r) C$,
// ))
// #align(center, text(size: 15pt, comp-deriv))
// - A two-layer perceptron $cal(N) := lambda x. "aff"_(W_2, b_2) ("relu" ("aff"_(W_1, b_1) space x))$ is typed
//   $ emptyctx ⊢ cal(N) : RR^n attach(multimap, br: r) RR^k, quad r = ||W_1|| dot ||W_2|| $
//   the product-of-norms Lipschitz bound of robustness certification, read off the derivation

// == Example: robustness as a predicate

// #set text(size: 17pt)
// #definition(title: [Quantitative robustness])[
//   For $cal(N) : RR^n multimap RR^k$ and a tolerance $r$,
//   $ "Rob"_r (cal(N), v) ::= r (x =_(RR^n) v) multimap (cal(N) space x =_(RR^k) cal(N) space v) $
//   evaluates to $e^(r dot d(x, v) - d(cal(N) x, cal(N) v))$: true at $x$ iff $d(cal(N) x, cal(N) v) <= r dot d(x, v)$.
// ]
// #proposition(title: [Robustness for free from the sensitivity type])[
//   If $emptyctx ⊢ cal(N) : RR^n attach(multimap, br: r) RR^k$, then for every $v$ and reference measure $m$
//   $ v : RR^n thin | thin top ent(oo) fa(oo) (x tilde m). "Rob"_r (cal(N), v) $
// ]
// #pause
// - $r = 1$: *individual fairness*, similar inputs get similar outputs, is non-expansiveness
// - A softer grade over a data distribution gives an *average-case* certificate,
//   #box($"AvgRob"^s_r ::= fa(s) (x tilde m). "Rob"_r (cal(N), v)$); by (RELAX) the hard certificate entails every softer one
// - A stochastic classifier $"net" : RR^n attach(multimap, br: r) cal(W) bold(2)$ is robust in the Kantorovich distance
