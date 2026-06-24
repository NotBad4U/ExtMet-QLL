
// #import "lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "main.typ": *

// Shrink a diagram uniformly so it never exceeds the width of its table cell.
#let fit-cell(body) = layout(size => {
  let m = measure(body)
  let f = if m.width > size.width and size.width > 0pt { size.width / m.width } else { 1.0 }
  scale(f * 100%, origin: left + horizon, reflow: true, body)
})

#set document(title: "λ-FQLL cheatsheet")

#align(center, text(1.4em, weight: "bold")[λ-FQLL cheatsheet])

= Syntax

#term-syntax

#types-syntax

= Typing

#align(left, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #typing-judg
])

#align(left, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #ctx-judg
])

== Context rules

#align(
  center,
  rule-set(
    ..ctx-typing-rules,
  ),
)

== Terms typing ruls

#align(
  center,
  rule-set(..typing-term-rules),
)


= Semantics

== Judgement

#align(
  center,
  judg-sem,
)

== Regular types

#sem-types

== Structural function

#struct-func


// Semantic interpretation of each term typing rule.
#figure(
  table(
    columns: (auto, 1fr),
    align: (center + horizon, left + horizon),
    stroke: (x: none, y: 0.5pt),
    inset: (x: 10pt, y: 8pt),

    table.header([*Rule*], [*Diagram*]),

    // (VAR)  Γ, x:ʳA, Γ' ⊢ x : A   — project to the slot, then r⟦A⟧ → ⟦A⟧ since r ≥ 1
    [(VAR)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧ times.o r⟦A⟧ times.o ⟦Γ'⟧$),
      node((1, 0), $r⟦A⟧$),
      node((2, 0), $⟦A⟧$),
      edge((0, 0), (1, 0), $"weak"$, "->"),
      edge((1, 0), (2, 0), $r >= 1$, "->"),
    ),

    // (ABS)  λx.t : A ⊸ʳ B   — ⟦λx.t⟧ = curry(⟦t⟧); the triangle is its defining property
    [(ABS)],
    diagram(
      spacing: (4.5em, 3em),
      node((0, 0), $⟦Γ⟧ times.o r⟦A⟧$),
      node((1, 0), $⟦B⟧$),
      node((0, 1), $(r⟦A⟧ multimap ⟦B⟧) times.o r⟦A⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((0, 0), (0, 1), $⟦λ x. t⟧ times.o "id"$, "->"),
      edge((0, 1), (1, 0), $"eval"$, "->"),
    ),

    // (APP)  Γ ⧺ rΓ' ⊢ t u : B   — Rasmus's diagram
    [(APP)],
    diagram(
      spacing: 2.6em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r⟦Γ'⟧$),
      node((2, 0), $(r⟦A⟧ multimap ⟦B⟧) times.o r⟦A⟧$),
      node((3, 0), $⟦B⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $⟦t⟧ times.o r⟦u⟧$, "->"),
      edge((2, 0), (3, 0), $"eval"$, "->"),
    ),

    // (PAIR)  ⟨t,u⟩ : A × B   (shared Γ — cartesian pairing)
    [(PAIR)],
    diagram(spacing: 3em, node((0, 0), $⟦Γ⟧$), node((1, 0), $⟦A⟧ times ⟦B⟧$), edge((0, 0), (1, 0), $⟨⟦t⟧, ⟦u⟧⟩$, "->")),

    // (π_i)  π_i t : A_i
    [($π_i$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A_1⟧ times ⟦A_2⟧$),
      node((2, 0), $⟦A_i⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $pi_i$, "->"),
    ),

    // (inj_i)  inj_i t : A_1 + A_2
    [($"inj"_i$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A_i⟧$),
      node((2, 0), $⟦A_1⟧ + ⟦A_2⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $iota_i$, "->"),
    ),

    // (CASE)  Γ ⧺ rΓ' ⊢ case t of [inj_1 x ⇒ u | inj_2 y ⇒ v] : C   (uses ⊗-over-+ distributivity)
    [(CASE)],
    fit-cell(diagram(
      spacing: 1.5em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r⟦Γ'⟧$),
      node((2, 0), $⟦Γ⟧ times.o r(⟦A⟧ + ⟦B⟧)$),
      node((3, 0), $(⟦Γ⟧ times.o r⟦A⟧) + (⟦Γ⟧ times.o r⟦B⟧)$),
      node((4, 0), $⟦C⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $"id" times.o r⟦t⟧$, "->"),
      edge((2, 0), (3, 0), $"dist"$, "->"),
      edge((3, 0), (4, 0), $[⟦u⟧, ⟦v⟧]$, "->"),
    )),

    // (⊗)  rΓ ⧺ sΓ' ⧺ Γ'' ⊢ (t,u) : A ⊗ʳˢ B   (Γ'' weakened away; codomain = ⟦A ⊗ʳˢ B⟧)
    [($times.o$)],
    diagram(
      spacing: 2.8em,
      node((0, 0), $⟦r Γ ⧺ s Γ' ⧺ Γ''⟧$),
      node((1, 0), $r⟦Γ⟧ times.o s⟦Γ'⟧$),
      node((2, 0), $r⟦A⟧ times.o s⟦B⟧$),
      edge((0, 0), (1, 0), $"split, weak"$, "->"),
      edge((1, 0), (2, 0), $r⟦t⟧ times.o s⟦u⟧$, "->"),
    ),

    // (LET-⊗)  Γ ⧺ Γ' ⊢ let (x,y) = t in u : C   (last arrow uses the associator α to reassociate)
    [(LET-$times.o$)],
    diagram(
      spacing: 2.4em,
      node((0, 0), $⟦Γ ⧺ Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o ⟦Γ'⟧$),
      node((2, 0), $⟦Γ⟧ times.o (r⟦A⟧ times.o s⟦B⟧)$),
      node((3, 0), $⟦C⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $"id" times.o ⟦t⟧$, "->"),
      edge((2, 0), (3, 0), $⟦u⟧ ∘ alpha$, "->"),
    ),

    // (δ)  δ t : 𝒲A   (monad unit η = δ)
    [($delta$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A⟧$),
      node((2, 0), $cal(W)⟦A⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $eta = delta$, "->"),
    ),

    // (⅋_p)  pΓ ⧺ (1-p)Γ' ⊢ t ⅋_p u : 𝒲A   — +_p(μ,ν) = pμ + (1-p)ν, short by the barycentric ineq.
    [($amp.inv_p$)],
    fit-cell(diagram(
      spacing: 1.7em,
      node((0, 0), $⟦p Γ ⧺ (1-p) Γ'⟧$),
      node((1, 0), $p⟦Γ⟧ times.o (1-p)⟦Γ'⟧$),
      node((2, 0), $p cal(W)⟦A⟧ times.o (1-p) cal(W)⟦A⟧$),
      node((3, 0), $cal(W)⟦A⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $p⟦t⟧ times.o (1-p)⟦u⟧$, "->"),
      edge((2, 0), (3, 0), $+_p$, "->"),
    )),

    // (LET)  Γ ⧺ rΓ' ⊢ let x = u in t : E   (E an IB-algebra) — strong-monad bind into α_E
    [(LET)],
    diagram(
      spacing: 2em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r cal(W)⟦A⟧$),
      node((2, 0), $cal(W)(⟦Γ⟧ times.o r⟦A⟧)$),
      node((3, 0), $cal(W)⟦E⟧$),
      node((4, 0), $⟦E⟧$),
      edge((0, 0), (1, 0), $("id" times.o r⟦u⟧) ∘ "split"$, "->"),
      edge((1, 0), (2, 0), $"st"$, "->"),
      edge((2, 0), (3, 0), $cal(W)⟦t⟧$, "->"),
      edge((3, 0), (4, 0), $alpha_E$, "->"),
    ),

    // (FIX)  Γ ⊢ fix x.t : A   from (1-r)Γ, x:ʳA ⊢ t : A with r < 1.
    // ⟦t⟧ is r-contractive in the A-slot, so Banach (within each galaxy) gives the unique fixed point;
    // the triangle IS the fixed-point equation ⟦fix x.t⟧ = ⟦t⟧ ∘ ⟨id, ⟦fix x.t⟧⟩.
    [(FIX)],
    diagram(
      spacing: (5em, 2.4em),
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $(1-r)⟦Γ⟧ times.o r⟦A⟧$),
      node((1, 1), $⟦A⟧$),
      edge((0, 0), (1, 0), $⟨"id", ⟦"fix" x. t⟧⟩$, "->"),
      edge((1, 0), (1, 1), $⟦t⟧$, "->"),
      edge((0, 0), (1, 1), $⟦"fix" x. t⟧$, "->"),
    ),
  ),
)

= Prop



=== Signature

$
  prop = #prop-signature
$

=== Typing rules

#align(center, rule-set(..prop-typing-rules))


=== Semantics

#prop-sem

==== Equality semantics

#figure(
  table(
    columns: 5,
    align: (left, left, center, center, left),
    stroke: none,
    inset: (x: 9pt, y: 6pt),
    table.hline(stroke: 1pt),
    table.header(
      [Distance $d = d_(⟦A⟧)(⟦t⟧, ⟦u⟧)$], [Meaning], [$⟦ t =_A u ⟧ = e^(-d)$], [Lands in], [Truth ( $>= 1$)]
    ),
    table.hline(stroke: 0.5pt),
    [$d = 0$], [$t, u$ equal], [$e^0 = 1$], [${1}$], [true],
    [$0 < d < oo$], [apart, finite], [$e^(-d) in (0, 1)$], [$(0, 1)$], [false to degree $d$],
    [$d = oo$], [infinitely far], [$e^(-oo) = 0$], [${0} = bot$], [false],
    table.hline(stroke: 1pt),
  ),
)

= Logic rule
