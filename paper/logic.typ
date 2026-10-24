#import "common.typ": *

= Logic

We now turn the poset $prop$ into the carrier of an _internal logic_. Predicates are terms of type $prop$, and reasoning is carried out by a _graded_ entailment whose grade is the softness $p$.

#let prop-signature = $(
  [0, +oo],
  ⊥, ⊤,
  times.o, times.o^*, multimap,
  (-)^*,
  and^s, or^s,
  exists^s, forall^s
)$

$
  prop = #prop-signature
$

Here $0 = bot$ and $oo = top$ are the lattice bounds, $1$ is the multiplicative unit, and a value is _true_ iff it is $>= 1$. We equip $prop$ with the _log metric_ $d_prop (a, b) = |log a - log b|$, the pullback of the additive metric along $log$. Under it the involution $a |-> a^* = 1\/a$ is an isometry, the multiplicatives $times.o$ and $multimap$ become addition and subtraction of log-values, and every soft family $plus.o^(plus.minus s)$ and mean $integral^(plus.minus s)$ is non-expansive at _every_ grade $s in [0, oo]$, with no $|s| >= 1$ restriction. The crisp values $0$ and $oo$ lie at infinite log-distance from every soft value, so the metric content sits on $(0, oo) tilde.equiv RR$.

The equality former is interpreted by the distance map, the quantifiers by the $p$-mean and its harmonic dual; each is a morphism of *CExtMet* (hence non-expansive):

$
      (attach(=, br: A)) & : A times.o A -> prop, quad                        & (x, x') |-> e^(-d_A (x, x')) \
  exists^s_A, forall^s_A & : cal(W) A times.o (A multimap prop) -> prop, quad &                 s in [0, oo]
$

For a reference measure $m in cal(W) A$, a predicate $g in A multimap prop$, and integration point $x : A$, the operators are the $p$-mean and harmonic $p$-mean
$
  exists^s_A (m, g) & ≜ (integral_A g(x)^s dif m(x))^(1\/s) quad quad
                      forall^s_A (m, g) & ≜ (integral_A g(x)^(-s) dif m(x))^(-1\/s)
$

The annotation $x tilde m$ — read as in the expectation $EE_(x tilde m)$ — binds the integration point $x$ over the carrier of $m$ and names $m$ as the reference measure; the boundary $s = oo$ gives the measure-free $sup_x g(x)$ and $inf_x g(x)$. The quantifier _binders_ reuse this annotation: $exists^s (x tilde m). φ$ binds $x$ in the body $φ$ while $m$ stays in the enclosing context, and abbreviates the operator application $exists^s_A (m, lambda x. φ)$ (dually $forall^s$).

== Typing rules for logical predicates

A _predicate in context_ $Γ$ is a term $φ$ with $Γ ⊢ φ : prop$. Since $prop$ is itself an object of *CExtMet*, predicates are non-expansive maps, so their formation _tracks sensitivity_ exactly like ordinary terms: the tensor-like connectives ($=, times.o, multimap, plus.o^s$) sum their contexts as $Γ ⧺ Γ'$, propositions can be _scaled_ by $r$, and a quantifier binds its point variable at its grade $s$, drawing the reference measure from a separate $cal(W) A$ premise. Logical _derivability_, by contrast, only uses the discrete context $Δ$ introduced below:

#let prop-tt = prooftree(rule(name: [($⊤_i$)], $Γ ⊢ top : prop$))

#let prop-ff = prooftree(rule(name: [($⊥_i$)], $Γ ⊢ bot : prop$))

#let prop-eq = prooftree(rule(
  name: [(P-=)],
  $Γ ⊢ t : A$,
  $Γ' ⊢ u : A$,
  $Γ ⧺ Γ' ⊢ (t attach(=, br: A) u) : prop$,
))

#let prop-tens = prooftree(rule(
  name: [(P-⊗)],
  $Γ ⊢ φ : prop$,
  $Γ' ⊢ ψ : prop$,
  // --------------------------
  $Γ ⧺ Γ' ⊢ φ times.o ψ : prop$,
))

#let prop-imp = prooftree(rule(
  name: [($⊸_i$)],
  $Γ ⊢ φ : prop$,
  $Γ' ⊢ ψ : prop$,
  // --------------------------
  $Γ ⧺ Γ' ⊢ φ multimap ψ : prop$,
))

#let prop-scale = prooftree(rule(
  name: [(P-scale)],
  $Γ ⊢ φ : prop$,
  $r in [0, oo]$,
  // ---------------------
  $r Γ ⊢ r φ : prop$,
))

#let prop-dual = prooftree(rule(
  name: [(P-$*$)],
  $Γ ⊢ φ : prop$,
  // ----------------
  $Γ ⊢ φ^* : prop$,
))

#let prop-sum = prooftree(rule(
  name: [($plus.o^s$)],
  $Γ ⊢ φ : prop$,
  $Γ ⊢ ψ : prop$,
  $s in [0, oo]$,
  // --------------------------
  $Γ ⊢ φ or^s ψ : prop$,
))

#let prop-hsum = prooftree(rule(
  name: [($plus.o^(-s)$)],
  $Γ ⊢ φ : prop$,
  $Γ ⊢ ψ : prop$,
  $s in [0, oo]$,
  // --------------------------
  $Γ ⊢ φ and^s ψ : prop$,
))

#let prop-all = prooftree(rule(
  name: [($forall^s_i$)],
  $Γ, x tcol(s) A ⊢ φ : prop$,
  $Γ' ⊢ m : cal(W) A$,
  $s in [0, oo]$,
  // --------------------------------
  $Γ ⧺ Γ' ⊢ fa(s) (x tilde m). space φ : prop$,
))

#let prop-ex = prooftree(rule(
  name: [($exists^s_i$)],
  $Γ, x tcol(s) A ⊢ φ : prop$,
  $Γ' ⊢ m : cal(W) A$,
  $s in [0, oo]$,
  // -------------------------------
  $Γ ⧺ Γ' ⊢ ex(s) (x tilde m). space φ : prop$,
))

#let prop-typing-rules = (
  prop-tt,
  prop-ff,
  prop-eq,
  prop-tens,
  prop-imp,
  prop-scale,
  prop-dual,
  prop-sum,
  prop-hsum,
  prop-all,
  prop-ex,
)

#align(center, rule-set(..prop-typing-rules))

The tensor connectives are non-expansive out of $prop times.o prop$ (hence the sum $Γ ⧺ Γ'$), matching @def:extmet-cmon; scaling $r φ$ comes from $r prop multimap prop$, the spare $Γ'$ absorbing weakening when $r = 0$.

=== Interpretation of logical predicate

#let prop-sem = columns(2)[
  $
          ⟦ ⊤ ⟧ & ≜ ∞ \
    ⟦ t =_A u ⟧ & ≜ e^(-d_⟦ A ⟧) ∘ (⟦t⟧ ⊗ ⟦ u ⟧) ∘ "split" \
      ⟦ φ ⊗ ψ ⟧ & ≜ ⊗ ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
    ⟦ φ ⊗^* ψ ⟧ & ≜ ⊗^* ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
      ⟦ φ ⊸ ψ ⟧ & ≜ space ⊸ ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
        ⟦ φ^* ⟧ & ≜ (-)^* ∘ ⟦φ⟧ \
  $
  #colbreak()
  $
                      ⟦ ⊥ ⟧ & ≜ 0 \
                ⟦ φ ∨^s ψ ⟧ & ≜ plus.o^s ∘ ⟨⟦φ⟧, ⟦ψ⟧⟩ quad (s = oo : space max = or) \
                ⟦ φ ∧^s ψ ⟧ & ≜ plus.o^(-s) ∘ ⟨⟦φ⟧, ⟦ψ⟧⟩ quad (s = oo : space min = and) \
    ⟦ ∃^s (x tilde m) . φ ⟧ & ≜ integral^s_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) \
    ⟦ ∀^s (x tilde m) . φ ⟧ & ≜ integral^(-s)_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) \
  $
]

#prop-sem

The equality clause is a morphism of *CExtMet*: it factors as the $1$-Lipschitz map $d_(⟦A⟧)$ into the _additive_ $[0, oo]$, followed by the isometry $e^(-(-)) : ([0, oo], |a - b|) -> prop$, so the composite is non-expansive.

#block(above: 1.5em, below: 1.5em, width: 100%, align(center, diagram(
  spacing: 3.6em,
  node((0, 0), $⟦A⟧ times.o ⟦A⟧$),
  node((1, 0), $([0, oo], |a - b|)$),
  node((2, 0), $prop$),
  edge((0, 0), (1, 0), $d_(⟦A⟧)$, "->"),
  edge((1, 0), (2, 0), $e^(-(-))$, "->"),
  edge((0, 0), (2, 0), $e^(-d_(⟦A⟧))$, "->", bend: 42deg),
)))

#lemma([Equality semantics interpretation is reflexive, symmetric and transitive])[
  Read $φ ⊢ ψ$ as $⟦ψ⟧ >= ⟦φ⟧$ and the comma as $times.o$. The predicate $⟦ t =_A u ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧))$ satisfies, at every grade $s in [0, oo]$:
  - *reflexivity:* $⟦ t =_A t ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦t⟧)) = e^0 = 1$, so $Ψ ent(oo) (t =_A t)$ holds — true at the threshold $1$;
  - *symmetry:* $⟦ t =_A u ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧)) = e^(-d_(⟦A⟧) (⟦u⟧, ⟦t⟧)) = ⟦ u =_A t ⟧$, since $d_(⟦A⟧)$ is symmetric — the two predicates are equal;
  - *transitivity:* $(t =_A u) times.o (u =_A v) ⊢ (t =_A v)$, i.e. $e^(-d_(⟦A⟧) (⟦t⟧, ⟦v⟧)) >= e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧)) dot e^(-d_(⟦A⟧) (⟦u⟧, ⟦v⟧))$, which after $-log$ is exactly the triangle inequality $d_(⟦A⟧) (⟦t⟧, ⟦v⟧) <= d_(⟦A⟧) (⟦t⟧, ⟦u⟧) + d_(⟦A⟧) (⟦u⟧, ⟦v⟧)$.
  All three hold at every grade because the averaged integrand is pointwise $>= 1$, and any $s$-mean of values $>= 1$ is again $>= 1$.
]

The quantifier clauses are morphisms by the same pattern: after $"split"$, the pair $⟦m⟧ times.o "curry"(⟦φ⟧)$ feeds the operator $exists^s_(⟦A⟧)$ (resp. $forall^s_(⟦A⟧)$), which is non-expansive in the predicate slot (sup-log, every $s$) and in the measure slot (Kantorovich, $p >= 1$).

#block(above: 1.5em, below: 1.5em, width: 100%, align(center, diagram(
  spacing: 3.6em,
  node((0, 0), $⟦Γ⟧ times.o ⟦Γ'⟧$),
  node((1, 0), $cal(W) ⟦A⟧ times.o (⟦A⟧ multimap prop)$),
  node((2, 0), $prop$),
  edge((0, 0), (1, 0), $⟦m⟧ times.o "curry"(⟦φ⟧)$, "->"),
  edge((1, 0), (2, 0), $exists^s_(⟦A⟧)$, "->"),
)))

so that $⟦ exists^s (x tilde m). φ ⟧ = integral^s_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) = exists^s_(⟦A⟧) ∘ (⟦m⟧ times.o "curry"(⟦φ⟧)) ∘ "split"$, and dually with $forall^s$.

== The graded entailment judgement

The logical judgement has the shape

#align(center, box(stroke: .5pt, inset: 5pt)[
  $ Δ thin | thin Ψ ent(p) φ $
])

where $Δ$ is a discrete typing context, $Ψ = ψ_1, ..., ψ_n$ a list of predicates (the _logical context_), $φ$ the conclusion, and $p ∈ [0, ∞]$ the _softness grade_. The intended reading is the graded entailment of the soft quantitative logic: writing $times.o.big Ψ$ for the tensor of the context, the judgement is _valid_ when, up to the chosen truth threshold,

$ 1 ≤ integral_x^(-p) ((times.o.big Ψ) multimap φ), $

i.e. the harmonic $p$-mean of the implication over the (Wasserstein) space of the discrete context. The grade $p$ is the exponent of that $p$-mean: $p = ∞$ recovers the _hard_ entailment $and.big_x ((times.o.big Ψ) multimap φ)$, while smaller $p$ is _softer_. The grade monoid is $([0, ∞], plus.o^*, ∞)$: its unit is $∞$ (graded reflexivity), and grades compose under cut by _harmonic sum_ $plus.o^*$, with $1 / (p plus.o^* q) = 1 / p + 1 / q$, the Hölder conjugacy of @def:holder.

#let l-ass = prooftree(rule(name: [(ASS)], $Δ thin | thin Ψ, φ ent(oo) φ$))
#let l-cut = prooftree(rule(
  name: [(CUT)],
  $Δ | Ψ ent(p) φ$,
  $Δ | Φ, φ ent(q) χ$,
  // --------------------------
  $Δ | Φ, Ψ ent(p plus.o^* q) χ$,
))
#let l-relax = prooftree(rule(
  name: [(RELAX)],
  $Δ | Ψ ent(q) φ$,
  $p <= q$,
  // --------------
  $Δ | Ψ ent(p) φ$,
))
#let l-weak = prooftree(rule(
  name: [(WEAK)],
  $Δ | Ψ ent(p) φ$,
  // -----------------
  $Δ | Ψ, ψ ent(p) φ$,
))

#align(center, rule-set(l-ass, l-cut, l-relax, l-weak))

== Connectives and quantifiers

The multiplicative fragment is residuated ($times.o ⊣ multimap$); note how cut-like rules accumulate softness by harmonic sum, while the introduction of $multimap$ leaves the grade untouched.

#let l-tensR = prooftree(rule(
  name: [(⊗R)],
  $Δ | Ψ ent(p) φ$,
  $Δ | Φ ent(q) ψ$,
  // --------------------------------------
  $Δ | Ψ, Φ ent(p plus.o^* q) φ times.o ψ$,
))
#let l-tensL = prooftree(rule(
  name: [(⊗L)],
  $Δ | Ψ, φ, ψ ent(p) χ$,
  // --------------------------
  $Δ | Ψ, φ times.o ψ ent(p) χ$,
))
#let l-impR = prooftree(rule(
  name: [(⊸R)],
  $Δ | Ψ, φ ent(p) ψ$,
  // --------------------------
  $Δ | Ψ ent(p) φ multimap ψ$,
))
#let l-impL = prooftree(rule(
  name: [(⊸L)],
  $Δ | Ψ ent(p) φ multimap ψ$,
  $Δ | Φ ent(q) φ$,
  // ----------------------------
  $Δ | Ψ, Φ ent(p plus.o^* q) ψ$,
))

#align(center, rule-set(l-tensR, l-tensL, l-impR, l-impL))

The soft disjunction $psum(s)$ (the $s$-sum of @def:holder) has the two semiadditive introductions, since $a <= a psum(s) b$ for every softness $s$. Equality is introduced by reflexivity.

#let l-sumIL = prooftree(rule(
  name: [($plus.o^s$-IL)],
  $Δ | Ψ ent(p) φ$,
  // --------------------------
  $Δ | Ψ ent(p) φ psum(s) ψ$,
))
#let l-sumIR = prooftree(rule(
  name: [($plus.o^s$-IR)],
  $Δ | Ψ ent(p) ψ$,
  // --------------------------
  $Δ | Ψ ent(p) φ psum(s) ψ$,
))
#let l-eqI = prooftree(rule(
  name: [(=I)],
  $Δ ⊢ t : A$,
  // ------------------------------------
  $Δ | Ψ ent(oo) (t attach(=, br: A) t)$,
))

#align(center, rule-set(l-sumIL, l-sumIR, l-eqI))

The soft quantifiers are the graded adjoints to reindexing. We give the _adjunction_ rules, which hold at the matching grade $s$: universal introduction (right adjoint) and existential elimination (left adjoint).

#let l-allI = prooftree(rule(
  name: [($forall^s$-I)],
  $Δ, x : A | Ψ ent(s) φ$,
  $Δ ⊢ m : cal(W) A$,
  $x in.not "FV"(Ψ)$,
  // --------------------------
  $Δ | Ψ ent(s) fa(s) (x tilde m). φ$,
))
#let l-exE = prooftree(rule(
  name: [($exists^s$-E)],
  $Δ, x : A | Ψ, φ ent(s) χ$,
  $Δ ⊢ m : cal(W) A$,
  $x in.not "FV"(Ψ, χ)$,
  // ------------------------------
  $Δ | Ψ, ex(s) (x tilde m). φ ent(s) χ$,
))

#align(center, rule-set(l-allI, l-exE))
