#import "common.typ": *

= A calculus for CExtMet

We now define a calculus for programming in the category *CExtMet*.

== Syntax

The syntax is based on a simply-typed $lambda$-calculus with products and sums, extended with  primitives for probabilistic distributions, recursion, and fixed points.


// Term syntax grammar (reused in spreadsheet.typ)
#let term-syntax = $
  M, N ::= & x | () | lambda x. M | M #h(0.3em) N | chevron.l M, N chevron.r | pi_1 M | pi_2 M | "let" x = M "in" N \
         | & #h(0.5em) "inl" M | "inr" M | "case" M "of" "inl" x => N | "inr" y => N \
         | & #h(0.5em) "fix" x. M | (M, N) | delta M | M amp.inv_p N | "zero" | "succ"(M) | "rec"(u, (x,t).t, v)
$

#term-syntax

There are two pairs constructors, $chevron.l M, N chevron.r$ and $(M, N)$, corresponding to the Cartesian and monoidal  products, respectively. The first one is eliminated using the projections $pi_i M$, whereas the second one is eliminated using $( "let" x = M "in" N)$. The term "()" is unit value. The injections "inl" and "inr" form expressions of sum type, which are eliminated by case analysis  $"case" M "of" "inl" x => N | "inr" y => N$.
The term $delta M$ denotes a distribution, and $M amp.inv_p N$ the convex sumof $M$ and $N$. For convenience, we also include the natural numbers with constructors $0$ and $"succ"(M)$. Finally, $"fix" x. M$ is the “Banach” fixed point combinator.

The types of the calculus are defined by the grammar:

#let types-syntax = $
  A, B ::= & NN | 1 | A times B | A + B | A attach(times.o, bl: r, br: s) B | A multimap_r B | cal(W) A
$

#types-syntax

essentially corresponding to the constructions of the previous section. Although rescaling of metric  spaces played a central role in the previous section, it is not a primitive type former in the calculus.
Instead, it is part of the tensor type $A attach(times.o, bl: r, br: s) B$ and function type $A multimap_r B$ constructors. This choice  was made to minimize the book keeping necessary for scalars in terms. Finally, $cal(W) A$ is the Wasserstein type of probability measures on $A$.

== Typing rules and properties



// #remark([Softness lives on the logical entailment, not the typing judgement])[
//   @def:holder is what lets the $p$-sum connective $plus.o.big^p$ pair soundly against its conjugate $plus.o.big^q$: a predicate aggregated with the $p$-sum may only be contracted against one aggregated with the conjugate $q$-sum, since the pairing is bounded only when $1 / p + 1 / q = 1$. For this reason softness is tracked as a grade on the entailment of the inner logic, and not on the term-level typing judgement.
// ]

Terms are typed with the judgement:

#let typing-judg = $Γ ⊢ t : A$

#align(center, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #typing-judg
])

where $Γ$ is a context of variable bindings, $t$ is a term of type $A$.

In context the sensitivity of a variable $x$ is tracked by annotating its type with a sensitivity index $r$ as in the following context judgment:

#let ctx-judg = $ Γ, x tcol(r) A $

#align(center, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #ctx-judg
])


We track the sensitivity $r$, which controls the Lipschitz behaviour of terms and, in particular, probabilistic choice described in @def:ib-algebra and @def:guarded-fix. Softness is not a term-level grade: it grades the entailment of the inner logic (@def:holder), and is introduced later, not in the term calculus.


=== Structural rules

The notation $Γ,Γ'$ denotes the concatenation of contexts with disjoint variable bindings.
The sum of two context $Γ ⧺ Γ'$ and scaling $r Γ$ of contexts are defined to keep track of the _sensitivities_ of the resources in the context.

#let ctx = prooftree(rule(
  name: [],
  $emptyctx :: "ctx"$,
))

#let abstraction = prooftree(rule(
  name: [],
  $Γ :: "ctx"$,
  $x in.not Γ$,
  $r in [0, oo]$,
  // ---------------------------------------
  $Γ, x tcol(r) A :: "ctx"$,
))


#let ctx-typing-rules = (ctx, abstraction)

#align(
  center,
  rule-set(
    ..ctx-typing-rules,
  ),
)

#definition[context scaling operations][
  - $emptyctx ⧺ emptyctx equiv emptyctx$
  - $r emptyctx equiv emptyctx$
  - $(Γ, x tcol(r) A) ⧺ (Γ', x tcol(s) A) equiv Γ ⧺ Γ', x tcol(r + s) A$
  - $r(Γ, x tcol(s) A) equiv r(Γ), x tcol(r dot s) A$
]

=== Rules for ordinary terms

#let var = prooftree(rule(
  name: [(VAR)],
  $r >= 1$,
  // --------------------------
  $Γ, x tcol(r) A, Γ' ⊢ x : A$,
))

#let abs = prooftree(rule(
  name: [(ABS)],
  $Γ, x tcol(r) A ⊢ t : B$,
  // ---------------------------------
  $Γ ⊢ λ x. t : A attach(⊸, br: r) B$,
))

#let app = prooftree(rule(
  name: [(APP)],
  $Γ ⊢ t : A attach(⊸, br: r) B$,
  $Γ' ⊢ u : A$,
  // --------------------------
  $Γ ⧺ r Γ' ⊢ t space u : B$,
))

#let unit = prooftree(rule(
  name: [(UNIT)],
  // ------------
  $Γ ⊢ () : 1$,
))

#let pair = prooftree(rule(
  name: [(PAIR)],
  $Γ ⊢ t : A$,
  $Γ ⊢ u : B$,
  // ----------------------------------------
  $Γ ⊢ chevron.l t, u chevron.r : A times B$,
))

#let proj = prooftree(rule(
  name: [($π_i$)],
  $Γ ⊢ t : A_1 times A_2$,
  // --------------------------
  $Γ ⊢ pi_i space t : A_i$,
))


#let inj = prooftree(rule(
  name: [($"inj"_i$)],
  $Γ ⊢ t : A_i$,
  // --------------------------
  $Γ ⊢ "inj"_i space t : A_1 + A_2$,
))

#let case = prooftree(rule(
  name: [(CASE)],
  $Γ' ⊢ t : A + B$,
  $Γ, x tcol(r) A ⊢ u : C$,
  $Γ, y tcol(r) B ⊢ v : C$,
  $r > 0$,
  // --------------------------------------------------------
  $Γ ⧺ r Γ' ⊢ "case" t "of" ["inj"_1 x => u | "inj"_2 y] : C$,
))

#let tensor = prooftree(rule(
  name: [($times.o$)],
  $Γ ⊢ t : A$,
  $Γ' ⊢ u : B$,
  // --------------------------------------------------------
  $r Γ ⧺ s Γ' ⧺ Γ'' ⊢ (t, u) : A attach(⊗, br: s, bl: r) B$,
))

#let letin = prooftree(rule(
  name: [(LET-$times.o$)],
  $Γ, x tcol(r) A, y tcol(s) B ⊢ t : C$,
  $Γ' ⊢ u : A attach(⊗, br: r, bl: s) B$,
  // -------------------------------------
  $Γ ⧺ Γ' ⊢ "let" (x, y) = t "in" u : C$,
))

#let dirac = prooftree(rule(
  name: [($delta$)],
  $Γ ⊢ t : A$,
  // ----------------------------
  $Γ ⊢ delta space t : cal(W) A$,
))

#let probchoice = prooftree(rule(
  name: [($amp.inv_p$)],
  $Γ ⊢ t : cal(W) A$,
  $Γ' ⊢ u : cal(W) A$,
  $p in (0, 1)$,
  // -----------------------------------------
  $p Γ ⧺ (1-p) Γ' ⊢ t amp.inv_p u : cal(W) A$,
))

#let letalg = prooftree(rule(
  name: [(LET)],
  $Γ, x tcol(r) A ⊢ t: E$,
  $Γ' ⊢ u : cal(W) A$,
  "E IB algebra",
  $r < infinity$,
  // ---------------------------------------
  $Γ ⧺ r Γ' ⊢ "let" x = u "in" t : E$,
))

#let zero = prooftree(rule(
  name: [(ZERO)],
  // --------------------------
  $Γ ⊢ "zero" : NN$,
))

#let succ = prooftree(rule(
  name: [(SUCC)],
  $Γ ⊢ t : NN$,
  // --------------------------
  $Γ ⊢ "succ"(t) : NN$,
))

#let rec = prooftree(rule(
  name: [(REC)],
  $Γ ⊢ z : A$,
  $Γ', x tcol(1) A, y tcol(1) NN ⊢ s : A$,
  $Γ'' ⊢ n : NN$,
  // ------------------------------------------
  $Γ ⧺ ∞ Γ' ⧺ Γ'' ⊢ "rec"(z, (x,y).s, n) : A$,
))

#let fix = prooftree(rule(
  name: [(FIX)],
  $(1-r) Γ, x tcol(r) A ⊢ t : A$,
  $r < 1$,
  // --------------------------
  $Γ ⊢ "fix" x. t : A$,
))

#let typing-term-rules = (
  var,
  abs,
  app,
  unit,
  pair,
  proj,
  inj,
  case,
  tensor,
  letin,
  dirac,
  probchoice,
  letalg,
  zero,
  succ,
  rec,
  fix,
)

#align(
  center,
  rule-set(..typing-term-rules),
)

== Semantics

Judgements are interpreted as morphisms:

#let judg-sem = $⟦ Γ ⊢t : A ⟧: ⟦ Γ ⟧ →^⟦ t ⟧ ⟦ A ⟧$

#align(
  center,
  judg-sem,
)

Each type is interprerted as an object in *CExtMet*:

#let sem-types = columns(3)[
  $
                             ⟦ NN ⟧ & ≜ NN \
                      ⟦ A times B ⟧ & ≜ ⟦ A ⟧ times ⟦ B ⟧ \
    ⟦ A attach(⊗, bl: r, br: s) ψ ⟧ & ≜ r ⟦ A ⟧ ⊗ s ⟦ B ⟧ \
  $
  #colbreak()
  $
                              ⟦ 1 ⟧ & ≜ bold("1") \
                          ⟦ A + B ⟧ & ≜ ⟦ A ⟧ + ⟦ B ⟧ \
    ⟦ φ attach(multimap, br: r) ψ ⟧ & ≜ r⟦ A ⟧ multimap ⟦ B ⟧ \
  $
  #colbreak()
  $
                   ⟦ cal(W)A ⟧ & ≜ cal(W)⟦ A ⟧ \
       ⟦ chevron.l chevron.r ⟧ & ≜ bold("1") \
    ⟦ Γ, x attach(:, tr: r) A⟧ & ≜ ⟦ Γ ⟧ times.o r⟦ A⟧
  $
]

#sem-types

Judgements are interpreted as morphisms:

$
  ⟦ Γ, x attach(:, tr: r) A⟧: ⟦ Γ ⟧ arrow r⟦ A ⟧
$

We define the semantics for the structural functions:


#let struct-func = columns(2)[
  $
    "split" & : ⟦ Γ ⧺ Γ' ⟧ arrow ⟦ Γ ⟧ times.o ⟦ Γ' ⟧ \
     "dist" & : ⟦ p Γ ⟧ arrow p ⟦ Γ ⟧ \
  $
  #colbreak()
  $
    "proj" & : ⟦ Γ , Δ , Γ' ⟧ arrow ⟦ Γ, Γ' ⟧ \
    "weak" & : ⟦ Γ ⧺ Γ' ⟧ arrow ⟦ Γ ⟧ \
  $
]

#struct-func
