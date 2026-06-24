#import "lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#show: para-lipics.with(
  title: [$lambda$-FQLL],
  title-running: [$lambda$-FQLL],
  authors: (
    (
      name: [Coltellacci Alessio],
      email: "alecol@itu.dk",
      orcid: "0009-0005-3580-2075",
      affiliations: [
        IT Univeristy Copenhagen
      ],
    ),
  ),
  copyright: [],
  keywords: [],
)

#let rule-set(column-gutter: 3em, row-gutter: 2em, ..rules) = {
  set par(leading: row-gutter)
  block(rules.pos().map(box).join(h(column-gutter, weak: true)))
}

#let emptyctx = $chevron.l chevron.r$;

// typing colon:  tcol(r) renders ":" with sensitivity r on top
#let tcol(r) = $attach(:, tr: #r)$

#let prop = "Prop";

= Preliminaries on extended Reals numbers

Many QLs are based on intervals of real numbers such as [0,∞], used in QLL.
Besides standard operations such as multiplication ⊗, we require the notion of comultiplication $times^*$ and p-sums $plus.o^p$, where $p eq.not 0$.
Comultiplication $a times.o^* b := (a^(−1) times.o b^(−1))^(−1)$ only differs from multiplication for $a= 0$ and $b= infinity$.

For ML applications, it is desirable to have operations that are differentiable and componentwise strictly increasing.
These are also referred to as _soft_ operations, in contrast to $max$ and $min$, which are referred to as _hard_ operations.
Due to being soft, p-sums $a plus.o^p b:= (a^p + b^p)^(1/p)$, originally applied to QLs in Yager logic, have recently gained importance and are used in QLL, for instance.
A key relation we are currently mechanising is that $plus.o^p$ converges to the binary maximum function as $p -> infinity$.

#notations[p-mean large operator][
  On the left we have the $p$-sum, and on the right its harmonic dual:
  $ plus.o.big_(i in I)^p a_i = (plus.o.big_(i in I) a_i^p)^(1/p) quad quad "and" quad quad plus.o.big_(i in I)^(p,*) a_i = (plus.o.big_(i in I) a_i^*)^(1/p)^* $.
]
#definition([Hölder conjugate exponents])[
  Two exponents $p, q in [1, +oo]$ are _Hölder conjugates_ when
  $ 1 / p + 1 / q = 1, $
  with the convention $1 / oo = 0$, so that $p = 1$ pairs with $q = oo$ and $p = q = 2$ is self-conjugate. Hölder's inequality @holder-inequality then bounds the $plus.o.big$-pairing of two families by the product of their $p$- and $q$-sums:
  $ plus.o.big_(i in I) (a_i times.o b_i) <= (plus.o.big_(i in I)^p a_i) times.o (plus.o.big_(i in I)^q b_i). $
] <def:holder>

= Preliminaries on extended metric spaces

// A function  $f: X -> Y$ between metric spaces is $r$-Lipschitz continuous , for $r >= 0$, if $r dot d_X (x_1, x_2) >= d_Y (f(x_1), f(x_2))$ for $x_1, x_2 in X$. A function is called  _non-expansive_ when $r = 1$ and a contraction
// when $r < 1$ and $X = Y$. A metric  space is complete if all Cauchy sequences converge.


#definition([Extended metric space])[
  Extended metric spaces are sets $X$ endowed with the distance function $d_infinity: X × X → [0,∞]$ as to allow the distance function d to attain the value ∞, i.e. distances are non-negative numbers on the extended real line $overline(RR)$.

] <def:ext-met>

#definition([Bounded extended metric])[
  Every extended metric can be replaced by a topologically equivalent real-valued metric i.e $d in RR^2 -> [0, infinity)$. It suffices to post-compose $d_infinity$ with a subadditive, monotonifcally increasing, bounded function vanishing at zero, e.g.

  - $d' (x, y) = frac(d_infinity (x, y), (1 + d_infinity (x, y))) quad "with" infinity / infinity = 1$
  - or  $d'' (x, y) = min(1, d_infinity (x, y))$,

  both of which take values in $[0, 1]$ and induce the same topology as $d_infinity$.
]<def:bounded-ext-met>

We will write $d_X$ instead of $d_infinity^X$ when it is clear from the context that we are talking about the extended metric on $X$.


#definition([r-Lipschitz continuity])[
  A function $f: X → Y$ between metric spaces is $r$-Lipschitz continuous, for $r ≥ 0$, if $r dot d_X (x, y) ≥ d_Y (f(x), f(y))$ for all $x, y ∈ X$. A function is called _non-expansive_ when $r = 1$ and a _contraction_ when $r < 1$ and $X = Y$.
]<def:lip-cont>

#definition([The category of $bold("CExtMet")$])[
  The category $bold("CExtMet")$ of complete extended metric spaces is defined by the following data:
  - objects: extended metric spaces $(X, d_X)$, that is, pairs consisting of a set $X$ together with an extended distance $d_X : X times X -> [0, +oo]$ satisfying @def:ext-met;
  - morphisms: $phi : (X, d_X) -> (Y, d_Y)$ are _short maps_ (equivalently, non-expansive maps), that is, functions $phi : X -> Y$ such that:
    $ d_Y (phi(x), phi(x')) <= d_X (x, x') quad "for every " x, x' in X. $
  - composition: is the composition of functions, and the identity on $(X, d_X)$ is $id_X$, which is trivially short map;
  - all Cauchy sequences in $(X, d_X)$ converges.
]

#proposition([Closed symmetric monoidal structure on $bold("CExtMet")$])[
  The category *CExtMet* carries a closed symmetric monoidal structure $(bold("CExtMet"), times.o, bold(1))$ given by:
  - Tensor product: For $(X, d_X), (Y, d_Y) in bold("CExtMet")$,
    $ (X, d_X) times.o (Y, d_Y) = (X times Y, #h(0.3em) d_X + d_Y), $
    with additive distance
    $ (d_X + d_Y)((x, y), (x', y')) = d_X (x, x') + d_Y (y, y'). $
  - Monoidal unit: The one-point space $bold(1) = ({*}, d_*)$ with $d_*(*,*) = 0$.
  - Internal hom: The object $[X, Y]$ is the set $bold("CExtMet")(X, Y)$ of short maps, equipped with the sup distance
    $ d_([X, Y])(phi, psi) = sup_(x in X) d_Y (phi(x), psi(x)) in [0, +oo]. $
  - Exponential adjunction: The bijection
    $ bold("CExtMet")(X times.o Y, Z) tilde.equiv bold("CExtMet")(X, [Y, Z]) $
    holds by currying: a map $f : X times Y -> Z$ is short with respect to $d_X + d_Y$ iff
    $ d_Z (f(x, y), f(x', y')) <= d_X (x, x') + d_Y (y, y'), $
    which is equivalent to requiring that each partial map $f(x, -) : Y -> Z$ be short and that $x |-> f(x, -)$ be short for the sup distance on $[Y, Z]$.
] <def:extmet-cmon>

The operator $X multimap Y$ denotes the set of non-expansive functions from $X$ to $Y$ endowed with point-wise supremum metric $d_(X multimap Y)(f, g) = sup_(x in X) d_Y (f(x), g(x))$. The counit of  the adjunction is function evaluation $"eval" : (X multimap Y) times.o X -> Y$.

#definition([Scaling functor and its boundary conventions])[
  For $r in [0, oo]$ the _scaling_ functor $r(-) : bold("CExtMet") -> bold("CExtMet")$ leaves the underlying set unchanged and rescales the distance,
  $ d_(r X)(x, x') = r dot d_X (x, x'), $
  under the extended-arithmetic conventions $r dot oo = oo$ for $r > 0$ and $0 dot oo = 0$. A non-expansive map $r X -> Y$ is exactly an $r$-Lipschitz map $X -> Y$. At the two boundary scalars we fix:
  - $0 X := bold(1)$, the terminal one-point space, so that a $0$-sensitive variable is genuinely _discarded_ — the indiscrete metric $0 dot d_X$ is collapsed to the point (note $0 X$ is otherwise _not_ isomorphic to $bold(1)$);
  - $oo X$ is the ${0, oo}$-valued space with $d_(oo X)(x, x') = oo$ for $x eq.not x'$. Since $oo + oo = oo$, the diagonal $oo X -> oo X times.o oo X$ is non-expansive, so $oo X$ is _copyable_; this is what licenses the duplication of the recursion context in @def:guarded-fix and the rule (REC).
] <def:scaling>

#proposition([Scaling is strong monoidal in *CExtMet*])[
  Because the tensor distance of @def:extmet-cmon is the _untruncated_ sum $d_X + d_Y$, the scaling functor is _strong_ monoidal with no side conditions: for all $r, s in [0, oo]$,
  $ r(A times.o B) tilde.equiv r A times.o r B, quad (r s) A tilde.equiv r (s A), quad r bold(1) tilde.equiv bold(1), $
  since $r(d_A + d_B) = r d_A + r d_B$ and $(r s) d_A = r(s d_A)$ hold _on the nose_. This contrasts with the $1$-bounded category *CMet*, where truncation forces the corresponding comparison maps to be isomorphisms only under provisos such as $s <= 1$ or $r >= 1$ (cf. @cmethol, Thm. 1); in *CExtMet* that bookkeeping disappears, and the structural rules need no truncation-induced conditions.
] <def:scaling-monoidal>

#definition([Coproducts in *CExtMet*])[
  The coproduct $A + B$ has the disjoint union as underlying set, with the components kept maximally apart:
  - $d_(A + B)("inj"_1 a, "inj"_1 a') = d_A (a, a')$,
  - $d_(A + B)("inj"_2 b, "inj"_2 b') = d_B (b, b')$,
  - $d_(A + B)("inj"_1 a, "inj"_2 b) = oo$.
  The injections are isometries, and any pair of non-expansive maps $A ->^("inl") C$, $B ->^("inr") C$ copairs to a non-expansive $A + B -> C$. The $oo$-separation is _scale-invariant_, $r dot oo = oo$ for every $r > 0$, so the comparison $r(A + B) tilde.equiv r A + r B$ holds for all $r > 0$; it degenerates only at $r = 0$, which would merge the two components.
] <def:coproduct>

= Fixed points of non-expansive maps

Unlike $bold("Set")$, the category *CExtMet* does _not_ support general recursion: there is no non-expansive combinator $"fix" : (Y multimap Y) -> Y$, since an arbitrary self-map need not have any fixed point compatible with the metric structure. What *CExtMet* does admit, once one restricts to complete objects, is a _guarded_ form of recursion, in which the recursive occurrence is rescaled by a contraction factor $p < 1$.

#lemma([Guarded recursion in *CExtMet*])[
  Let $(Y, d_Y) in bold("CExtMet")$ be non-empty and _complete_ (every Cauchy net in $(Y, d_Y)$ converges), and let $p < 1$. Write $p Y$ for the object obtained by rescaling distances by $p$, so that a non-expansive map $p Y -> Y$ is the same datum as a $p$-Lipschitz map $Y -> Y$, i.e. a _$p$-contraction_. By Banach's fixed-point theorem, every such contraction has a unique fixed point in $Y$, and the assignment is non-expansive.
  $ "fix" : (p Y multimap Y) -> (1 - p) Y. $
] <def:guarded-fix>

More generally, for any $X in bold("CExtMet")$ and non-expansive $f : X times.o_p Y -> Y$, the partial fixed point
$ "fp"(f) : X -> Y, quad "fp"(f)(x) = "fix"(y |-> f(x, y)) $
is itself non-expansive.

#remark([Banach in the extended setting])[
  In an _extended_ metric the contraction iteration may start at infinite displacement, $d_Y (y_0, f(y_0)) = oo$, and then $d_Y (f^n y_0, f^(n+1) y_0) <= p^n dot oo = oo$ never decreases. Banach's theorem therefore applies _within each galaxy_, i.e. each maximal subspace on which distances are finite (the equivalence classes of $x tilde y arrow.l.r.double d(x, y) < oo$). A $p$-contraction maps each galaxy into itself and has a unique fixed point there, so $"fix"$ is well-defined; concretely this is guaranteed by working with the finite-moment Wasserstein space $cal(W)_p$ of @def:wasserstein-monad. The typing rule (FIX) is unaffected: it still only requires $p < 1$.
]


= Probability Measures

We introduce the Wasserstein monad $cal(W)_p$ with $p >= 1$ on *CExtMet* together with its algebraic presentation as the free interpolative barycentric algebra @FreeWassersteinAlgebras.


#definition([Wasserstein monad])[
  The _Wasserstein monad_ on *CExtMet* is the triple $(cal(W)_p, delta, m)$ defined as:
  - an endofunctor $cal(W)_p : bold("CExtMet") -> bold("CExtMet")$
    sending each object $(X, tau, d)$ to the space of Radon probability
    measures on $X$ with the Wasserstein distance, and each
    continuous-short map $f$ to its pushforward $mu mapsto mu compose f^(-1)$;
  - a unit operator $delta_X : X -> cal(W)_p X$ sending a point to the corresponding Dirac measure;
  - a join operator $mu_X : cal(W)_p cal(W)_p X -> cal(W)_p X$ given by the usual expectation;


  Subject to the laws:

  - unit:  $mu_X compose delta_(cal(W)_p X) = mu_X compose cal(W)_p delta_X = "id"_(cal(W)_p X)$
  - associativity: $mu_X compose m_(cal(W)_p X) = mu_X compose cal(W)_p mu_X$.
] <def:wasserstein-monad>


This monad has an algebraic presentation as the free  complete interpolative barycentric algebra @FreeWassersteinAlgebras, which we now define.

#definition([Interpolative barycentric algebra])[
  A _(complete) interpolative barycentric algebra_ in *CExtMet* is a metrically-complete object $X$ equipped with a family of non-expansive _convex combinations_
  $ amp.inv_p : p X times.o (1 - p) X -> X, quad p in (0, 1), $
  satisfying the equations
  - *(idempotence)* $x amp.inv_p x = x$;
  - *(commutativity)* $x amp.inv_p y = y amp.inv_(1 - p) x$;
  - *(associativity)* $(x amp.inv_p y) amp.inv_q z = x amp.inv_(p q) (y amp.inv_((q - p q) / (1 - p q)) z) quad$ provided $p < 1, q < 1$;
] <def:ib-algebra>

A homomorphism $f : X -> Y$ of IB algebras is a continuous-short map such that $f(x amp.inv_p y) = f(x) amp.inv_p f(y)$ for all $x, y in X$ and $p in (0, 1)$.

For every $X in bold("CExtMet")$, the space $cal(W)_p X$ is an interpolative barycentric algebra under the pointwise convex combination $mu amp.inv_p nu = p mu + (1 - p) nu$. It axiomatizing probabilistic choice by means of this binary convex combination operations ($plus.o_p$).




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



#remark([Softness lives on the logical entailment, not the typing judgement])[
  @def:holder is what lets the $p$-sum connective $plus.o.big^p$ pair soundly against its conjugate $plus.o.big^q$: a predicate aggregated with the $p$-sum may only be contracted against one aggregated with the conjugate $q$-sum, since the pairing is bounded only when $1 / p + 1 / q = 1$. For this reason softness is tracked as a grade on the entailment of the inner logic, and not on the term-level typing judgement.
]

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




// graded turnstile and soft connectives
#let ent(p) = $attach(tack.r, br: #p)$
#let psum(s) = $attach(plus.o, tr: #s)$
#let fa(s) = $attach(forall, tr: #s)$
#let ex(s) = $attach(exists, tr: #s)$

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

= Examples

== Properties of neural networks.

Given a neural network $cal(N): RR^m arrow.r RR^n$, the verification property usually takes the formof a Hoare triple $forall x in RR^. cal(W)(x) arrow.r cal(Q)(x)$, where $cal(W)$ and $cal(Q)$can be arbitrary properties $RR multimap bold(prop)$ obtained by using

#definition([$epsilon$-$delta$-robustness])[
  Given a neural network $N$ and a vector $v$, consider the specification that requires that for all inputs $x$ that are within $epsilon$ distance from $v$,
  the output of $cal(N)(x)$ should not deviate by more than $δ$ from $cal(N)(v)$:

  $
    forall x. |x - v| <= epsilon multimap |cal(N)(x) - cal(N)(v)| <= delta
  $
]

It can be used to avoid misclassifying images when only a few pixels are perturbed.

#example("A simple NN")[
  Consider the input value $x : RR^n$ and the weight and bias vectors: $W_1 : RR^(m times n), b_1 : RR^m, w_2 : RR^m, b_2 : RR$. A first hidden layer:
  #[
    #show math.equation.where(block: true): set align(left)
    $
      & "features" : RR^n -> RR^m \
      & "features"(x) = "relu"(W_1 x + b_1)
    $
  ]

  #[
    #show math.equation.where(block: true): set align(left)
    $
      & "logit" : RR^m -> RR \
      & "logit"(h) = w_2^top h + b_2
    $
  ]

  #[
    #show math.equation.where(block: true): set align(left)
    $
      & sigma : RR -> II \
      & sigma(z) = 1 / (1 + e^(-z))
    $
  ]

  #[
    #show math.equation.where(block: true): set align(left)
    $
      & "Bernoulli" : II -> cal(G)({0, 1}) \
      & "Bernoulli"(p) = p dot delta_1 + (1 - p) dot delta_0
    $
  ]

  The network factorize has:

  $ RR^n ->^("features") RR^m ->^("logit") RR ->^(sigma) II ->^("Bernoulli") cal(G)({0,1}) $

  #[
    #show math.equation.where(block: true): set align(left)
    $
      & "net" : RR^n -> cal(G)({0, 1}) \
      & "net"(x) = "Bernoulli"(sigma("logit"("features"(x)))) \
      & quad quad = "Bernoulli"(sigma(w_2^top "relu"(W_1 x + b_1) + b_2)) \
      & quad quad = sigma(w_2^top "relu"(W_1 x + b_1) + b_2) dot delta_1 + (1 - sigma(w_2^top "relu"(W_1 x + b_1) + b_2)) dot delta_0
    $
  ]
]

== Properties of neural networks.

#bibliography("refs.bib")
