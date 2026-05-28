#import "lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#show: para-lipics.with(
  title: [Internal QLL in CExtMet],
  title-running: [Dummy short title],
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
  copyright: [Jane Open Access and Joan R. Public],
  keywords: [Dummy keyword],
)

= Preliminaries on extended Reals numbers

= Preliminaries on extended metric spaces

// A function  $f: X -> Y$ between metric spaces is $r$-Lipschitz continuous , for $r >= 0$, if $r dot d_X (x_1, x_2) >= d_Y (f(x_1), f(x_2))$ for $x_1, x_2 in X$. A function is called  _non-expansive_ when $r = 1$ and a contraction
// when $r < 1$ and $X = Y$. A metric  space is complete if all Cauchy sequences converge.


#definition([Extended metric space])[
  Extended metric spaces are sets $X$ endowed with the distance function $d_infinity: X × X → [0,∞]$ as to allow the distance function d to attain the value ∞, i.e. distances are non-negative numbers on the extended real line $overline(RR)$.

] <def:ext-met>

#definition([Bounded extended metric])[
  Every extended metric can be replaced by a topologically equivalent real-valued metric i.e $d in RR^2 -> [0, infinity)$. It suffices to post-compose $d_infinity$ with a subadditive, monotonically increasing, bounded function vanishing at zero, e.g.

  - $d' (x, y) = frac(d_infinity (x, y), (1 + d_infinity (x, y))) quad "with" infinity / infinity = 1$
  - or  $d'' (x, y) = min(1, d_infinity (x, y))$,

  both of which take values in $[0, 1]$ and induce the same topology as $d_infinity$.
]<def:bounded-ext-met>

We will write $d_X$ instead of $d_infinity^X$ when it is clear from the context that we are talking about the extended metric on $X$.


#definition([r-Lipschitz continuity])[
  A function $f: X → Y$ between metric spaces is $r$-Lipschitz continuous, for $r ≥ 0$, if $r dot d_X (x, y) ≥ d_Y (f(x), f(y))$ for all $x, y ∈ X$. A function is called _non-expansive_ when $r = 1$ and a _contraction_ when $r < 1$ and $X = Y$.
]<def:lip-cont>

#proposition([cases of r-Lipschitz p-mean])[
  The $p$-mean function:
  $
    M_p(x_1, dots, x_n) := (frac(1, n) sum_(i=1)^n x_i^p)^(1/p)
  $
  on $[0, +oo)^n$ is non-expansive ($r = 1$) in the three closed-form cases $p = +oo$, $p = -oo$ and $p = 1$, where it degenerates to a lattice or affine operation:
  $
    M_(+oo)(x) = max x_i, quad M_(-oo)(x) = min x_i, quad M_1(x) = 1 / n sum_(i = 1)^n x_i.
  $
  The two extremal means are non-expansive because the lattice operations contract differences pointwise:
  $ |max x_i - max y_i| <= max |x_i - y_i| quad "and" quad |min x_i - min y_i| <= max |x_i - y_i|, $
  whereas for the arithmetic mean the triangle inequality gives
  $ |M_1(x) - M_1(y)| = |1 / n sum_(i = 1)^n (x_i - y_i)| <= 1 / n sum_(i = 1)^n |x_i - y_i| <= max |x_i - y_i|. $
  In each case the bounding quantity $max |x_i - y_i|$ is exactly the sup (Chebyshev) distance $d_oo (x, y)$, so $|M_p (x) - M_p (y)| <= d_oo (x, y)$. Hence for $p in {1, +oo, -oo}$ the $p$-mean is $1$-Lipschitz, i.e. non-expansive ($r = 1$) for $d_oo$, which establishes the claim.
]<def:lip-p-mean>

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

// Nonexpansive morphisms in CMet subsume the notion of Lipschitz continuity through the  rescaling functor $r X$which scalesdistance by a factor $r > 0$.

= Fixed points of non-expansive maps

Unlike $bold("Set")$, the category *CExtMet* does _not_ support general recursion: there is no non-expansive combinator $"fix" : (Y multimap Y) -> Y$, since an arbitrary self-map need not have any fixed point compatible with the metric structure. What *CExtMet* does admit, once one restricts to complete objects, is a _guarded_ form of recursion, in which the recursive occurrence is rescaled by a contraction factor $p < 1$.

#lemma([Guarded recursion in *CExtMet*])[
  Let $(Y, d_Y) in bold("CExtMet")$ be non-empty and _complete_ (every Cauchy net in $(Y, d_Y)$ converges), and let $p < 1$. Write $p Y$ for the object obtained by rescaling distances by $p$, so that a non-expansive map $p Y -> Y$ is the same datum as a $p$-Lipschitz map $Y -> Y$, i.e. a _$p$-contraction_. By Banach's fixed-point theorem, every such contraction has a unique fixed point in $Y$, and the assignment is non-expansive.
  $ "fix" : (p Y multimap Y) -> (1 - p) Y. $
] <def:guarded-fix>

More generally, for any $X in bold("CExtMet")$ and non-expansive $f : X times.o_p Y -> Y$, the partial fixed point
$ "fp"(f) : X -> Y, quad "fp"(f)(x) = "fix"(y |-> f(x, y)) $
is itself non-expansive.


= Probability Measures

We introduce the Wasserstein monad $cal(P)_p$ with $p >= 1$ on *CExtMet* together with its algebraic presentation as the free interpolative barycentric algebra @FreeWassersteinAlgebras.


#definition([Wasserstein monad])[
  The _Wasserstein monad_ on *CExtMet* is the triple $(cal(P)_p, delta, m)$ defined as:
  - an endofunctor $cal(P)_p : bold("CExtMet") -> bold("CExtMet")$
    sending each object $(X, tau, d)$ to the space of Radon probability
    measures on $X$ with the Wasserstein distance, and each
    continuous-short map $f$ to its pushforward $mu mapsto mu compose f^(-1)$;
  - a unit operator $delta_X : X -> cal(P)_p X$ sending a point to the corresponding Dirac measure;
  - a join operator $mu_X : cal(P)_p cal(P)_p X -> cal(P)_p X$ given by the usual expectation;


  Subject to the laws:

  - unit:  $mu_X compose delta_(cal(P)_p X) = mu_X compose cal(P)_p delta_X = "id"_(cal(P)_p X)$
  - associativity: $mu_X compose m_(cal(P)_p X) = mu_X compose cal(P)_p mu_X$.
] <def:wasserstein-monad>


This monad has an algebraic presentation as the free  complete interpolative barycentric algebra @FreeWassersteinAlgebras, which we now define.

#definition([Interpolative barycentric algebra])[
  A _(complete) interpolative barycentric algebra_ in *CExtMet* is a metrically-complete object $X$ equipped with a family of non-expansive _convex combinations_
  $ plus.o_p : p X attach(times.o, bl: 1, br: 1) (1 - p) X -> X, quad p in (0, 1), $
  satisfying the equations
  - *(idempotence)* $x plus.o_p x = x$;
  - *(commutativity)* $x plus.o_p y = y plus.o_(1 - p) x$;
  - *(associativity)* $(x plus.o_p y) plus.o_q z = x plus.o_(p q) (y plus.o_((q - p q) / (1 - p q)) z) quad$ provided $p < 1, q < 1$;
] <def:ib-algebra>

A homomorphism $f : X -> Y$ of IB algebras is a continuous-short map such that $f(x plus.o_p y) = f(x) plus.o_p f(y)$ for all $x, y in X$ and $p in (0, 1)$.

For every $X in bold("CExtMet")$, the space $cal(P)_p X$ is an interpolative barycentric algebra under the pointwise convex combination $mu plus.o_p nu = p mu + (1 - p) nu$. It axiomatizing probabilistic choice by means of this binary convex combination operations ($plus.o_p$).


= Hölder's inequality

Hölder's inequality is the analytic backbone of the duality between the $p$-sum and its harmonic dual, and it is what ultimately makes the $p$-Wasserstein distance of @def:wasserstein-monad a genuine extended metric. Fix two _conjugate exponents_ $p, q in [1, +oo]$, that is, exponents related by $1 / p + 1 / q = 1$, equivalently $p^* + q^* = 1$ in terms of the inversion $(-)^*$. Then for any two families $(a_i)_(i in I)$ and $(b_i)_(i in I)$ of extended non-negative reals,
$ sum_(i in I) a_i dot b_i <= (sum_(i in I) a_i^p)^(1 / p) dot (sum_(i in I) b_i^q)^(1 / q), $
where the boundary cases $p = 1$, $q = +oo$ (and symmetrically) are evaluated with the conventions $a times.o.big oo = oo$ for $a > 0$ and $0 times.o.big oo = 0$ fixed for the semiring $([0, +oo], plus.o.big, times.o.big)$. Geometrically, the inequality says that pairing a vector against another is bounded by the product of their $p$- and $q$-norms; the special case $p = q = 2$ is the Cauchy–Schwarz inequality. In the $p$-sum notation $plus.o.big_(i in I)^p a_i = (plus.o.big_(i in I) a_i^p)^(1 / p)$ introduced below, it states that the bilinear pairing is jointly bounded by the conjugate $p$- and $q$-sums,
$ plus.o.big_(i in I) (a_i times.o.big b_i) <= (plus.o.big_(i in I)^p a_i) times.o.big (plus.o.big_(i in I)^q b_i). $
From it one derives Minkowski's inequality, i.e. the triangle inequality for the $p$-sum, which in turn is exactly what is needed for the $p$-Wasserstein distance carried by the monad $cal(P)_p$ to satisfy the triangular axiom of @def:ext-met.

This is also what will let us encode the quantitative quantifiers: the $p$-indexed $forall^p$ and $exists^p$ are infinitary $p$-sums (respectively, harmonic $p$-sums) over the domain of quantification, and the non-expansiveness of the $p$-mean established in @def:lip-p-mean — extended from finite tuples to arbitrary index sets by Minkowski's inequality — guarantees that these quantifiers are themselves short maps, hence legitimate *CExtMet* morphisms.

= A calculus for CExtMet

We now define a calculus for programming in the category *CExtMet*.

== Syntax

The syntax is based on a simply-typed $lambda$-calculus with products and sums, extended with  primitives for probabilistic distributions, recursion, and fixed points.

$
  M, N ::= & x | () | lambda x. M | M #h(0.3em) N | chevron.l M, N chevron.r | pi_1 M | pi_2 M | "let" x = M "in" N \
         | & #h(0.5em) "inl" M | "inr" M | "case" M "of" "inl" x => N | "inr" y => N \
         | & #h(0.5em) "fix" x. M | (M, N) | delta M | M plus.o_p N | 0 | "succ"(M) | "rec"(u, (x,t).t, v)
$

There are two pairs constructors, $chevron.l M, N chevron.r$ and $(M, N)$, corresponding to the Cartesian and monoidal  products, respectively. The first one is eliminated using the projections $pi_i M$, whereas the second one is eliminated using $( "let" x = M "in" N)$. The term "()" is unit value. The injections "inl" and "inr" form expressions of sum type, which are eliminated by case analysis  $"case" M "of" "inl" x => N | "inr" y => N$.
The term $delta M$ denotes a distribution, and $M plus.o_p N$ the convex sumof $M$ and $N$. For convenience, we also include the natural numbers with constructors $0$ and $"succ"(M)$. Finally, $"fix" x. M$ is the “Banach” fixed point combinator.

The types of the calculus are defined by the grammar:
$
  A, B ::= & NN | 1 | A times B | A + B | A attach(times.o, bl: r, br: s) B | A multimap_r B | 𝔇_∞ A
$

essentially corresponding to the constructions of the previous section. Although rescaling of metric  spaces played a central role in the previous section, it is not a primitive type former in the calculus.
Instead, it is part of the tensor type $A attach(times.o, bl: r, br: s) B$ and function type $A multimap_r B$ constructors. This choice  was made to minimize the book keeping necessary for scalars in terms. Finally, $𝔇_∞ A$ is the Kantorovich type of Radon probability measures on $A$.

== Typing rules and properties

#figure(
  caption: [Typing rules.],
  [TODO],
)

== Semantics

= Logic

Consider the extended positive reals $[0, infinity]$ with their usual order $<=$. We define an ∗-autonomous poset $([0, +oo],1 , <=, times.o.big, (-)^*)$ where $a times.o.big b$ is defined by multiplication $a dot b$ extended with the rules
$forall a in (0, infinity], a times.o.big infinity = infinity$ and $0 times.o.big infinity = 0$. The inversion $(-)^*: [0, +oo]^(op) -> [0, infinity]$ yields a duality and defined as $forall a in (0, infinity), a^* = 1 / a$ extended with the rules $1/0 = infinity$ and $1/infinity=0$.

Now on the same poset $[0, infinity]$ consider the sum $plus.o.big$ trivially defined by $a plus.o.big b = a + b$ extended with the rules $a plus.o.big infinity = infinity$ for every $a in [0, infinity]$. The resulting structure is a commutative semiring, and the multiplication $times.o.big$ distributes over the sum $plus.o.big$.
The harmonic sum is defined as $a plus.o.big^* b := (a^* plus.o.big b^*)^*$. Choosing $0 < p < infinity$, we can conjugatet these operationsby exponentiation to obtain p-sum and harmonic p-sum:

$ plus.o.big_(i in I)^p a_i = (plus.o.big_(i in I) a_i^p)^(1/p) $ and $ plus.o.big_(i in I)^(p,*) a_i = (plus.o.big_(i in I) a_i^*)^(1/p)^* $.

We introduce a first order quantitative logic to reason about the terms of the calculus.
Qualitative truth values are valuated in the extended non-negative reals $[0, infinity]$.
To represent the two modes of qualitative logic with their different properties, we consider
the type $"Prop"_plus.o$ of additive where $a = 0$ 'false' and everything else 'true'.
$
  "Prop"_(plus.o) = (
    [-oo, +oo], <=,
    bot, top
    0,
    plus.big, attach(plus.big, tr: *),
    -(-),
    forall,
    exists
  )
$

and the type $"Prop"_times.o$ of multiplicative where we pick $<= 1$ as threshold of truth.

$
  "Prop"_(times.o) = (
    [0, +oo], <=,
    bot,
    top,
    1,
    times.o.big, attach(times.o.big, tr: *), multimap, (-)^*,
    plus.circle^p, plus.circle^(-p),
    forall^p, exists^p
  )
$

At first glance, $"Prop"_plus.o$ does not fit in *CExtMet*: its carrier $[-infinity, +infinity]$ admits negative differences, so the candidate distance $|u - v|$ fails the axioms of @def:ext-met.
This obstruction dissolves once we recognize that $"Prop"_plus.o$ and $"Prop"_times.o$ are two presentations of the same signature, related by the Napier isomorphism.
We therefore take $"Prop"_times.o$ as the primary internal definition and read $"Prop"_plus.o$ as its Napier-transported image.

#observation([On Lipschitz continuity for Napier isomorphism])[
  In the Euclidean metric, neither $log$ nor $exp$ is Lipschitz: $log'(x) = 1/x$
  blows up at $0$, and $exp'(u) = e^u$ blows up at $+oo$. The sensitivity-$1$
  typing above is sound only because $d_("log")$ on $"Prop"_times.o$ is defined
  as the pullback of the Euclidean distance along $log$, making both maps
  isometries by construction.
] <rem:napier-lipschitz>


We introduce two term-level constants witnessing the isomorphism:
$
  log : "Prop"_times.o attach(multimap, br: 1) "Prop"_plus.o
  quad quad
  exp : "Prop"_plus.o attach(multimap, br: 1) "Prop"_times.o
$
Both carry sensitivity $1$ because, under $d_("log")$ on $"Prop"_times.o$, they
are isometries. The following judgmental equalities axiomatize the isomorphism:

#figure(
  caption: [Napier isomorphism axioms.],
  table(
    columns: (1fr, 1fr),
    align: (left, left),
    stroke: none,
    table.header([$"Prop"_times.o arrow "Prop"_plus.o$], [$"Prop"_plus.o arrow "Prop"_times.o$]),
    $log(exp u) equiv u$, $exp(log a) equiv a$,
    $log(a times.o.big b) equiv log a + log b$, $exp(u + v) equiv exp u times.o.big exp v$,
    $log(a attach(times.o.big, tr: *) b) equiv log a attach(+, tr: *) log b$,
    $exp(u attach(+, tr: *) v) equiv exp u attach(times.o.big, tr: *) exp v$,

    $log 1 equiv 0$, $exp 0 equiv 1$,
    $log bot_times.o equiv bot_plus.o$, $exp bot_plus.o equiv bot_times.o$,
    $log top_times.o equiv top_plus.o$, $exp top_plus.o equiv top_times.o$,
    $log(a^*) equiv -(log a)$, $exp(-u) equiv (exp u)^*$,
    $log(a multimap b) equiv log b - log a$, $exp(v - u) equiv exp u multimap exp v$,
  ),
) <fig:napier-axioms>

== semantics

= Examples

== Properties of neural networks.

Given a neural network $cal(N): RR^m arrow.r RR^n$, the verification property usually takes the formof a Hoare triple $forall x in RR^. cal(P)(x) arrow.r cal(Q)(x)$, where $cal(P)$ and $cal(Q)$can be arbitrary properties $RR multimap bold("Prop")$ obtained by using

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
