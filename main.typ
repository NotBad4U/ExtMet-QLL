#import "lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#show: para-lipics.with(
  title: [Internal QLL in CExtMetTop],
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

= Preliminaries on metric spaces

A (1-bounded) metric space is a set $X$ equipped with a distance $d_X: X times X -> [0,1]$ satisfying:
- (reflexivity) $d_X (x,y) = 0$ if $x = y$
- (symmetry) $d_X (x, y) = d_X(y, x)$
- (triangular inequality) $d_X(x, z) <= d_X (x,y) + d_X (y,z)$

A function  $f: X -> Y$ between metric spaces is $r$-Lipschitz continuous , for $r >= 0$, if $r dot d_X (x_1, x_2) >= d_Y (f(x_1), f(x_2))$ for $x_1, x_2 in X$. A function is called  _non-expansive_ when $r = 1$ and a contraction
when $r < 1$ and $X = Y$. A metric  space is complete if all Cauchy sequences converge.


#definition([Extended metric space])[
  Extended metric structures, where extended metric spaces are sets $X$ endowed with a symmetric and triangular $d_X: X × X → [0,∞]$, with $d(x, y) = 0$ iff $x = y$.
  Extended distances arise in a natural way either by taking the supremum $sup |f(x)−f(y)|$ along
  a set $F$ of functions which separate the points of $X$, by construction of length distances and more generally by action minimization
] <def:ext-met>


#definition([The category of $bold("ExtMet")$])[
  The category $bold("CExtMet")$ of extended metric spaces is defined by the following data:
  - objects: extended metric spaces $(X, d_X)$, that is, pairs consisting of a set $X$ together with an extended distance $d_X : X times X -> [0, +oo]$ satisfying @def:ext-met.
  - morphisms: $phi : (X, d_X) -> (Y, d_Y)$ are _short maps_ (equivalently, non-expansive maps), that is, functions $phi : X -> Y$ such that:
    $ d_Y (phi(x), phi(x')) <= d_X (x, x') quad "for every " x, x' in X. $
  - composition: is the composition of functions, and the identity on $(X, d_X)$ is $id_X$, which is trivially short map.
]

*ExtMet* _is bicomplete_ since *ExtMetTop* (Extended metric topological spaces) is proven bicomplete @ecmt and another argument will be that *Ext*$Psi$*Met* is known bicomplete in the folklore and the full subcategory
inclusion *ExtMet* $arrow.hook$ *Ext*$Psi$*Met* is reflective (its left adjoint sends a pseudometric space $(X, d)$ to the metric quotient $(X slash tilde, [d])$, with $x tilde y$ iff $d(x, y) = 0$). A reflective subcategory is always closed under the limits that exist in the ambient category — the full inclusion is monadic and therefore creates limits — and inherits colimits from the ambient category by applying the reflector (Riehl, Prop. 4.5.15). In particular, whenever the ambient category is complete and cocomplete, so is the reflective subcategory; applied to *ExtMet* $arrow.hook$ *Ext*$Psi$*Met* this yields bicompleteness of *ExtMet*.

Therefore, products are computed on the underlying sets with the $sup$ distance:

$ d_(product_i X_i) ((x_i)_i, (y_i)_i) = sup d_(X_i) (x_i, y_i), $


#figure(
  caption: [Categories of (extended) metric spaces and topological spaces.],
  diagram(
    cell-size: 15mm,
    node-inset: 4pt,
    node((1, 0), [*Set*], label: "set"),
    node((0, 1), [*Top*], label: "top"),
    node((1, 1), [*PreExt*$Psi$*MetTop*], label: "pre-extended metric top"),
    node((2, 1), [*Ext*$Psi$*Met*], label: "extended metric"),
    node((0, 2), [*Tych*], label: "tychonoff"),
    node((1, 2), [*ExtMetTop*], label: "extended metric top"),
    node((2, 2), [*ExtMet*], label: "extended metric"),

    // Forgetful functors to Set
    edge((0, 1), (1, 0), $U$, "->"),
    edge((2, 1), (1, 0), $U$, "->"),

    // Forgetful functors out of PreExtΨMetTop
    edge((1, 1), (0, 1), $U$, "->"),
    edge((1, 1), (1, 0), $U$, "->"),
    edge((1, 1), (2, 1), $U$, "->"),

    // Full-subcategory inclusions
    edge((0, 2), (0, 1), $iota$, "hook->"),
    edge((2, 2), (2, 1), $iota$, "hook->"),

    // emt ⊣ ι  (ExtMetTop is a reflective subcategory of PreExtΨMetTop)
    edge((1, 1), (1, 2), $"emt"$, "->", bend: +25deg, label-side: left),
    edge((1, 2), (1, 1), $iota$, "hook->", bend: +25deg, label-side: left),

    // 𝔇∞ ⊣ U∞  (Tych is a coreflective subcategory of ExtMetTop)
    edge((0, 2), (1, 2), $frak(D)_oo$, "->", bend: +20deg, label-side: left),
    edge((1, 2), (0, 2), $U_oo$, "->", bend: +20deg, label-side: left),

    // T ⊣ U  (ExtMet is a coreflective subcategory of ExtMetTop)
    edge((2, 2), (1, 2), $T$, "->", bend: +20deg, label-side: left),
    edge((1, 2), (2, 2), $U$, "->", bend: +20deg, label-side: left),
  ),
)

Equalizers are subspaces carrying the restricted distance, coproducts are disjoint unions where points in distinct components are placed at distance $+oo$, and coequalizers of $phi, psi : X arrows Y$ are obtained by quotienting $Y$ by the zig-zag (pseudo)distance

$ d([y], [y']) = inf sum_(i=1)^n d_Y (z_i, z'_i), $

where the infimum ranges over finite chains $z_1 = y$, $z'_n = y'$, with $z'_(i-1)$ identified to $z_i$ through the relation generated by $phi(x) tilde psi(x)$, and then collapsing points at zero distance to restore separation. By @def:ext-met every (co)limit in $bold("ExtMet")$ arises from the corresponding one in $bold("Set")$ carrying a canonical extended distance, mirroring the situation for ordinary (co)complete concrete categories.

#definition([Closed symmetric monoidal structure on $bold("ExtMet")$])[
  The category *ExtMet* carries a closed symmetric monoidal structure $(bold("ExtMet"), times.o, bold(1))$ given by:
  - Tensor product: For $(X, d_X), (Y, d_Y) in bold("ExtMet")$,
    $ (X, d_X) times.o (Y, d_Y) = (X times Y, #h(0.3em) d_X + d_Y), $
    with additive distance
    $ (d_X + d_Y)((x, y), (x', y')) = d_X (x, x') + d_Y (y, y'). $
  - Monoidal unit: The one-point space $bold(1) = ({*}, d_*)$ with $d_*(*,*) = 0$.
  - Internal hom: The object $[X, Y]$ is the set $bold("ExtMet")(X, Y)$ of short maps, equipped with the sup distance
    $ d_([X, Y])(phi, psi) = sup_(x in X) d_Y (phi(x), psi(x)) in [0, +oo]. $
  - Exponential adjunction: The bijection
    $ bold("ExtMet")(X times.o Y, Z) tilde.equiv bold("ExtMet")(X, [Y, Z]) $
    holds by currying: a map $f : X times Y -> Z$ is short with respect to $d_X + d_Y$ iff
    $ d_Z (f(x, y), f(x', y')) <= d_X (x, x') + d_Y (y, y'), $
    which is equivalent to requiring that each partial map $f(x, -) : Y -> Z$ be short and that $x |-> f(x, -)$ be short for the sup distance on $[Y, Z]$.
] <def:extmet-cmon>

The operator $X multimap Y$ denotes the set of non-expansive functions from $X$ to $Y$ endowed with point-wise supremum metric $d_(X multimap Y)(f, g) = sup_(x in X) d_Y (f(x), g(x))$. The counit of  the adjunction is function evaluation $"eval" : (X multimap Y) times.o X -> Y$.

Nonexpansive morphisms in CMet subsume the notion of Lipschitz continuity through the  rescaling functor $r X$which scalesdistance by a factor $r > 0$.

#definition([Extended metric-topological space])[
  An _extended metric-topological space_ (or _e.m.t. space_) is a triple $(X, tau, d)$ where $(X, tau)$ is a topological space and $(X, d)$ is an extended metric space in the sense of @def:ext-met, subject to two compatibility axioms. Writing $"LIP"_(b,1)(X, tau, d)$ for the set of bounded continuous-short maps $(X, tau, d) -> RR$:
  + $tau$ is the _initial topology_ of $"LIP"_(b,1)(X, tau, d)$ — equivalently, the coarsest topology on $X$ making every such map continuous;
  + $d$ can be _$tau$-recovered_ from these functions:
    $ d(x, y) = sup { abs(f(x) - f(y)) : f in "LIP"_(b,1)(X, tau, d) } quad "for every " x, y in X. $
] <def:extmettop-obj>

#definition([The category of $bold("ExtMetTop")$])[
  The category $bold("ExtMetTop")$ of extended metric-topological spaces is defined by the following data:
  - objects: e.m.t. spaces $(X, tau, d)$ in the sense of @def:extmettop-obj.
  - morphisms: $phi : (X, tau_X, d_X) -> (Y, tau_Y, d_Y)$ are _continuous-short maps_, that is, functions $phi : X -> Y$ that are simultaneously continuous $(X, tau_X) -> (Y, tau_Y)$ and short $(X, d_X) -> (Y, d_Y)$.
  - composition: is the composition of functions, and the identity on $(X, tau, d)$ is $id_X$, which is trivially a continuous-short map.
] <def:extmettop>

$bold("ExtMetTop")$ _is bicomplete_, by an argument analogous to the one used for $bold("ExtMet")$: @ecmt exhibits $bold("ExtMetTop")$ as a reflective subcategory of $bold("PreExt")Psi bold("MetTop")$, which is itself bicomplete, with reflector the _e.m.t.-fication_ functor $"emt"$ .

#lemma([Closed symmetric monoidal structure on $bold("ExtMetTop")$])[
  TODO
] <def:extmettop-cmon>


= Fixed points of non-expansive maps

Unlike $bold("Set")$, the category *ExtMetTop* does _not_ support general recursion: there is no non-expansive combinator $"fix" : (Y multimap Y) -> Y$, since an arbitrary self-map need not have any fixed point compatible with the metric structure. What *ExtMetTop* does admit, once one restricts to complete objects, is a _guarded_ form of recursion, in which the recursive occurrence is rescaled by a contraction factor $p < 1$.

#lemma([Guarded recursion in *ExtMetTop*])[
  Let $(Y, d_Y) in bold("ExtMetTop")$ be non-empty and _complete_ (every Cauchy net in $(Y, d_Y)$ converges), and let $p < 1$. Write $p Y$ for the object obtained by rescaling distances by $p$, so that a non-expansive map $p Y -> Y$ is the same datum as a $p$-Lipschitz map $Y -> Y$, i.e. a _$p$-contraction_. By Banach's fixed-point theorem, every such contraction has a unique fixed point in $Y$, and the assignment is non-expansive.
  $ "fix" : (p Y multimap Y) -> (1 - p) Y. $
] <def:guarded-fix>

More generally, for any $X in bold("ExtMetTop")$ and non-expansive $f : X times.o p Y -> Y$, the partial fixed point
$ "fp"(f) : X -> Y, quad "fp"(f)(x) = "fix"(y |-> f(x, y)) $
is itself non-expansive.


= Probability Measures

We introduce the Kantorovich monad $bold(𝔇)_∞$ on *ExtMetTop* together with its algebraic presentation as the free interpolative barycentric algebra.

A (Borel) probability measure $mu$ on an object $(X, tau, d) in bold("ExtMetTop")$ is _Radon_ when, for every Borel set $E subset.eq X$, the quantity $mu(E)$ is the supremum of $mu(K)$ over all $tau$-compact subsets $K subset.eq E$. Typical examples include Dirac measures $delta_x$, finitely-supported measures, the Borel restriction of Lebesgue measure on $[0,1]$, and every Borel probability measure on a complete separable (extended) metric space.

A _coupling_ between two probability measures $mu, nu$ on $X$ is a probability measure $omega$ on $X times X$ whose left and right marginals are respectively $mu$ and $nu$, i.e.
$ omega(E times X) = mu(E) quad "and" quad omega(X times E) = nu(E) $
for every Borel set $E subset.eq X$. The product measure $mu times nu$ is always a coupling, and couplings of Radon measures are themselves Radon.

For $X in bold("ExtMetTop")$, let $bold(𝔇)_∞ X$ denote the set of Radon probability measures on $X$ equipped with the _Kantorovich distance_
$
  d_(bold(𝔇)_∞ X) (mu, nu) = inf_omega integral d_X (x, x') #h(0.3em) omega(d x, d x'),
$
where $omega$ ranges over the couplings of $mu$ and $nu$. Since $d_X$ takes values in $[0, +oo]$, so does $d_(bold(𝔇)_∞ X)$: two measures supported on different finite-distance components of $X$ sit at distance $+oo$. Whenever $X$ is metrically complete, so is $bold(𝔇)_∞ X$.


#definition([Kantorovich monad])[
  The _Kantorovich monad_ on *ExtMetTop* is the triple $(bold(𝔇)_∞, delta, m)$ defined as:
  - an endofunctor $bold(𝔇)_∞ : bold("ExtMetTop") -> bold("ExtMetTop")$
    sending each object $(X, tau, d)$ to the space of Radon probability
    measures on $X$ with the Kantorovich distance, and each
    continuous-short map $f$ to its pushforward $mu mapsto mu compose f^(-1)$;
  - a unit operator $delta_X : X -> bold(𝔇)_∞ X$ sending a point to the corresponding Dirac measure;
  - a join operator $mu_X : bold(𝔇)_∞ bold(𝔇)_∞ X -> bold(𝔇)_∞ X$ given by the usual expectation;


  Subject to the laws:

  - unit:  $mu_X compose delta_(bold(𝔇)_∞ X) = mu_X compose bold(𝔇)_∞ delta_X = "id"_(bold(𝔇)_∞ X)$
  - associativity: $mu_X compose m_(bold(𝔇)_∞ X) = mu_X compose bold(𝔇)_∞ mu_X$.
] <def:kantorovich-monad>


This monad has an algebraic presentation as the free  complete interpolative barycentric algebra @FreeWassersteinAlgebras, which we now define.

#definition([Interpolative barycentric algebra])[
  A _(complete) interpolative barycentric algebra_ in *ExtMetTop* is a metrically-complete object $X$ equipped with a family of non-expansive _convex combinations_
  $ plus.o_p : p X attach(times.o, bl: 1, br: 1) (1 - p) X -> X, quad p in (0, 1), $
  satisfying the equations
  - *(idempotence)* $x plus.o_p x = x$;
  - *(commutativity)* $x plus.o_p y = y plus.o_(1 - p) x$;
  - *(associativity)* $(x plus.o_p y) plus.o_q z = x plus.o_(p q) (y plus.o_((q - p q) / (1 - p q)) z)$.
  A _homomorphism_ $f : X -> Y$ of IB algebras is a continuous-short map such that $f(x plus.o_p y) = f(x) plus.o_p f(y)$ for all $x, y in X$ and $p in (0, 1)$.
] <def:ib-algebra>

As shown in @def:ib-algebra, the scaling factor $p$ on the arguments of $plus.o_p$ is precisely what turns the standard barycentric inequality $d(x plus.o_p y, x' plus.o_p y') <= p #h(0.2em) d(x, x') + (1 - p) #h(0.2em) d(y, y')$ into a typing discipline: incorporating the Lipschitz constants directly into the type of $plus.o_p$ allows the remaining axioms to be stated purely as equations, and turns many probabilistic processes into guarded fixed points (cf. @def:guarded-fix).

For every $X in bold("ExtMetTop")$, the space $bold(𝔇)_∞ X$ is an interpolative barycentric algebra under the pointwise convex combination $mu plus.o_p nu = p mu + (1 - p) nu$. It axiomatizing probabilistic choice by means of this binary convex combination operations ($plus.o_p$).

= A calculus for ExtMetTop

We now define a calculus for programming in the category *ExtMetTop*.

== Syntax

The syntax is based on a simply-typed $lambda$-calculus with products and sums, extended with  primitives for probabilistic distributions, recursion, and fixed points.

$
  M, N ::= & x | () | lambda x. M | M #h(0.3em) N | chevron.l M, N chevron.r | pi_1 M | pi_2 M | "let" x = M "in" N \
         | & #h(0.5em) "inl" M | "inr" M | "case" M "of" "inl" x => N | "inr" y => N \
         | & #h(0.5em) "fix" x. M | (M, N) | delta M | M plus.o_p N | 0 | "succ"(M)
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

At first glance, $"Prop"_plus.o$ does not fit in *ExtMetTop*: its carrier $[-infinity, +infinity]$ admits negative differences, so the candidate distance $|u - v|$ fails the axioms of @def:ext-met.
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
  log : "Prop"_times.o attach(multimap, br:1) "Prop"_plus.o
  quad quad
  exp : "Prop"_plus.o attach(multimap, br:1) "Prop"_times.o
$
Both carry sensitivity $1$ because, under $d_("log")$ on $"Prop"_times.o$, they
are isometries. The following judgmental equalities axiomatize the isomorphism:

#figure(
  caption: [Napier isomorphism axioms.],
  table(
    columns: (1fr, 1fr),
    align: (left, left),
    stroke: none,
    table.header(
      [$"Prop"_times.o arrow "Prop"_plus.o$],
      [$"Prop"_plus.o arrow "Prop"_times.o$],
    ),
    $log(exp u) equiv u$,                                           $exp(log a) equiv a$,
    $log(a times.o.big b) equiv log a + log b$,                      $exp(u + v) equiv exp u times.o.big exp v$,
    $log(a attach(times.o.big, tr: *) b) equiv log a attach(+, tr: *) log b$, $exp(u attach(+, tr: *) v) equiv exp u attach(times.o.big, tr: *) exp v$,
    $log 1 equiv 0$,                                                 $exp 0 equiv 1$,
    $log bot_times.o equiv bot_plus.o$,                              $exp bot_plus.o equiv bot_times.o$,
    $log top_times.o equiv top_plus.o$,                              $exp top_plus.o equiv top_times.o$,
    $log(a^*) equiv -(log a)$,                                       $exp(-u) equiv (exp u)^*$,
    $log(a multimap b) equiv log b - log a$,                         $exp(v - u) equiv exp u multimap exp v$,
  ),
) <fig:napier-axioms>

== semantics

#bibliography("refs.bib")
