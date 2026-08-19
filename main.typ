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
Truth, FLTL
Many QLs are based on intervals of real numbers such as [0,∞], used in QLL.
Besides standard operations such as multiplication ⊗, we require the notion of comultiplication $times^*$ and p-sums $plus.o^p$, where $p eq.not 0$.
Comultiplication $a times.o^* b := (a^(−1) times.o b^(−1))^(−1)$ only differs from multiplication for $a= 0$ and $b= infinity$.

For ML applications, it is desirable to have operations that are differentiable and componentwise strictly increasing.
These are also referred to as _soft_ operations, in contrast to $max$ and $min$, which are referred to as _hard_ operations.
Due to being soft, p-sums $a plus.o^p b:= (a^p + b^p)^(1/p)$, originally applied to QLs in Yager logic, have recently gained importance and are used in QLL, for instance.
A key relation we are currently mechanising is that $plus.o^p$ converges to the binary maximum function as $p -> infinity$.

#notations[p-sum large operator and its harmonic dual][
  On the left the $p$-sum, and on the right its harmonic (De Morgan) dual, obtained by conjugating with the involution $a |-> a^* = 1 \/ a$:
  $ plus.o.big_(i in I)^p a_i = (sum_(i in I) a_i^p)^(1/p) quad quad "and" quad quad plus.o.big_(i in I)^(p,*) a_i = ((sum_(i in I) (a_i^*)^p)^(1/p))^* = (sum_(i in I) a_i^(-p))^(-1/p). $
  The binary case of the harmonic dual at exponent $1$ is the _harmonic sum_ of two grades,
  $ p plus.o^* q := (p^(-1) + q^(-1))^(-1), quad "i.e." quad 1/(p plus.o^* q) = 1/p + 1/q, $
  which is the operation under which entailment grades compose (@sec:entailment). Note $plus.o^*$ is the dual of _addition_; it is distinct from the comultiplication $times.o^*$ above, the dual of multiplication.
]
#definition([Graded Hölder inequality and conjugate exponents])[
  For _all_ exponents $p, q in (0, +oo]$, the generalized Hölder inequality @holder-inequality bounds the pairing of two families at the composite grade $p plus.o^* q$:
  $ plus.o.big_(i in I)^(p plus.o^* q) (a_i times.o b_i) <= (plus.o.big_(i in I)^p a_i) times.o (plus.o.big_(i in I)^q b_i). $
  No relation between $p$ and $q$ is required: any two grades compose, the composite simply being $p plus.o^* q$. The classical statement is the slice $p plus.o^* q = 1$: two exponents $p, q in [1, +oo]$ are _Hölder conjugates_ when $1/p + 1/q = 1$ (with $1/oo = 0$), so that $p = 1$ pairs with $q = oo$ and $p = q = 2$ is self-conjugate, and the left-hand side becomes the plain sum $sum_i a_i times.o b_i$.
] <def:holder>

= Preliminaries on extended metric spaces

// A function  $f: X -> Y$ between metric spaces is $r$-Lipschitz continuous , for $r >= 0$, if $r dot d_X (x_1, x_2) >= d_Y (f(x_1), f(x_2))$ for $x_1, x_2 in X$. A function is called  _non-expansive_ when $r = 1$ and a contraction
// when $r < 1$ and $X = Y$. A metric  space is complete if all Cauchy sequences converge.


#definition([Extended metric space])[
  An _extended metric space_ is a set $X$ endowed with a distance function $d_infinity: X × X → [0,∞]$ — the distance is allowed to attain the value $∞$, i.e. distances are non-negative numbers on the extended real line $overline(RR)$ — satisfying, for all $x, y, z in X$:
  - *(identity of indiscernibles)* $d_infinity (x, y) = 0 arrow.l.r.double x = y$;
  - *(symmetry)* $d_infinity (x, y) = d_infinity (y, x)$;
  - *(triangle inequality)* $d_infinity (x, z) <= d_infinity (x, y) + d_infinity (y, z)$, where $+$ is extended addition on $[0, ∞]$ (so the inequality is vacuous when the right-hand side is $∞$).
  The relation $x tilde y arrow.l.r.double d_infinity (x, y) < ∞$ is an equivalence; its classes are called the _galaxies_ of $X$. Each galaxy is an ordinary metric space, and distinct galaxies lie at distance $∞$ from one another.
] <def:ext-met>

#remark([Bounded extended metrics — and why we do not use them])[
  Every extended metric can be replaced by a topologically equivalent bounded metric $d' : X times X -> [0, 1]$: it suffices to post-compose $d_infinity$ with a subadditive, monotonically increasing, bounded function vanishing at zero, e.g.

  - $d' (x, y) = frac(d_infinity (x, y), (1 + d_infinity (x, y))) quad "with" infinity / infinity = 1$
  - or  $d'' (x, y) = min(1, d_infinity (x, y))$,

  both of which take values in $[0, 1]$ and induce the same topology (indeed the same uniformity) as $d_infinity$. However, the equivalence is only topological, _not_ Lipschitz: truncation changes which maps are non-expansive and destroys the scaling structure of the next section. This remark therefore cannot be used to transfer results from the $1$-bounded setting of @cmethol; the category *CExtMet* below is genuinely different from *CMet*, and that difference is the point of this work.
]<def:bounded-ext-met>

We will write $d_X$ instead of $d_infinity^X$ when it is clear from the context that we are talking about the extended metric on $X$.


#definition([r-Lipschitz continuity])[
  A function $f: X → Y$ between metric spaces is $r$-Lipschitz continuous, for $r ≥ 0$, if $r dot d_X (x, y) ≥ d_Y (f(x), f(y))$ for all $x, y ∈ X$. A function is called _non-expansive_ when $r = 1$ and a _contraction_ when $r < 1$ and $X = Y$.
]<def:lip-cont>

#definition([The category of $bold("CExtMet")$])[
  The category $bold("CExtMet")$ of complete extended metric spaces is defined by the following data:
  - objects: _non-empty complete_ extended metric spaces $(X, d_X)$, that is, sets $X$ together with an extended distance $d_X : X times X -> [0, +oo]$ satisfying @def:ext-met, such that $X eq.not emptyset$ and every Cauchy sequence in $(X, d_X)$ converges (equivalently: every galaxy is a complete metric space, since a Cauchy sequence has eventually finite mutual distances and so eventually stays in a single galaxy);
  - morphisms: $phi : (X, d_X) -> (Y, d_Y)$ are _short maps_ (equivalently, non-expansive maps), that is, functions $phi : X -> Y$ such that:
    $ d_Y (phi(x), phi(x')) <= d_X (x, x') quad "for every " x, x' in X; $
  - composition: is the composition of functions, and the identity on $(X, d_X)$ is $id_X$, which is trivially a short map.
  Non-emptiness mirrors the convention of @cmethol for *CMet*; it is what allows Banach's theorem (@def:guarded-fix) to be applied to the interpretation of every type. All type formers of the calculus preserve it.
]

The category has binary _products_: $X times Y$ is the cartesian product with the pointwise maximum distance $d_(X times Y)((x, y), (x', y')) = max(d_X (x, x'), d_Y (y, y'))$, under which the projections and the pairing $chevron.l f, g chevron.r$ of short maps are short; it is complete and non-empty when $X, Y$ are, and $"diam"(X times Y) = max("diam" X, "diam" Y)$. Alongside it lives the monoidal tensor:

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
  All three constructions land in *CExtMet*: $X times.o Y$ is complete because a Cauchy sequence of pairs is Cauchy componentwise; $[X, Y]$ is complete because a sup-Cauchy sequence of short maps converges pointwise to a short map, uniformly on each galaxy; and non-emptiness is preserved ($[X, Y]$ contains the constant maps).
] <def:extmet-cmon>

The operator $X multimap Y$ denotes the set of non-expansive functions from $X$ to $Y$ endowed with point-wise supremum metric $d_(X multimap Y)(f, g) = sup_(x in X) d_Y (f(x), g(x))$. The counit of  the adjunction is function evaluation $"eval" : (X multimap Y) times.o X -> Y$.

#definition([Scaling functor and its boundary conventions])[
  For $r in (0, oo]$ the _scaling_ functor $r(-) : bold("CExtMet") -> bold("CExtMet")$ leaves the underlying set unchanged and rescales the distance,
  $ d_(r X)(x, x') = r dot d_X (x, x'), $
  under the extended-arithmetic conventions $r dot oo = oo$ for $r > 0$ and $0 dot oo = 0$. For $r in (0, oo]$ a non-expansive map $r X -> Y$ is exactly an $r$-Lipschitz map $X -> Y$. At the two boundary scalars:
  - $0 X := bold(1)$, the terminal one-point space, so that a $0$-sensitive variable is genuinely _discarded_. This redefinition is _forced_, not a convention, for any $X$ with at least two points: $(X, 0 dot d_X)$ then has distinct points at distance $0$, violating identity of indiscernibles, so it is not an object of *CExtMet* at all (for singleton $X$ the two definitions already agree). At $r = 0$ the underlying set does change, and $0 f$ is the unique map $bold(1) -> bold(1)$.
  - $oo X$ is the ${0, oo}$-valued space with $d_(oo X)(x, x') = oo$ for $x eq.not x'$ — which is exactly $oo dot d_X$ by identity of indiscernibles. Since $oo + oo = oo$, the diagonal $oo X -> oo X times.o oo X$ is non-expansive, so $oo X$ is _copyable_; this is what licenses the duplication of the recursion context in the rule (REC).
] <def:scaling>

#proposition([Scaling is strong monoidal in *CExtMet*])[
  Because the tensor distance of @def:extmet-cmon is the _untruncated_ sum $d_X + d_Y$, the scaling functor is _strong_ monoidal with no side conditions: for all $r, s in [0, oo]$,
  $ r(A times.o B) tilde.equiv r A times.o r B, quad (r s) A tilde.equiv r (s A), quad r bold(1) tilde.equiv bold(1). $
  For $r, s in (0, oo]$ the comparison maps are _identities_ on the underlying sets, since $r(d_A + d_B) = r d_A + r d_B$ and $(r s) d_A = r(s d_A)$ hold on the nose in $[0, oo]$ (including $r = oo$, and all mixed edge cases of $(r s) A tilde.equiv r(s A)$ under $0 dot oo = 0$). At $r = 0$ the comparisons are the canonical isomorphisms of one-point spaces ($0(A times.o B) = bold(1) tilde.equiv bold(1) times.o bold(1) = 0 A times.o 0 B$ by terminality, not by distance arithmetic, since $0 X$ is redefined). This contrasts with the $1$-bounded category *CMet*, where truncation forces the comparison maps $beta_(r,s,A) : (r s)A -> r(s A)$ and $m_(r,A,B) : r A times.o r B -> r(A times.o B)$ to be isomorphisms only under provisos such as $s <= 1$ or $r >= 1$ (cf. @cmethol, Thm. 1); in *CExtMet* that bookkeeping disappears, and the structural rules need no truncation-induced conditions.
] <def:scaling-monoidal>

#definition([Coproducts in *CExtMet*])[
  The coproduct $A + B$ has the disjoint union as underlying set, with the components kept maximally apart:
  - $d_(A + B)("inj"_1 a, "inj"_1 a') = d_A (a, a')$,
  - $d_(A + B)("inj"_2 b, "inj"_2 b') = d_B (b, b')$,
  - $d_(A + B)("inj"_1 a, "inj"_2 b) = oo$.
  The injections are isometries, and any pair of non-expansive maps $A ->^("inl") C$, $B ->^("inr") C$ copairs to a non-expansive $A + B -> C$. The $oo$-separation is _scale-invariant_, $r dot oo = oo$ for every $r > 0$, so the comparison $r(A + B) tilde.equiv r A + r B$ holds for all $r > 0$; it degenerates only at $r = 0$, which would merge the two components.
] <def:coproduct>

= Fixed points of non-expansive maps

Unlike $bold("Set")$, the category *CExtMet* does _not_ support general recursion: there is no non-expansive combinator $"fix" : (Y multimap Y) -> Y$, since an arbitrary self-map need not have any fixed point compatible with the metric structure. What *CExtMet* does admit is a _guarded_ form of recursion, in which the recursive occurrence is rescaled by a contraction factor $p < 1$ — but, unlike in the $1$-bounded setting of @cmethol, guardedness alone is _not_ enough: infinite distances make the contraction condition vacuous across galaxies.

#lemma([Banach in the extended setting, galaxy-wise])[
  Let $(Y, d_Y) in bold("CExtMet")$ and $p in (0, 1)$ (the boundary $p = 0$ is trivial via the convention $0 Y := bold(1)$: a point of $Y$, which is its own fixed point). A non-expansive map $f : p Y -> Y$ is a map with $d_Y (f y, f y') <= p dot d_Y (y, y')$ under extended arithmetic; this inequality is _vacuous_ on pairs at distance $oo$ (since $p dot oo = oo$), so $f$ need not be a contraction in the classical sense. What holds is:
  - $f$ maps the galaxy $G(y)$ of any point into the galaxy $G(f y)$ — _not_ necessarily into $G(y)$ itself;
  - $f$ has a fixed point iff $d_Y (y_0, f y_0) < oo$ for some $y_0$ (equivalently, iff some galaxy is $f$-invariant); in that case $G(y_0)$ is $f$-invariant, closed, hence complete, and classical Banach gives a unique fixed point in it, at distance at most $d_Y (y_0, f y_0) \/ (1 - p)$ from $y_0$;
  - uniqueness holds only _per invariant galaxy_: $f$ may fix several galaxies and have one fixed point in each.
] <def:guarded-fix>

#remark([Why a restriction is necessary])[
  Both existence and uniqueness genuinely fail on multi-galaxy objects. On $Y = {a, b}$ with $d(a, b) = oo$ — which is exactly $⟦1 + 1⟧$ under @def:coproduct — the _swap_ map satisfies $d("swap" thin a, "swap" thin b) = oo <= p dot oo$, so it is non-expansive $p Y -> Y$, yet has _no_ fixed point; the _identity_ is likewise non-expansive $p Y -> Y$ and has _two_. A finite-displacement premise alone does not restore uniqueness either: $y |-> y\/2$ on $RR + RR$ has one fixed point in each copy. Hence there is no non-expansive combinator $"fix" : (p Y multimap Y) -> (1-p) Y$ on arbitrary $Y in bold("CExtMet")$, and the typing rule (FIX) must carry a restriction on its type.
] <rem:fix-fails>

#definition([Banach types])[
  Call an object of *CExtMet* _bounded_ when its diameter is finite; a bounded object is a single galaxy, so @def:guarded-fix applies to it unconditionally: every non-expansive $f : p Y -> Y$ has a unique fixed point, and the assignment
  $ "fix" : (p Y multimap Y) -> (1 - p) Y $
  is well-defined and non-expansive by the standard estimate $(1-p) dot d("fix" f, "fix" g) <= d_(p Y multimap Y)(f, g)$. The _Banach types_ are the fragment of the type grammar whose interpretations are bounded:
  $ B, B' ::= 1 | NN | B times B' | B attach(times.o, bl: r, br: s) B' | A multimap_r B | cal(W) B, $
  where the _tensor_ scalars are finite, $r, s < oo$, while the domain $A$ and the scalar $r$ of the hom are arbitrary ($r in [0, oo]$: scaling the _domain_ cannot unbound the hom, whose diameter is at most $"diam" thin B$). Indeed $bold(1)$ and the $1$-discrete $NN$ are bounded; products (max metric) and finite-scalar tensors (sum metric) of bounded spaces are bounded; $d_(A multimap_r B) <= "diam" thin B$; and the Kantorovich distance on $cal(W) B$ is at most $"diam" thin B$. The coproduct $A + B$ (components $oo$-separated) and $oo$-scaled _tensors_ are never bounded and are excluded. In *CMet* every object is $1$-bounded, so no such restriction is visible there; it is the price of the extended setting, paid exactly at (FIX).
] <def:banach-types>

More generally, for $X in bold("CExtMet")$ and non-expansive $f : (1-p) X times.o p Y -> Y$ with $Y$ bounded, the partial fixed point
$ "fp"(f) : X -> Y, quad "fp"(f)(x) = "fix"(y |-> f(x, y)) $
is itself non-expansive (cf. @cmethol, Prop. 2). The $(1-p)$ rescaling of $X$ is needed: from an $f$ that is merely non-expansive on $X times.o p Y$ one only gets that $"fp"(f)$ is $1\/(1-p)$-Lipschitz, as $f(x, y) = x + p y$ on $RR$ shows, where $"fp"(f)(x) = x \/ (1 - p)$.


= Probability Measures

We introduce the _Kantorovich_ (order-$1$ Wasserstein) monad $cal(W)$ on *CExtMet* together with its algebraic presentation as the free complete interpolative barycentric algebra @FreeWassersteinAlgebras. The restriction to order $1$ is not cosmetic: it is forced by the graded typing of probabilistic choice (@rem:why-order-one).

#definition([Kantorovich monad])[
  The _Kantorovich monad_ on *CExtMet* is the triple $(cal(W), delta, m)$ defined as:
  - an endofunctor $cal(W) : bold("CExtMet") -> bold("CExtMet")$
    sending each object $(X, d)$ to the space of Radon probability
    measures on $X$ (with its metric topology) equipped with the Kantorovich distance
    $ d_(cal(W) X)(mu, nu) = inf_omega integral d_X (x, x') thin omega ("d"x, "d"x') in [0, oo], $
    the infimum over couplings $omega$ of $(mu, nu)$ — the value $oo$ is allowed, and legitimate in *CExtMet* — and each short map $f$ to its pushforward $mu mapsto mu compose f^(-1)$;
  - a unit $delta_X : X -> cal(W) X$ sending a point to the corresponding Dirac measure;
  - a multiplication $m_X : cal(W) cal(W) X -> cal(W) X$ given by the barycentre (expectation);

  subject to the monad laws:

  - unit:  $m_X compose delta_(cal(W) X) = m_X compose cal(W) delta_X = "id"_(cal(W) X)$
  - associativity: $m_X compose m_(cal(W) X) = m_X compose cal(W) m_X$.
] <def:wasserstein-monad>

#lemma([$cal(W) X$ is an object of *CExtMet*])[
  For $X in bold("CExtMet")$, the pair $(cal(W) X, d_(cal(W) X))$ is a non-empty complete extended metric space: identity of indiscernibles holds for Radon measures; the triangle inequality follows from the gluing lemma, with everything reduced to the standard separable-complete theory by tightness of Radon measures; and completeness holds galaxy-wise (a Cauchy sequence eventually stays in a single galaxy of $cal(W) X$, where the classical completeness of Wasserstein spaces applies). Note that on an unbounded single-galaxy $X$ the space $cal(W) X$ genuinely has several galaxies — measures with and without finite first moment — which is unproblematic here precisely because *CExtMet* admits infinite distances.
] <lem:wx-object>

This monad has an algebraic presentation as the free complete interpolative barycentric algebra @FreeWassersteinAlgebras, which we now define.

#definition([Interpolative barycentric algebra])[
  A _(complete) interpolative barycentric algebra_ in *CExtMet* is an object $E$ equipped with a family of non-expansive _convex combinations_
  $ amp.inv_p : p E times.o (1 - p) E -> E, quad p in (0, 1), $
  satisfying the equations
  - *(idempotence)* $x amp.inv_p x = x$;
  - *(commutativity)* $x amp.inv_p y = y amp.inv_(1 - p) x$;
  - *(associativity)* $(x amp.inv_p y) amp.inv_q z = x amp.inv_(p q) (y amp.inv_((q - p q) / (1 - p q)) z) quad$ provided $p < 1, q < 1$;
] <def:ib-algebra>

A homomorphism $f : E -> F$ of IB algebras is a short map such that $f(x amp.inv_p y) = f(x) amp.inv_p f(y)$ for all $x, y in E$ and $p in (0, 1)$.

For every $X in bold("CExtMet")$, the space $cal(W) X$ is an interpolative barycentric algebra under the mixture $mu amp.inv_p nu = p mu + (1 - p) nu$: the required grading is exactly the coupling estimate $d_(cal(W) X)(mu amp.inv_p nu, mu' amp.inv_p nu') <= p dot d_(cal(W) X)(mu, mu') + (1-p) dot d_(cal(W) X)(nu, nu')$, obtained by mixing couplings. Unlike in the $1$-bounded setting, however, $cal(W) X$ is _not_ in general the free complete IB algebra on $X$: whole galaxies of $cal(W) X$ are unreachable from the Diracs — on $X = RR$, a measure with infinite first moment is at Kantorovich distance $oo$ from _every_ finitely supported measure (@lem:wx-object). Freeness holds for the reachable part:

#proposition([Free extension])[
  Let $cal(W)_0 X subset.eq cal(W) X$ be the closure of the finitely supported measures (equivalently, of the finite convex combinations of Diracs) — a closed, hence complete, subalgebra, and all of $cal(W) X$ when $X$ is bounded (tightness plus quantization on an $epsilon$-net of a near-full compact). Then $cal(W)_0 X$ is the _free_ complete IB algebra on $X$ (cf. @FreeWassersteinAlgebras; @cmethol, Prop. 4 — in the $1$-bounded case $cal(W)_0 = cal(W)$, which is why no such distinction is visible there): for every complete IB algebra $E$, $Gamma in bold("CExtMet")$ and $r < oo$, every non-expansive $f : Gamma times.o r X -> E$ extends uniquely to a non-expansive $macron(f) : Gamma times.o r cal(W)_0 X -> E$ that is an IB-homomorphism in its second argument. Existence extends $f$ from finite mixtures of Diracs by uniform continuity — this is where the side condition $r < oo$ is needed, precisely the proviso carried by the typing rule (LET) below; uniqueness holds because homomorphisms are determined on the finite mixtures and continuous on their closure. Since $delta$, pushforward and barycentre preserve the closure, $cal(W)_0$ is a submonad of $cal(W)$, and it is $cal(W)_0$ that interprets the type former $cal(W)$.
] <prop:free-ext>

#remark([Why order $1$])[
  For the order-$q$ Wasserstein distance with $q > 1$ the mixture is _not_ graded by $p$ and $1 - p$: the sharp estimate is
  $ W_q (mu amp.inv_p nu, thin mu' amp.inv_p nu) <= p^(1/q) dot W_q (mu, mu'), $
  and $p^(1/q) > p$ is attained — on $X = {x, y}$ with $d(x, y) = c$, take $mu = delta_x, mu' = delta_y, nu = nu' = delta_x$: the unique coupling gives $W_q = p^(1/q) c$, while the $p$-grading would demand $<= p c$. Accordingly, the free-algebra presentation for $q > 1$ in @FreeWassersteinAlgebras replaces the convex grading by the $q$-mean interpolation axiom. Since the typing rule ($amp.inv_p$) scales contexts by $p$ and $1 - p$, the calculus commits to $q = 1$. (We also reserve the letter $p$ for mixture weights and contraction factors from now on; the Wasserstein order is fixed at $1$ and no longer decorates $cal(W)$.)
] <rem:why-order-one>




= A calculus for CExtMet

We now define a calculus for programming in the category *CExtMet*.

== Syntax

The syntax is based on a simply-typed $lambda$-calculus with products and sums, extended with  primitives for probabilistic distributions, recursion, and fixed points.


// Term syntax grammar (reused in spreadsheet.typ)
#let term-syntax = $
  M, N ::= & x | () | lambda x. M | M #h(0.3em) N | chevron.l M, N chevron.r | pi_1 M | pi_2 M | "let" (x, y) = M "in" N | "let" x = M "in" N \
         | & #h(0.5em) "inj"_1 M | "inj"_2 M | "case" M "of" "inj"_1 x => N | "inj"_2 y => N \
         | & #h(0.5em) "fix" x. M | (M, N) | delta M | M amp.inv_p N | "zero" | "succ"(M) | "rec"(z, (x,y).s, n)
$

#term-syntax

There are two pairs constructors, $chevron.l M, N chevron.r$ and $(M, N)$, corresponding to the Cartesian and monoidal  products, respectively. The first one is eliminated using the projections $pi_i M$, whereas the second one is eliminated by pattern matching, $"let" (x, y) = M "in" N$. The term "()" is unit value. The injections $"inj"_1$ and $"inj"_2$ form expressions of sum type, which are eliminated by case analysis  $"case" M "of" "inj"_1 x => N | "inj"_2 y => N$.
The term $delta M$ denotes a distribution, $M amp.inv_p N$ the convex sum of $M$ and $N$, and $"let" x = M "in" N$ is the _sampling_ let, binding $x$ to a sample from the distribution $M$. For convenience, we also include the natural numbers with constructors $0$ and $"succ"(M)$. Finally, $"fix" x. M$ is the “Banach” fixed point combinator.

The types of the calculus are defined by the grammar:

#let types-syntax = $
  A, B ::= & NN | 1 | A times B | A + B | A attach(times.o, bl: r, br: s) B | A multimap_r B | cal(W) A
$

#types-syntax

essentially corresponding to the constructions of the previous section. Although rescaling of metric  spaces played a central role in the previous section, it is not a primitive type former in the calculus.
Instead, it is part of the tensor type $A attach(times.o, bl: r, br: s) B$ and function type $A multimap_r B$ constructors. This choice  was made to minimize the book keeping necessary for scalars in terms. Finally, $cal(W) A$ is the Kantorovich type of probability measures on $A$.

== Typing rules and properties



#remark([Softness lives on the logical entailment, not the typing judgement])[
  @def:holder is what lets predicates aggregated at different softness grades compose soundly: _any_ two grades $p, q$ compose, the pairing being bounded at the composite grade $p plus.o^* q$ (classical Hölder conjugacy is the slice $p plus.o^* q = 1$). Because this composition happens when entailments are cut against each other, softness is tracked as a grade on the entailment of the inner logic, and not on the term-level typing judgement — the term-level sensitivity index $r$ (Lipschitz behaviour w.r.t. the metric) is a different quantity and the two must not be conflated.
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
The sum of two contexts $Γ ⧺ Γ'$ and the scaling $r Γ$ of a context are defined to keep track of the _sensitivities_ of the resources in the context. The sum $Γ ⧺ Γ'$ is defined only for _compatible_ contexts — same variables, with the same types, in the same order, differing only in their sensitivity annotations (cf. @cmethol); rules such as (APP) below implicitly weaken both premises to a common variable support first, which is harmless since the calculus is affine.

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

#definition([IB types])[
  The _IB types_ are the fragment of types whose interpretations carry a complete interpolative barycentric algebra structure (@def:ib-algebra), closed under the type formers that preserve it:
  $ E, F ::= cal(W) A | E attach(times.o, bl: p, br: q) F | A multimap_r E, quad quad p, q in [0, oo), thick r in [0, oo], thick A "arbitrary". $
  This is the grammar of @cmethol (p. 6:9) — with one difference worth noting: their side condition $q <= 1$ on scaled IB types exists because in *CMet* the comparison $beta_(q,p) : (q p) X -> q(p X)$ is an isomorphism only under provisos (Thm. 1); in *CExtMet*, where $beta$ is an identity for all scalars (@def:scaling-monoidal), $q E$ is an IB algebra for _every_ $q in [0, oo)$, so no restriction is needed. The (LET) rule below eliminates $cal(W) A$ into any IB type via the free extension of @prop:free-ext, which is where its side condition $r < oo$ comes from.
] <def:ib-types>

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
  $r >= 1$,
  // --------------------------------------------------------
  $Γ ⧺ r Γ' ⊢ "case" t "of" ["inj"_1 x => u | "inj"_2 y => v] : C$,
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
  $Γ' ⊢ u : A attach(⊗, bl: r, br: s) B$,
  // -------------------------------------
  $Γ ⧺ Γ' ⊢ "let" (x, y) = u "in" t : C$,
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
  $E "IB type"$,
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
  $Γ ⧺ ∞ Γ' ⧺ ∞ Γ'' ⊢ "rec"(z, (x,y).s, n) : A$,
))

#let fix = prooftree(rule(
  name: [(FIX)],
  $(1-r) Γ, x tcol(r) A ⊢ t : A$,
  $r < 1$,
  $A "Banach"$,
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

Two side conditions deserve comment. In (FIX), the side condition "$A$ Banach" (@def:banach-types) is what makes $⟦"fix" x. t⟧$ exist and be unique; without it the rule is unsound at multi-galaxy types: the closed term $"fix" x. "case" x "of" ["inj"_1 y => "inj"_2 () | "inj"_2 y => "inj"_1 ()] : 1 + 1$ would otherwise be derivable (with (CASE) at any $r < 1$, since the branches ignore their binder), and its denotation would have to be the fixed-point-free swap of @rem:fix-fails. In (CASE) we keep $r >= 1$ in conformance with @cmethol; semantically $r > 0$ would also be sound in *CExtMet* — the $oo$-separated coproduct makes $r(A + B) tilde.equiv r A + r B$ for every $r > 0$, and the Banach guard on (FIX) already blocks the term above — but we do not pursue the relaxation here, as the metatheory (substitution, adequacy) is developed against the $r >= 1$ convention.

== Semantics

Judgements are interpreted as morphisms:

#let judg-sem = $⟦ Γ ⊢t : A ⟧: ⟦ Γ ⟧ →^⟦ t ⟧ ⟦ A ⟧$

#align(
  center,
  judg-sem,
)

Each type is interpreted as an object in *CExtMet*:

#let sem-types = columns(3)[
  $
                             ⟦ NN ⟧ & ≜ (NN, d_1) \
                      ⟦ A times B ⟧ & ≜ ⟦ A ⟧ times ⟦ B ⟧ \
    ⟦ A attach(⊗, bl: r, br: s) B ⟧ & ≜ r ⟦ A ⟧ ⊗ s ⟦ B ⟧ \
  $
  #colbreak()
  $
                              ⟦ 1 ⟧ & ≜ bold("1") \
                          ⟦ A + B ⟧ & ≜ ⟦ A ⟧ + ⟦ B ⟧ \
    ⟦ A attach(multimap, br: r) B ⟧ & ≜ r⟦ A ⟧ multimap ⟦ B ⟧ \
  $
  #colbreak()
  $
                   ⟦ cal(W)A ⟧ & ≜ cal(W)_0 ⟦ A ⟧ \
       ⟦ chevron.l chevron.r ⟧ & ≜ bold("1") \
    ⟦ Γ, x attach(:, tr: r) A⟧ & ≜ ⟦ Γ ⟧ times.o r⟦ A⟧
  $
]

#sem-types

Here $(NN, d_1)$ is the natural numbers with the $1$-_discrete_ metric $d_1 (m, n) = 1$ for $m eq.not n$, i.e. the *CMet* convention rather than the free ($oo$-discrete) *CExtMet* embedding. The choice matters: with the $oo$-discrete metric, any two distinct finitely supported measures in $cal(W) NN$ would lie at distance $oo$, and recursively defined distributions in the style of $"geo"_p$ (whose Banach iteration must converge in $cal(W) NN$) would die. With $d_1$, the space $cal(W) NN$ is a genuine bounded Kantorovich space, and $NN$ is a Banach type. Note the $oo$-scaling of _both_ side contexts in (REC): the step context $Γ'$ because it is used at every stage (copyability of $oo Γ'$), and the numeral context $Γ''$ because the result of a recursion is _not_ Lipschitz in $n$ — results at successive numerals can be arbitrarily far apart once the result type has diameter $> 1$ (e.g. $A = NN attach(times.o, bl: 2, br: 1) 1$ with $s$ applying $"succ"$), so $n$ must enter discretely. In the $1$-bounded *CMet* the unscaled $Γ''$ is harmless because every object has diameter $<= 1$; in *CExtMet* it would be unsound.

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

== Judgemental equality

Following @cmethol (Fig. 2), the calculus carries an equational judgement $Γ ⊢ t ≡ u : A$, generated by the $beta$/$eta$ laws for $lambda$, $chevron.l -, - chevron.r$/$pi_i$ and $()$, together with:

- $"let" (x, y) = (s, t) "in" u ≡ u[s\/x, t\/y]$ and the case-of-injection reductions;
- the sampling-let laws $"let" x = delta(t) "in" u ≡ u[t\/x]$ and the $amp.inv_p$-homomorphism law $"let" x = (s amp.inv_p s') "in" u ≡ ("let" x = s "in" u) amp.inv_p ("let" x = s' "in" u)$, together with the commuting conversions for nested lets;
- fixed-point unfolding $"fix" x. t ≡ t["fix" x. t \/ x]$;
- the recursor equations $"rec"(z, (x,y).s, "zero") ≡ z$ and $"rec"(z, (x,y).s, "succ"(n)) ≡ s["rec"(z, (x,y).s, n)\/x, thin n\/y]$.

Judgemental equality is what feeds the logical equality introduction rule (=I) below: every fixed-point proof begins by unfolding $"fix"$ judgementally and then rewriting logically. We also record the definable functorial action of $cal(W)$: for $f : A multimap_r B$ with $r < oo$,
$ cal(W)(f) := lambda a. "let" x = a "in" delta(f #h(0.2em) x) : cal(W) A multimap_r cal(W) B, $
needed e.g. for $"geo"_p$-style recursive distributions.

= Logic

We now turn the poset $prop$ into the carrier of an _internal logic_. Predicates are terms of type $prop$, and reasoning is carried out by a _graded_ entailment whose grade is the softness $p$.

#let prop-signature = $(
  [0, +oo],
  ⊥, ⊤, bold(1),
  times.o, times.o^*, multimap,
  (-)^*,
  and^s, or^s,
  exists^s, forall^s
)$

$
  prop = #prop-signature
$

Here $0 = bot$ and $oo = top$ are the lattice bounds, $bold(1)$ is the multiplicative unit, and a value is _true_ iff it is $>= 1$. Note that top and unit come apart in this signature: $top = oo$ is the strongest possible predicate, while the _trivial_ (discardable) predicate is the unit $bold(1)$ — in the $[0,1]$-valued logic of @cmethol the two coincide (both are the distance $0$), and keeping them apart is essential for the structural rules below. We equip $prop$ with the _log metric_ $d_prop (a, b) = |log a - log b|$, the pullback of the additive metric along $log$, with the boundary conventions $d_prop (0, 0) = d_prop (oo, oo) = 0$ and $d_prop (0, a) = d_prop (oo, a) = oo$ for $a in (0, oo)$ (and $d_prop (0, oo) = oo$). With these conventions $prop$ is a non-empty complete extended metric space with three galaxies — ${0}$, $(0, oo) tilde.equiv RR$, and ${oo}$ — hence an object of *CExtMet*. Under the log metric the involution $a |-> a^* = 1\/a$ is an isometry, the multiplicatives $times.o$ and $multimap$ become addition and subtraction of log-values, and every soft family $plus.o^(plus.minus s)$ and mean $integral^(plus.minus s)$ is non-expansive at _every_ grade $s in (0, oo]$, with no $|s| >= 1$ restriction. (The boundary $s = 0$ is degenerate for the binary sums and splits into two geometric means for the integrals — cf. the conjunctive and disjunctive geometric means of QLL, eq. 3.19 — so we exclude it from the connective grammar.) The crisp values $0$ and $oo$ lie at infinite log-distance from every soft value, so the metric content sits on $(0, oo) tilde.equiv RR$.




// graded turnstile and soft connectives
#let ent(p) = $attach(tack.r, br: #p)$
#let psum(s) = $attach(plus.o, tr: #s)$
#let fa(s) = $attach(forall, tr: #s)$
#let ex(s) = $attach(exists, tr: #s)$

The equality former is interpreted by the distance map, the quantifiers by the $s$-mean and its harmonic dual; each is a morphism of *CExtMet* (hence non-expansive):

$
      (attach(=, br: A)) & : A times.o A -> prop, quad                        & (x, x') |-> e^(-d_A (x, x')) \
  exists^s_A, forall^s_A & : oo(cal(W) A) times.o (A multimap prop) -> prop, quad &                 s in (0, oo]
$

For a reference measure $m in cal(W) A$, a predicate $g in A multimap prop$, and integration point $x : A$, the operators are the $s$-mean and harmonic $s$-mean
$
  exists^s_A (m, g) & ≜ (integral_A g(x)^s dif m(x))^(1\/s) quad quad
                      forall^s_A (m, g) & ≜ (integral_A g(x)^(-s) dif m(x))^(-1\/s)
$

The $oo$-scaling of the measure slot is _forced_: the operators are non-expansive in the predicate slot (sup-log metric, every $s$), but they are _not_ Lipschitz in the measure slot for the Kantorovich metric — on $A = RR$ with the log-isometric predicate $g(x) = e^x$, moving mass $epsilon\/K$ from $0$ to $K$ changes $d_(cal(W) A)$ by $epsilon$ while the log-distance of the means grows like $K$. (Kantorovich duality controls integrals of _additively_ Lipschitz integrands; log-Lipschitz predicates grow exponentially. The problem is invisible in @cmethol, whose $[0,1]$-valued $prop$ carries the Euclidean metric, and in QLL, whose measures are structure of the base category rather than metric arguments.) Every map out of an $oo$-scaled space is short, so with the source $oo(cal(W) A)$ the operators are morphisms of *CExtMet*; equivalently one may metrize the measure argument by the $oo$-Wasserstein (uniform-transport) distance, for which the operators are non-expansive uniformly in $s$.

The annotation $x tilde m$ — read as in the expectation $EE_(x tilde m)$ — binds the integration point $x$ over the carrier of $m$ and names $m$ as the reference measure; the boundary $s = oo$ gives the $m$-_essential_ supremum and infimum, $"ess sup"_(x tilde m) g(x)$ and $"ess inf"_(x tilde m) g(x)$ — that is, sup and inf over $"supp"(m)$ up to $m$-null sets, not the measure-free sup and inf over all of $A$. The quantifier _binders_ reuse this annotation: $exists^s (x tilde m). φ$ binds $x$ in the body $φ$ while $m$ stays in the enclosing context, and abbreviates the operator application $exists^s_A (m, lambda x. φ)$ (dually $forall^s$).

== Typing rules for logical predicates

A _predicate in context_ $Γ$ is a term $φ$ with $Γ ⊢ φ : prop$. Since $prop$ is itself an object of *CExtMet*, predicates are non-expansive maps, so their formation _tracks sensitivity_ exactly like ordinary terms: the tensor-like connectives ($=, times.o, times.o^*, multimap$) sum their contexts as $Γ ⧺ Γ'$, the additive-like ones ($or^s, and^s$) share theirs, and propositions can be _scaled_ by $r$. A quantifier binds its point variable at sensitivity $1$ — the softness $s$ is _not_ a sensitivity, it is the exponent of the mean, and the two grades are independent — and draws the reference measure from a separate $cal(W) A$ premise whose context enters $oo$-scaled, matching the operator signature above. Logical _derivability_, by contrast, uses the ordered measured context $Θ$ of @sec:entailment:

#let prop-tt = prooftree(rule(name: [($⊤_i$)], $Γ ⊢ top : prop$))

#let prop-ff = prooftree(rule(name: [($⊥_i$)], $Γ ⊢ bot : prop$))

#let prop-one = prooftree(rule(name: [($bold(1)_i$)], $Γ ⊢ bold(1) : prop$))

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

#let prop-cotens = prooftree(rule(
  name: [(P-$times.o^*$)],
  $Γ ⊢ φ : prop$,
  $Γ' ⊢ ψ : prop$,
  // --------------------------
  $Γ ⧺ Γ' ⊢ φ times.o^* ψ : prop$,
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
  $s in (0, oo]$,
  // --------------------------
  $Γ ⊢ φ or^s ψ : prop$,
))

#let prop-hsum = prooftree(rule(
  name: [($plus.o^(-s)$)],
  $Γ ⊢ φ : prop$,
  $Γ ⊢ ψ : prop$,
  $s in (0, oo]$,
  // --------------------------
  $Γ ⊢ φ and^s ψ : prop$,
))

#let prop-all = prooftree(rule(
  name: [($forall^s_i$)],
  $Γ, x tcol(1) A ⊢ φ : prop$,
  $Γ' ⊢ m : cal(W) A$,
  $s in (0, oo]$,
  // --------------------------------
  $Γ ⧺ oo Γ' ⊢ fa(s) (x tilde m). space φ : prop$,
))

#let prop-ex = prooftree(rule(
  name: [($exists^s_i$)],
  $Γ, x tcol(1) A ⊢ φ : prop$,
  $Γ' ⊢ m : cal(W) A$,
  $s in (0, oo]$,
  // -------------------------------
  $Γ ⧺ oo Γ' ⊢ ex(s) (x tilde m). space φ : prop$,
))

#let prop-typing-rules = (
  prop-tt,
  prop-ff,
  prop-one,
  prop-eq,
  prop-tens,
  prop-cotens,
  prop-imp,
  prop-scale,
  prop-dual,
  prop-sum,
  prop-hsum,
  prop-all,
  prop-ex,
)

#align(center, rule-set(..prop-typing-rules))

The tensor connectives are non-expansive out of $prop times.o prop$ (hence the sum $Γ ⧺ Γ'$), matching @def:extmet-cmon, while $or^s \/ and^s$ are non-expansive for the max metric (log-sum-exp is jointly $1$-Lipschitz), hence the shared context and cartesian pairing. In the quantifier rules the bound variable carries sensitivity $1$ — so that $"curry"(⟦φ⟧)$ lands in $⟦A⟧ multimap prop$, the source of the operators — and the measure context $Γ'$ enters $oo$-scaled, because the operators are only short out of $oo(cal(W) ⟦A⟧)$ (see above); the softness $s$ appears on the connective only. Scaling $r φ$ is interpreted by the power map, as follows.

=== Interpretation of logical predicate

#let prop-sem = columns(2)[
  $
          ⟦ ⊤ ⟧ & ≜ ∞ quad quad ⟦ bold(1) ⟧ ≜ 1 \
    ⟦ t =_A u ⟧ & ≜ e^(-d_⟦ A ⟧) ∘ (⟦t⟧ ⊗ ⟦ u ⟧) ∘ "split" \
      ⟦ φ ⊗ ψ ⟧ & ≜ ⊗ ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
    ⟦ φ ⊗^* ψ ⟧ & ≜ ⊗^* ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
      ⟦ φ ⊸ ψ ⟧ & ≜ space ⊸ ∘ (⟦φ⟧ ⊗ ⟦ψ⟧) ∘ "split" \
        ⟦ φ^* ⟧ & ≜ (-)^* ∘ ⟦φ⟧ \
  $
  #colbreak()
  $
                      ⟦ ⊥ ⟧ & ≜ 0 quad quad ⟦ r φ ⟧ ≜ (-)^r ∘ r⟦φ⟧ ∘ "dist" \
                ⟦ φ ∨^s ψ ⟧ & ≜ plus.o^s ∘ ⟨⟦φ⟧, ⟦ψ⟧⟩ quad (s = oo : space max = or) \
                ⟦ φ ∧^s ψ ⟧ & ≜ plus.o^(-s) ∘ ⟨⟦φ⟧, ⟦ψ⟧⟩ quad (s = oo : space min = and) \
    ⟦ ∃^s (x tilde m) . φ ⟧ & ≜ integral^s_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) \
    ⟦ ∀^s (x tilde m) . φ ⟧ & ≜ integral^(-s)_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) \
  $
]

#prop-sem

The scaling clause deserves comment: $r φ$ is interpreted by the _power_ map $a |-> a^r$, not by multiplication with $r$. For $r in (0, oo)$, $(-)^r$ is precisely the isometry $r thin prop -> prop$ (since $|log a^r - log b^r| = r thin |log a - log b|$, including the crisp points), so the composite $(-)^r ∘ r⟦φ⟧ ∘ "dist"$ is short out of $⟦r Γ⟧$, matching the rule (P-scale). At the boundaries we set $φ^0 = bold(1)$ (matching $0 Γ = chevron.l chevron.r$: a $0$-scaled predicate is discarded) and $φ^oo$ crisp three-valued ($0$, $1$, or $oo$ according as $φ < 1$, $= 1$, $> 1$) — at $r = oo$ the map is no longer an isometry (it collapses $(1, oo]$ to $oo$), but shortness out of the $oo$-scaled $prop$ is automatic, which is all (P-scale) needs there. This power scaling is exactly the _softening modality_ $(-)^p$ of QLL; note it rescales softness grades, e.g. $(r φ) and^s (r ψ) = r(φ and^(r s) ψ)$ for $r in (0, oo)$.

The equality clause is a morphism of *CExtMet*: it factors as the $1$-Lipschitz map $d_(⟦A⟧)$ into the _additive_ $[0, oo]$ (with $|oo - oo| = 0$ on the source), followed by the isometry $e^(-(-)) : ([0, oo], |a - b|) -> prop$, so the composite is non-expansive.

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
  Read $φ ⊢ ψ$ as $⟦ψ⟧ >= ⟦φ⟧$ and the comma as $times.o$. The predicate $⟦ t =_A u ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧))$ satisfies, at every grade $s in (0, oo]$:
  - *reflexivity:* $⟦ t =_A t ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦t⟧)) = e^0 = 1$, so $ent(oo) (t =_A t)$ holds _with empty logical context_ — true exactly at the threshold $1$. (The context must be empty, or consist of subunital hypotheses: a hypothesis $ψ$ with $⟦ψ⟧ > 1$ would strengthen the antecedent past the conclusion, cf. @rem:linear.)
  - *symmetry:* $⟦ t =_A u ⟧ = e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧)) = e^(-d_(⟦A⟧) (⟦u⟧, ⟦t⟧)) = ⟦ u =_A t ⟧$, since $d_(⟦A⟧)$ is symmetric — the two predicates are equal;
  - *transitivity:* $(t =_A u) times.o (u =_A v) ⊢ (t =_A v)$, i.e. $e^(-d_(⟦A⟧) (⟦t⟧, ⟦v⟧)) >= e^(-d_(⟦A⟧) (⟦t⟧, ⟦u⟧)) dot e^(-d_(⟦A⟧) (⟦u⟧, ⟦v⟧))$, which after $-log$ is exactly the triangle inequality $d_(⟦A⟧) (⟦t⟧, ⟦v⟧) <= d_(⟦A⟧) (⟦t⟧, ⟦u⟧) + d_(⟦A⟧) (⟦u⟧, ⟦v⟧)$.
  All three hold at every grade because the relevant integrand is pointwise $>= 1$, and any $s$-mean of values $>= 1$ is again $>= 1$.
]

The quantifier clauses are morphisms by the same pattern: after $"split"$ (and the symmetry braiding $sigma$ matching the factors), $"curry"(⟦φ⟧) times.o oo⟦m⟧$ feeds the operator $exists^s_(⟦A⟧)$ (resp. $forall^s_(⟦A⟧)$), which is non-expansive in the predicate slot (sup-log, every $s$) and trivially short in the $oo$-scaled measure slot.

#block(above: 1.5em, below: 1.5em, width: 100%, align(center, diagram(
  spacing: 3.6em,
  node((0, 0), $⟦Γ⟧ times.o oo⟦Γ'⟧$),
  node((1, 0), $(⟦A⟧ multimap prop) times.o oo(cal(W) ⟦A⟧)$),
  node((2, 0), $prop$),
  edge((0, 0), (1, 0), $"curry"(⟦φ⟧) times.o oo⟦m⟧$, "->"),
  edge((1, 0), (2, 0), $exists^s_(⟦A⟧) ∘ sigma$, "->"),
)))

so that $⟦ exists^s (x tilde m). φ ⟧ = integral^s_(x tilde ⟦m⟧) ∘ "curry"(⟦φ⟧) = exists^s_(⟦A⟧) ∘ sigma ∘ ("curry"(⟦φ⟧) times.o oo⟦m⟧) ∘ "split"$, and dually with $forall^s$.

== The graded entailment judgement <sec:entailment>

The logical judgement has the shape

#align(center, box(stroke: .5pt, inset: 5pt)[
  $ Θ thin | thin Ψ ent(P) φ $
])

where $Ψ = ψ_1, ..., ψ_k$ is a list of predicates (the _logical context_), $φ$ the conclusion, and $Θ$ is an _ordered, measured, graded_ context of variable declarations
$ Θ ::= emptyctx thin | thin Θ thin ; thin x tilde^s m thin | thin Θ thin ; thin x : A $
The measured form declares $x : A$ with a _softness grade_ $s in (0, oo]$ and a _reference measure_ $m : cal(W) A$, a term over the preceding prefix of $Θ$ (disintegration style: $m$ may depend on the earlier variables, not on $x$ or later ones). The plain form $x : A$ is a genuine measure-free declaration, read at the hard grade with the sup/inf over _all_ of $⟦A⟧$ — note this is stronger than any measured declaration $x tilde^oo m$, whose grade-$oo$ mean is only the $m$-essential inf over $"supp"(m)$. The judgement carries the _vector_ $P = (s_1, ..., s_n)$ of the declared grades (grade $oo$ for plain declarations).

Writing $times.o.big Ψ$ for the tensor of the logical context — read with the convention $0 dot oo = 0$, so that a false hypothesis beats a $top$ one — the judgement is _valid_ when
$ 1 ≤ integral^(-s_1)_(x_1 tilde m_1) integral^(-s_2)_(x_2 tilde m_2) dots.c integral^(-s_n)_(x_n tilde m_n) ((times.o.big Ψ) multimap φ), $
the _nested_ harmonic means taken in declaration order, first-declared variable outermost (with the plain declarations contributing the pointwise inf over their type) — the nesting order is forced by the dependency of each $m_i$ on the earlier variables, and it matters: means at different grades do not commute. When every declaration is plain, validity is the pointwise inequality $inf_(⟦Θ⟧) (⟦times.o.big Ψ⟧ multimap ⟦φ⟧) >= 1$, exactly the hard entailment judgement of @cmethol (Thm. 16); with measured declarations at grade $oo$ the infima run over the supports of the reference measures instead.

Whenever a rule below places $Θ$ to the left of a term-typing turnstile (as in $Θ ⊢ t : A$ or $Θ ⊢ m : cal(W) A$), it is read through the _erasure_ $|Θ|$ to a sensitivity context, each declaration contributing $x tcol(oo) A$ — validity constrains nothing about the Lipschitz behaviour of predicates in the context variables, so the discrete reading is the right default; premises that do need a specific sensitivity, such as the $x tcol(r) A$ of (EQ-E), say so explicitly.

#remark([Why a vector of grades, and why ordered])[
  A single scalar grade cannot express this judgement, for reasons QLL makes precise (§5, (5.1)–(5.3)): quantifiers do not contract — $forall^p forall^q eq.not forall^(p and q)$ — so distinct variables must keep distinct grades; and they do not exchange — $forall^1 forall^oo$ (mean of sups) differs from $forall^oo forall^1$ (sup of means) — so the context must be ordered. Only _consecutive_ variables of _equal_ grade may be merged through the product of their measures. The grade monoid in each component is $([0, ∞], plus.o^*, ∞)$: its unit is $∞$ (graded reflexivity), and grades compose under cut by the harmonic sum $plus.o^*$ of @def:holder, componentwise.
] <rem:vector-grades>

#remark([The logic is linear, not affine])[
  In the $[0,1]$-valued logic of @cmethol the trivial predicate ("tt", distance $0$) is simultaneously the truth value and the unit of the context comma, so weakening is free and the logic is affine. Here the unit $bold(1)$ sits strictly _inside_ $[0, oo]$: a hypothesis $ψ$ with $⟦ψ⟧ > 1$ ("truer than true") genuinely _strengthens_ the antecedent under the multiplicative reading — from $Ψ ⊢ φ$ one cannot conclude $Ψ, ψ ⊢ φ$, since the integrand drops by the factor $⟦ψ⟧$. In particular the unrestricted axiom $Ψ, φ ⊢ φ$ and unrestricted weakening are _unsound_ (take $⟦ψ⟧ = oo$, or the dual of an equality, $⟦(t = u)^*⟧ = e^(d(t,u)) > 1$). The identity axiom is linear, and weakening is gated on the _subunital_ predicates
  $ σ ::= bold(1) | ⊥ | (t attach(=, br: A) u) | σ times.o σ' | σ and^s σ' | r σ | fa(s)(x tilde m). σ | ex(s)(x tilde m). σ, $
  all of which satisfy $⟦σ⟧ <= 1$ (equalities land in $[0,1]$; tensors, harmonic sums, powers, and $s$-means of subunital values stay subunital). Weakening by a fresh _variable_ declaration is always sound, because reference measures are probability measures.
] <rem:linear>

#let l-id = prooftree(rule(name: [(ID)], $Θ thin | thin φ ent(P) φ$))
#let l-cut = prooftree(rule(
  name: [(CUT)],
  $Θ | Ψ ent(P) φ$,
  $Θ | Φ, φ ent(Q) χ$,
  // --------------------------
  $Θ | Φ, Ψ ent(P plus.o^* Q) χ$,
))
#let l-relax = prooftree(rule(
  name: [(RELAX)],
  $Θ | Ψ ent(Q) φ$,
  $P <= Q$,
  // --------------
  $Θ | Ψ ent(P) φ$,
))
#let l-weak = prooftree(rule(
  name: [(WEAK-$σ$)],
  $Θ | Ψ ent(P) φ$,
  $σ "subunital"$,
  // -----------------
  $Θ | Ψ, σ ent(P) φ$,
))
#let l-vweak = prooftree(rule(
  name: [(V-WEAK)],
  $Θ | Ψ ent(P) φ$,
  $Θ ⊢ m : cal(W) A$,
  $x "fresh"$,
  // -----------------
  $Θ thin ; thin x tilde^s m | Ψ ent(#$P, s$) φ$,
))

#align(center, rule-set(l-id, l-cut, l-relax, l-weak, l-vweak))

Here $P plus.o^* Q$ and $P <= Q$ are componentwise. (ID) is sound at every grade vector since $a multimap a >= 1$ for every $a in [0, oo]$ (including $0 multimap 0 = oo multimap oo = oo$); (CUT) is the iterated reverse Hölder inequality for negative-exponent means; (RELAX) is the monotonicity of power means over probability measures — this is where probability normalization of the reference measures is used; (V-WEAK) integrates a constant.

#theorem([Soundness, statement])[
  If $Θ | Ψ ent(P) φ$ is derivable from the rules of this section and the next, then it is valid in the sense above. (Proof obligation; the grade-$oo$ fragment reduces to the pointwise soundness argument of @cmethol, Thm. 16, and the soft rules to the reverse Hölder and power-mean inequalities named per rule.)
] <thm:soundness>

== Connectives and quantifiers

The multiplicative fragment is residuated ($times.o ⊣ multimap$); note how cut-like rules accumulate softness by componentwise harmonic sum, while the introduction of $multimap$ leaves the grades untouched.

#let l-tensR = prooftree(rule(
  name: [(⊗R)],
  $Θ | Ψ ent(P) φ$,
  $Θ | Φ ent(Q) ψ$,
  // --------------------------------------
  $Θ | Ψ, Φ ent(P plus.o^* Q) φ times.o ψ$,
))
#let l-tensL = prooftree(rule(
  name: [(⊗L)],
  $Θ | Ψ, φ, ψ ent(P) χ$,
  // --------------------------
  $Θ | Ψ, φ times.o ψ ent(P) χ$,
))
#let l-impR = prooftree(rule(
  name: [(⊸R)],
  $Θ | Ψ, φ ent(P) ψ$,
  // --------------------------
  $Θ | Ψ ent(P) φ multimap ψ$,
))
#let l-impL = prooftree(rule(
  name: [(⊸L)],
  $Θ | Ψ ent(P) φ multimap ψ$,
  $Θ | Φ ent(Q) φ$,
  // ----------------------------
  $Θ | Ψ, Φ ent(P plus.o^* Q) ψ$,
))

#align(center, rule-set(l-tensR, l-tensL, l-impR, l-impL))

The soft disjunction $psum(s)$ (the $s$-sum of @def:holder) has the two semiadditive introductions, since $a <= a psum(s) b$ for every softness $s$. Equality is introduced from _judgemental_ equality — with _empty_ logical context, as @rem:linear requires; the rule is sound because $≡$-equal terms have equal denotations, so the predicate evaluates to $1$. Plain reflexivity is the instance $t ≡ t$.

#let l-sumIL = prooftree(rule(
  name: [($plus.o^s$-IL)],
  $Θ | Ψ ent(P) φ$,
  // --------------------------
  $Θ | Ψ ent(P) φ psum(s) ψ$,
))
#let l-sumIR = prooftree(rule(
  name: [($plus.o^s$-IR)],
  $Θ | Ψ ent(P) ψ$,
  // --------------------------
  $Θ | Ψ ent(P) φ psum(s) ψ$,
))
#let l-eqI = prooftree(rule(
  name: [(=I)],
  $Θ ⊢ t ≡ u : A$,
  // ------------------------------------
  $Θ | thin ent(P) (t attach(=, br: A) u)$,
))

#align(center, rule-set(l-sumIL, l-sumIR, l-eqI))

The soft quantifiers are the graded adjoints to reindexing, binding the _innermost_ declaration of the ordered context — the position whose mean is applied first, which is also the only position a binder can leave without crossing another mean. Universal introduction (right adjoint) and existential elimination (left adjoint) are invertible; the premise records $x$'s grade $s$ and measure $m$ in the context, so the mean discharged from the judgement is exactly the one internalized into the formula:

#let l-allI = prooftree(rule(
  name: [($forall^s$-I)],
  $Θ thin ; thin x tilde^s m | Ψ ent(#$P, s$) φ$,
  $x in.not "FV"(Ψ)$,
  // --------------------------
  $Θ | Ψ ent(P) fa(s) (x tilde m). φ$,
))
#let l-exE = prooftree(rule(
  name: [($exists^s$-E)],
  $Θ thin ; thin x tilde^s m | Ψ, φ ent(#$P, s$) χ$,
  $x in.not "FV"(Ψ, χ)$,
  // ------------------------------
  $Θ | Ψ, ex(s) (x tilde m). φ ent(P) χ$,
))

#align(center, rule-set(l-allI, l-exE))

Soundness of ($forall^s$-I) is the pointwise identity $integral^(-s)_(x tilde m) (Ψ multimap φ) = Ψ multimap forall^s (x tilde m). φ$ for $x$-free $Ψ$ (the harmonic mean of a quotient with constant numerator factor); soundness of ($exists^s$-E) additionally pulls the $x$-free $Ψ$ out of the existential — a _Frobenius_ condition, which must be proven for these operators (the scalar identity $integral^s (Ψ times.o φ) = Ψ times.o integral^s φ$ for $x$-free $Ψ$; cf. QLL Lemma 4.11). Note what is _not_ here yet: instantiation ($forall$-E) and witnessing ($exists$-I) are sound only at the hard grade $s = oo$ — a soft mean neither dominates nor is dominated by the value at a single point — and require a substitution rule; see @rem:roadmap.

== Equality elimination, quantifier monotonicity, guarded recursion

Three further principles are sound in the present semantics and ported here from @cmethol; the remaining infrastructure is collected in @rem:roadmap.

#let l-eqE = prooftree(rule(
  name: [(EQ-E)],
  $Θ, x tcol(r) A ⊢ φ : prop$,
  $Θ | Ψ ent(P) φ[t\/x]$,
  $Θ | Φ ent(Q) r(t attach(=, br: A) u)$,
  // --------------------------
  $Θ | Ψ, Φ ent(P plus.o^* Q) φ[u\/x]$,
))
#let l-allmono = prooftree(rule(
  name: [($forall$-MONO)],
  $s <= q$,
  // --------------------------
  $Θ | fa(q) (x tilde m). φ thick ent(P) fa(s) (x tilde m). φ$,
))
#let l-grec = prooftree(rule(
  name: [(G-REC)],
  $Θ | (1-p)Ψ, p φ ent(P) φ$,
  $p < 1$,
  $⟦φ⟧ > 0$,
  // --------------------------
  $Θ | Ψ ent((1-p) P) φ$,
))

#align(center, rule-set(l-eqE, l-allmono, l-grec))

// All entailment rules, re-displayed in spreadsheet.typ
#let logic-rules = (
  l-id, l-cut, l-relax, l-weak, l-vweak,
  l-tensR, l-tensL, l-impR, l-impL,
  l-sumIL, l-sumIR, l-eqI,
  l-allI, l-exE,
  l-eqE, l-allmono, l-grec,
)

_(EQ-E)_ is the workhorse elimination rule of @cmethol adapted to the multiplicative scale: since $φ$ is non-expansive from $r ⟦A⟧$ into the log-metric $prop$, we have $|log ⟦φ[u\/x]⟧ - log ⟦φ[t\/x]⟧| <= r dot d(⟦t⟧, ⟦u⟧)$, i.e. $⟦φ[u\/x]⟧ >= ⟦φ[t\/x]⟧ dot ⟦t = u⟧^r$ — exactly the tensor of the two premises, with grades composing by the cut monoid. Symmetry and transitivity of equality, and congruence, become derivable rather than merely semantically true.

_($forall$-MONO)_ is the power-mean inequality: harmonic means decrease as the exponent grows, so the _harder_ quantifier entails every _softer_ one, $forall^q (x tilde m). φ ⊢ forall^s (x tilde m). φ$ for $s <= q$. This — not (RELAX), which only lowers the grade on the turnstile of a fixed sequent — is the rule that takes a worst-case certificate to an average-case one.

_(G-REC)_ is the logical guarded recursion principle, with scaled hypotheses read as powers per the (P-scale) semantics: from $Ψ^(1-p) times.o φ^p ⊢ φ$ conclude $Ψ ⊢ φ$ — at the _rescaled_ grade $(1-p)P$. Pointwise, given the guard $⟦φ⟧ > 0$, the premise's integrand is exactly $((Ψ multimap φ))^(1-p)$: in log coordinates $L(φ) >= (1-p) L(Ψ) + p L(φ)$ gives $L(φ) >= L(Ψ)$ whenever $L(φ) in RR$. The grade rescaling is where softness enters: by homogeneity of power means, the nested mean of $h^(1-p)$ at grade vector $P$ equals the $(1-p)$-th power of the nested mean of $h$ at grade $(1-p)P$ — so the premise at $P$ is _equivalent_ to the conclusion at $(1-p)P$, and concluding at $P$ itself would be unsound for finite grades (harmonic means decrease as the grade drops). At the all-$oo$ vector $(1-p) dot oo = oo$ and the rule keeps its familiar form. The _positivity side condition_ $⟦φ⟧ > 0$ is where the crisp bottom bites: at $⟦φ⟧ = 0$ the premise trivializes while the conclusion does not, and the rule is unsound. (At $⟦φ⟧ = oo$ both trivialize, harmlessly. Equalities at Banach types satisfy the condition, since bounded diameter keeps $e^(-d) > 0$.) This is the logical shadow of the galaxy phenomenon of @rem:fix-fails.

#remark([Roadmap: infrastructure still to port])[
  To substantiate "the first-order logic of QLL over *CExtMet*", the following remain. From @cmethol: the four induction principles — for $NN$, $times.o$, $+$, and the distribution induction (IND-$cal(W)$), whose convex hypothesis must take the geometric-mean form $φ[μ\/x]^p times.o φ[ν\/x]^(1-p) ⊢ φ[μ amp.inv_p ν\/x]$ (the arithmetic mixture is not the IB structure of the log-metric $prop$; the weighted geometric mean is), keeping the $r < oo$ continuity proviso; the scaled-hypothesis structural rules, where the power reading makes (DUP) $φ^(r+s) = φ^r times.o φ^s$ and (ASSOC) $(φ^r)^s = φ^(r s)$ _exact identities_ — a genuine payoff of *CExtMet* — while (INC) becomes threshold-gated ($φ^s >= φ^r$ for $s > r > 0$ holds iff $φ >= 1$ or $φ = 0$); and the _additive fragment_ of the entailment calculus, entirely absent so far: rules for $and^s$ (note the hard $and$-introduction has no sound finite-$s$ analogue without a $2^(1\/s)$ correction, since $1 and^s 1 = 2^(-1\/s) < 1$), $or^s$-elimination, the $top$/$bot$ axioms ($Θ | Ψ ⊢ top$ under the proviso $times.o.big Ψ < oo$, and ex falso $Θ | Ψ, bot ⊢ φ$), and derivability rules for $times.o^*$ and the involution $(-)^*$, which are currently formation-only; QLL's structure-level sequents (6.4–6.5, 6.29–6.34) suggest single-conclusion validity may not suffice for the additive left rules. Also outstanding for the _term_ calculus: the interpretation clauses per rule, syntactic weakening and substitution lemmas, independence of the interpretation from the derivation (needed since $⧺$-splittings are not unique), and term-level soundness (LICS Lemmas 7–8, Thms 10–11). From QLL: the substitution rule with inflation-constant bookkeeping (QLL 6.14–6.15, §3), from which instantiation ($forall$-E) and witnessing ($exists$-I) derive at the hard grade — with the caveat that $forall^oo (x tilde m)$ is the $m$-essential infimum, so instantiation needs $t$ in the support of $m$; the Frobenius lemma flagged above; and a Beck–Chevalley condition for substitution under parameterized measures (QLL Remark 4.10 — for disintegration-style contexts this is precisely QLL's open case (4.22)). Finally, an attribution note: the metric equality $e^(-d)$ and its rules are the @cmethol lineage extended to $[0, oo]$, not part of QLL, which approaches equality through comprehension (QLL Def. 4.14, 4.16).
] <rem:roadmap>

= Examples

#bibliography("refs.bib")
