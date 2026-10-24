#import "common.typ": *

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

#let metric_space_tb =  align(center)[
  #table(
    columns: 2,
    align: center + horizon,
    stroke: (x, y) => (
      left: if x == 1 { 0.5pt },
      bottom: if y == 0 { 0.5pt },
    ),
    table.header([Space (Carrier)], [$d(a, b)$]),
    [$RR$], [$|a - b|$],
    [$NN$], [$cases(0 & "if" a = b, oo & "otherwise")$],
    [$bold(1)$], [$0$],
    [$r dot X$ ($X$)], [$r dot d_X (a, b)$],
    [$X \& Y$ ($X times Y$)], [$max(d_X (a_1, b_1), d_Y (a_2, b_2))$],
    [$X times.o Y$ ($X times Y$)], [$d_X (a_1, b_1) + d_Y (a_2, b_2)$],
    [$X + Y$],
    [$cases(
      d_X (a, b) & "if" a\, b in X,
      d_Y (a, b) & "if" a\, b in Y,
      oo & "otherwise",
    )$],
    [$X -> Y$], [$sup_(x in X) d_Y (a(x), b(x))$],
  )
]

#metric_space_tb <table:metric-spaces>
