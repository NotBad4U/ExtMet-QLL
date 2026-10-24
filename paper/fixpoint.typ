#import "common.typ": *

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
