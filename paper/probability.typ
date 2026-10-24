#import "common.typ": *

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
