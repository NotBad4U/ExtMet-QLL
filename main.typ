#import "lib.typ" : *

#show: para-lipics.with(
  title: [Inner QLL in CMET],
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
]



#bibliography("refs.bib")