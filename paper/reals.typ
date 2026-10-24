#import "common.typ": *

= Preliminaries on extended Reals numbers


*Truth values* $Omega = [0,oo]$.

#tb(
  columns: (1fr, auto),
  table.header([*operations*], [*unit*]),
  [$a ⊗ b = a b$ #h(1em) ($0 ⊗ oo = 0$)],
  [$1$],
  [$a ⊗^* b = a b$ #h(1em) ($0 ⊗^* oo = oo$)],
  [$1$],
  [$a^* = 1 slash a$, #h(0.4em) $0^* = oo$],
  [---],
  [$a multimap b = sup{c mid(|) a ⊗ c <= b} = a^* ⊗^* b$],
  [---],
  [$a ⊕^p b = (a^p + b^p)^(1 slash p)$, #h(0.4em) $a ⊕^(-p) b = (a^(-p) + b^(-p))^(-1 slash p)$],
  [$0$ / $oo$],
)

// #rem[
//   The two corner conventions $0 ⊗ oo = 0$ and $0 ⊗^* oo = oo$ are forced, not ad hoc:
//   they are exactly what makes $multimap$ the residual of $⊗$ at every boundary
//   ($a ⊗ b <= c$ iff $b <= a multimap c$, e.g. $0 multimap 0 = oo$ needs
//   $oo ⊗^* 0 = oo$), what makes $(-)^*$ an involution with dualizing element $1$
//   (so $(Omega, ⊗, 1, (-)^*)$ is a *Girard quantale* and $⊗^*$ its "par"), and what
//   makes reflexivity of the graded entailment of @sec:quasitripos exact. Via $-log$,
//   $(Omega, <=, ⊗, 1)$ is isomorphic to the extended Lawvere quantale
//   $([-oo,+oo], >=, +, 0)$ @lawvere1973, with $(-)^*$ becoming negation.
// ]

*Grades* $[0,oo]$.

#tb(
  columns: (1fr, auto),
  table.header([*operations*], [*unit*]),
  [$p ⊕^* q = (p^(-1) + q^(-1))^(-1)$ #h(0.6em) (harmonic sum)],
  [$oo$],
  [$p and q$ #h(0.6em) (meet, used by thinning and substitution)],
  [$oo$],
)

#definition([Hölder conjugate exponents])[
  Two exponents $p, q in [1, +oo]$ are _Hölder conjugates_ when
  $ 1 / p + 1 / q = 1, $
  with the convention $1 / oo = 0$, so that $p = 1$ pairs with $q = oo$ and $p = q = 2$ is self-conjugate. Hölder's inequality @holder-inequality then bounds the $plus.o.big$-pairing of two families by the product of their $p$- and $q$-sums:
  $ plus.o.big_(i in I) (a_i times.o b_i) <= (plus.o.big_(i in I)^p a_i) times.o (plus.o.big_(i in I)^q b_i). $
] <def:holder>
