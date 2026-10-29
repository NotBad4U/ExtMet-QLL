#import "common.typ": *

= Examples

#let PP = $bb(P)$

== Bisimilarity distance of two processes <sec:ex-bisim>

We redo in $lambda$-FQLL the running example of @cmethol: two processes $m$ and $n$ of a Markov chain, whose bisimilarity distance is bounded by guarded recursion and the congruence of equality. The term-level encoding carries over unchanged; the logical statement does not, because the number $1 \/ 4$ of the original is an artefact of the truncation of distances at $1$, which *CExtMet* does not perform.

#let markov-chain = align(center, diagram(
  node-stroke: 0.6pt,
  node-shape: circle,
  node-inset: 5pt,
  spacing: (4em, 1.5em),
  node((0, 0), $m$, name: <m>),
  node((1, 0), $z$, name: <z>),
  node((2, 0), $n$, name: <n>),
  edge(<m>, <z>, $2 / 3$, "->"),
  edge(<n>, <z>, $1 / 2$, "->"),
  edge(<m>, <m>, $1 / 3$, "->", bend: 130deg, loop-angle: 180deg),
  edge(<n>, <n>, $1 / 2$, "->", bend: 130deg, loop-angle: 0deg),
))

#markov-chain

Assume a type of processes, an observation paired with a next-state distribution, $PP tilde.equiv A attach(times.o, bl: 1, br: 1) cal(W) PP$. The two processes are written over the coupling that the proof below uses: $n$ moves to $n$ with probability $1 \/ 3 + 2 \/ 3 dot 1 \/ 4 = 1 \/ 2$, so

#let proc-defs = $
  m & ≜ "fix" m. (a, space delta m amp.inv_(1 \/ 3) (delta z amp.inv_(1 \/ 4) delta z)) \
  n & ≜ "fix" n. (a, space delta n amp.inv_(1 \/ 3) (delta n amp.inv_(1 \/ 4) delta z))
$
#proc-defs

Both are typed by (FIX): the recursive variable has sensitivity $1 \/ 3$ in the body of $m$, and $1 \/ 3 + 2 \/ 3 dot 1 \/ 4 = 1 \/ 2$ in the body of $n$, both $< 1$.

=== The statement

In *CMet* the example reads $1 / 4 dot "ff" ⊢ m = n$: the constant $"ff" = 1$ is the maximal distance and $1 / 4 dot "ff"$ is the distance $1 \/ 4$. In $lambda$-FQLL the false predicate is $bot = 0 = e^(-oo)$ and scaling is the power $r φ = φ^r$, so $1 / 4 bot = 0^(1 \/ 4) = bot$: scaling never turns an infinite distance into a finite one, and the literal translation $1 / 4 bot ⊢ m = n$ reads $d(m, n) <= oo$. Nor is there a closed predicate denoting a finite non-zero distance, the closed truth values being $top$, $bot$ and the unit $1$.

The statement that transfers is the one the *CMet* proof establishes _before_ it bounds the leaf $d(z, n)$ by the maximal distance $1$. It is parametric in that leaf:

#let bisim-statement = $
  emptyctx thin | thin 1 / 4 (z attach(=, br: PP) n) ent(oo) m attach(=, br: PP) n, quad "i.e." quad d(m, n) <= 1 / 4 dot d(z, n).
$
#bisim-statement

It specialises correctly in every model (@rem:bisim-models).

=== The rules used

The derivation uses four rules which are not among those of @sec:entailment. Each is sound in *CExtMet*; the first is where the untruncated setting is simpler than *CMet*.

#let l-scale = prooftree(rule(
  name: [(scale)],
  $Δ | Ψ ent(oo) φ$,
  $r in (0, oo]$,
  // --------------------------
  $Δ | r Ψ ent(oo) r φ$,
))
#let l-cong = prooftree(rule(
  name: [(cong)],
  $Δ, x_1 tcols(r_1, s_1) A_1, ..., x_k tcols(r_k, s_k) A_k ⊢ t : B$,
  $Δ ⊢ u_i, v_i : A_i$,
  // --------------------------------------------------------------
  $Δ | r_1 (u_1 attach(=, br: A_1) v_1), ..., r_k (u_k attach(=, br: A_k) v_k) ent(oo) t[arrow(u) \/ arrow(x)] attach(=, br: B) t[arrow(v) \/ arrow(x)]$,
))
#let l-unfold = prooftree(rule(
  name: [(unfold)],
  $Δ ⊢ "fix" x. t : A$,
  // -------------------------------------------------
  $Δ | Ψ ent(oo) "fix" x. t attach(=, br: A) t["fix" x. t \/ x]$,
))
#let l-grec = prooftree(rule(
  name: [(G-REC)],
  $Δ | (1 - p) Ψ, p φ ent(oo) φ$,
  $Δ | top times.o Ψ ent(oo) top times.o φ$,
  $p in (0, 1)$,
  // --------------------------
  $Δ | Ψ ent(oo) φ$,
))

#align(center, rule-set(l-scale, l-cong, l-unfold, l-grec))

- *Scaling.* $r Ψ$ scales every formula of $Ψ$. Since $(a b)^r = a^r b^r$ and $(a^s)^r = a^(r s)$, the predicates satisfy on the nose
  $ r (φ times.o ψ) equiv r φ times.o r ψ, quad r (s φ) equiv (r s) φ, quad r (t = t) equiv (t = t), $
  which is the strong monoidality of scaling (@def:scaling-monoidal) read in $prop$. In *CMet* the comparison maps $m_r$ and $pi_(r, s)$ of @cmethol are isomorphisms only under provisos such as $s <= 1$ or $r >= 1$; the proof below needs $2 / 3 (1 / 4 φ) equiv 1 / 6 φ$.
- *Congruence.* (CONG) is the soundness theorem read through $e^(-d)$: $⟦t⟧ : ⟦Δ⟧ times.o r_1 ⟦A_1⟧ times.o dots.c -> ⟦B⟧$ is non-expansive, so $d(t[arrow(u)], t[arrow(v)]) <= sum_i r_i d(u_i, v_i)$, i.e. $⟦t[arrow(u)] = t[arrow(v)]⟧ >= product_i ⟦u_i = v_i⟧^(r_i)$. It is what @cmethol derive from their elimination rule for equality.
- *Unfolding.* (UNFOLD) is the fixed-point equation $⟦"fix" x. t⟧ = ⟦t⟧ ∘ ⟨"id", ⟦"fix" x. t⟧⟩$, at the value $1$. It holds under the same proviso as (FIX) itself: the seed of the iteration must be at finite displacement (@def:guarded-fix).
- *Guarded recursion.* The rule of @cmethol is $(1 - p) Ψ, p φ ⊢ φ arrow.double Ψ ⊢ φ$. It is _not_ sound in *CExtMet* without the second premise. Write $D = -log ⟦φ⟧$ and $E = -log ⟦times.o.big Ψ⟧$ in $[0, oo]$; the first premise says $(1 - p) E + p D >= D$. If $D < oo$ this yields $E >= D$, the conclusion. If $D = oo$ the premise is vacuous and the conclusion $E >= oo$ fails whenever $E < oo$. This is the galaxy issue of Banach's theorem in the extended setting: recursion is only sound where the predicate is finite. The second premise says exactly that. By the convention $0 times.o oo = 0$ the predicate $top times.o φ$ takes the value $oo$ when $⟦φ⟧ > 0$ and $0$ otherwise, so $top times.o Ψ ⊢ top times.o φ$ reads "$Ψ$ finite implies $φ$ finite", i.e. $Ψ$ and $φ$ lie in a common galaxy. It is trivially satisfied when $⟦φ⟧$ is a single galaxy, for instance when $A$ is bounded.

#proposition([Bisimilarity distance of $m$ and $n$])[
  $emptyctx thin | thin 1 / 4 (z = n) ent(oo) m = n$.
] <prop:bisim>

#proof[
  By (G-REC) with $p = 1 \/ 3$ it suffices to derive
  $ 2 / 3 (1 / 4 (z = n)), thin 1 / 3 (m = n) ent(oo) m = n $
  together with the galaxy premise. By the scaling identities the first hypothesis is $1 / 6 (z = n)$. By (UNFOLD) on both sides and transitivity of equality (@lem:eq-equiv), it suffices to derive
  $
    1 / 6 (z = n), thin 1 / 3 (m = n) ent(oo) (a, space delta m amp.inv_(1 \/ 3) (delta z amp.inv_(1 \/ 4) delta z)) = (a, space delta n amp.inv_(1 \/ 3) (delta n amp.inv_(1 \/ 4) delta z)).
  $
  Consider the term
  $
    x tcols(1 \/ 3, o) PP, thin y tcols(1 \/ 6, o) PP, thin z tcols(1 \/ 2, o) PP ⊢ (a, space delta x amp.inv_(1 \/ 3) (delta y amp.inv_(1 \/ 4) delta z)) : PP,
  $
  typed by ($amp.inv_p$), ($delta$) and ($times.o$): the sensitivities are $1 \/ 3$, $2 / 3 dot 1 / 4 = 1 / 6$ and $2 / 3 dot 3 / 4 = 1 / 2$. Instantiating (CONG) with $arrow(u) = (m, z, z)$ and $arrow(v) = (n, n, z)$ gives
  $
    1 / 3 (m = n), thin 1 / 6 (z = n), thin 1 / 2 (z = z) ent(oo) (a, space delta m amp.inv_(1 \/ 3) (delta z amp.inv_(1 \/ 4) delta z)) = (a, space delta n amp.inv_(1 \/ 3) (delta n amp.inv_(1 \/ 4) delta z)),
  $
  and the third hypothesis is the unit $1$ by (=I) and (SCALE), so it is discharged by (CUT). Read in log scale, the derivation is $d(m, n) <= 1 / 3 d(m, n) + 1 / 6 d(z, n)$.

  For the galaxy premise, $top times.o 1 / 4 (z = n) ⊢ top times.o (m = n)$ says that $d(z, n) < oo$ implies $d(m, n) < oo$. Let $F(x) = (a, delta x amp.inv_(1 \/ 3) (delta z amp.inv_(1 \/ 4) delta z))$ be the contraction defining $m$. Since $n = (a, delta n amp.inv_(1 \/ 3) (delta n amp.inv_(1 \/ 4) delta z))$, non-expansiveness gives $d(n, F(n)) <= 2 / 3 dot 1 / 4 dot d(z, n) < oo$, so $n$ is a seed at finite displacement for $F$ and, by Banach's theorem in the extended setting (@def:guarded-fix), its fixed point $m$ lies in the galaxy of $n$.
]

#remark([The bound in each model])[
  The hypothesis $1 / 4 (z = n)$ is what the original constant $1 / 4 dot "ff"$ stood for: a quarter of the distance between $z$ and $n$, which the truncation at $1$ made equal to $1 \/ 4$.
  - In *CMet*, $d(z, n) <= 1$ and @prop:bisim gives $d(m, n) <= 1 \/ 4$.
  - With $A$ carrying the $oo$-discrete metric and $z$ observing a label other than $a$, both sides are $oo$: $m$ and $n$ are told apart with positive probability, and $oo$ is their bisimilarity distance in the extended setting.
  - With $A = RR$ and $z ≜ "fix" z. (b, delta z)$ where $d_A (a, b) = 1$, a second guarded recursion at $p = 1 \/ 2$ on the term $ell tcols(1, o) A, x tcols(1 \/ 2, o) PP ⊢ (ell, space delta x amp.inv_(1 \/ 2) delta z) : PP$ derives $2 (b = a) ⊢ z = n$, i.e. $d(z, n) <= 2$, whence $1 / 2 (b = a) ⊢ m = n$ and $d(m, n) <= 1 \/ 2$, not $1 \/ 4$.
] <rem:bisim-models>
