
// #import "lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "main.typ": *

// Shrink a diagram uniformly so it never exceeds the width of its table cell.
#let fit-cell(body) = layout(size => {
  let m = measure(body)
  let f = if m.width > size.width and size.width > 0pt { size.width / m.width } else { 1.0 }
  scale(f * 100%, origin: left + horizon, reflow: true, body)
})

#set document(title: "λ-FQLL cheatsheet")

#align(center, text(1.4em, weight: "bold")[λ-FQLL cheatsheet])

= Syntax

#term-syntax

#types-syntax

= Typing

#align(left, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #typing-judg
])

#align(left, box(
  stroke: .5pt,
  inset: 5pt,
)[
  #ctx-judg
])

== Context rules

#align(
  center,
  rule-set(
    ..ctx-typing-rules,
  ),
)

== Terms typing ruls

#align(
  center,
  rule-set(..typing-term-rules),
)


= Semantics

== Judgement

#align(
  center,
  judg-sem,
)

== Regular types

#sem-types

== Structural function

#struct-func


// Semantic interpretation of each term typing rule.
#figure(
  table(
    columns: (auto, 1fr),
    align: (center + horizon, left + horizon),
    stroke: (x: none, y: 0.5pt),
    inset: (x: 10pt, y: 8pt),

    table.header([*Rule*], [*Diagram*]),

    // (VAR)  Γ, x:ʳA, Γ' ⊢ x : A   — project to the slot, then r⟦A⟧ → ⟦A⟧ since r ≥ 1
    [(VAR)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧ times.o r⟦A⟧ times.o ⟦Γ'⟧$),
      node((1, 0), $r⟦A⟧$),
      node((2, 0), $⟦A⟧$),
      edge((0, 0), (1, 0), $"weak"$, "->"),
      edge((1, 0), (2, 0), $r >= 1$, "->"),
    ),

    // (ABS)  λx.t : A ⊸ʳ B   — ⟦λx.t⟧ = curry(⟦t⟧); the triangle is its defining property
    [(ABS)],
    diagram(
      spacing: (4.5em, 3em),
      node((0, 0), $⟦Γ⟧ times.o r⟦A⟧$),
      node((1, 0), $⟦B⟧$),
      node((0, 1), $(r⟦A⟧ multimap ⟦B⟧) times.o r⟦A⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((0, 0), (0, 1), $⟦λ x. t⟧ times.o "id"$, "->"),
      edge((0, 1), (1, 0), $"eval"$, "->"),
    ),

    // (APP)  Γ ⧺ rΓ' ⊢ t u : B   — Rasmus's diagram
    [(APP)],
    diagram(
      spacing: 2.6em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r⟦Γ'⟧$),
      node((2, 0), $(r⟦A⟧ multimap ⟦B⟧) times.o r⟦A⟧$),
      node((3, 0), $⟦B⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $⟦t⟧ times.o r⟦u⟧$, "->"),
      edge((2, 0), (3, 0), $"eval"$, "->"),
    ),

    // (PAIR)  ⟨t,u⟩ : A × B   (shared Γ — cartesian pairing)
    [(PAIR)],
    diagram(spacing: 3em, node((0, 0), $⟦Γ⟧$), node((1, 0), $⟦A⟧ times ⟦B⟧$), edge((0, 0), (1, 0), $⟨⟦t⟧, ⟦u⟧⟩$, "->")),

    // (π_i)  π_i t : A_i
    [($π_i$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A_1⟧ times ⟦A_2⟧$),
      node((2, 0), $⟦A_i⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $pi_i$, "->"),
    ),

    // (inj_i)  inj_i t : A_1 + A_2
    [($"inj"_i$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A_i⟧$),
      node((2, 0), $⟦A_1⟧ + ⟦A_2⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $iota_i$, "->"),
    ),

    // (CASE)  Γ ⧺ rΓ' ⊢ case t of [inj_1 x ⇒ u | inj_2 y ⇒ v] : C   (uses ⊗-over-+ distributivity)
    [(CASE)],
    fit-cell(diagram(
      spacing: 1.5em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r⟦Γ'⟧$),
      node((2, 0), $⟦Γ⟧ times.o r(⟦A⟧ + ⟦B⟧)$),
      node((3, 0), $(⟦Γ⟧ times.o r⟦A⟧) + (⟦Γ⟧ times.o r⟦B⟧)$),
      node((4, 0), $⟦C⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $"id" times.o r⟦t⟧$, "->"),
      edge((2, 0), (3, 0), $"dist"$, "->"),
      edge((3, 0), (4, 0), $[⟦u⟧, ⟦v⟧]$, "->"),
    )),

    // (⊗)  rΓ ⧺ sΓ' ⧺ Γ'' ⊢ (t,u) : A ⊗ʳˢ B   (Γ'' weakened away; codomain = ⟦A ⊗ʳˢ B⟧)
    [($times.o$)],
    diagram(
      spacing: 2.8em,
      node((0, 0), $⟦r Γ ⧺ s Γ' ⧺ Γ''⟧$),
      node((1, 0), $r⟦Γ⟧ times.o s⟦Γ'⟧$),
      node((2, 0), $r⟦A⟧ times.o s⟦B⟧$),
      edge((0, 0), (1, 0), $"split, weak"$, "->"),
      edge((1, 0), (2, 0), $r⟦t⟧ times.o s⟦u⟧$, "->"),
    ),

    // (LET-⊗)  Γ ⧺ Γ' ⊢ let (x,y) = t in u : C   (last arrow uses the associator α to reassociate)
    [(LET-$times.o$)],
    diagram(
      spacing: 2.4em,
      node((0, 0), $⟦Γ ⧺ Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o ⟦Γ'⟧$),
      node((2, 0), $⟦Γ⟧ times.o (r⟦A⟧ times.o s⟦B⟧)$),
      node((3, 0), $⟦C⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $"id" times.o ⟦t⟧$, "->"),
      edge((2, 0), (3, 0), $⟦u⟧ ∘ alpha$, "->"),
    ),

    // (δ)  δ t : 𝒲A   (monad unit η = δ)
    [($delta$)],
    diagram(
      spacing: 3em,
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $⟦A⟧$),
      node((2, 0), $cal(W)⟦A⟧$),
      edge((0, 0), (1, 0), $⟦t⟧$, "->"),
      edge((1, 0), (2, 0), $eta = delta$, "->"),
    ),

    // (⅋_p)  pΓ ⧺ (1-p)Γ' ⊢ t ⅋_p u : 𝒲A   — +_p(μ,ν) = pμ + (1-p)ν, short by the barycentric ineq.
    [($amp.inv_p$)],
    fit-cell(diagram(
      spacing: 1.7em,
      node((0, 0), $⟦p Γ ⧺ (1-p) Γ'⟧$),
      node((1, 0), $p⟦Γ⟧ times.o (1-p)⟦Γ'⟧$),
      node((2, 0), $p cal(W)⟦A⟧ times.o (1-p) cal(W)⟦A⟧$),
      node((3, 0), $cal(W)⟦A⟧$),
      edge((0, 0), (1, 0), $"split"$, "->"),
      edge((1, 0), (2, 0), $p⟦t⟧ times.o (1-p)⟦u⟧$, "->"),
      edge((2, 0), (3, 0), $+_p$, "->"),
    )),

    // (LET)  Γ ⧺ rΓ' ⊢ let x = u in t : E   (E an IB-algebra) — strong-monad bind into α_E
    [(LET)],
    diagram(
      spacing: 2em,
      node((0, 0), $⟦Γ ⧺ r Γ'⟧$),
      node((1, 0), $⟦Γ⟧ times.o r cal(W)⟦A⟧$),
      node((2, 0), $cal(W)(⟦Γ⟧ times.o r⟦A⟧)$),
      node((3, 0), $cal(W)⟦E⟧$),
      node((4, 0), $⟦E⟧$),
      edge((0, 0), (1, 0), $("id" times.o r⟦u⟧) ∘ "split"$, "->"),
      edge((1, 0), (2, 0), $"st"$, "->"),
      edge((2, 0), (3, 0), $cal(W)⟦t⟧$, "->"),
      edge((3, 0), (4, 0), $alpha_E$, "->"),
    ),

    // (FIX)  Γ ⊢ fix x.t : A   from (1-r)Γ, x:ʳA ⊢ t : A with r < 1.
    // ⟦t⟧ is r-contractive in the A-slot, so Banach (within each galaxy) gives the unique fixed point;
    // the triangle IS the fixed-point equation ⟦fix x.t⟧ = ⟦t⟧ ∘ ⟨id, ⟦fix x.t⟧⟩.
    [(FIX)],
    diagram(
      spacing: (5em, 2.4em),
      node((0, 0), $⟦Γ⟧$),
      node((1, 0), $(1-r)⟦Γ⟧ times.o r⟦A⟧$),
      node((1, 1), $⟦A⟧$),
      edge((0, 0), (1, 0), $⟨"id", ⟦"fix" x. t⟧⟩$, "->"),
      edge((1, 0), (1, 1), $⟦t⟧$, "->"),
      edge((0, 0), (1, 1), $⟦"fix" x. t⟧$, "->"),
    ),
  ),
)

= Prop



=== Signature

$
  prop = #prop-signature
$

$
  d_prop (a,b) = |log(a) - log(b)|
$

=== Typing rules

#align(center, rule-set(..prop-typing-rules))


=== Semantics

#prop-sem

==== Equality semantics in details

#figure(
  table(
    columns: 5,
    align: (left, left, center, center, left),
    stroke: none,
    inset: (x: 9pt, y: 6pt),
    table.hline(stroke: 1pt),
    table.header(
      [Distance $d = d_(⟦A⟧)(⟦t⟧, ⟦u⟧)$], [Meaning], [$⟦ t =_A u ⟧ = e^(-d)$], [Lands in], [Truth ( $>= 1$)]
    ),
    table.hline(stroke: 0.5pt),
    [$d = 0$], [$t, u$ equal], [$e^0 = 1$], [${1}$], [true],
    [$0 < d < oo$], [apart, finite], [$e^(-d) in (0, 1)$], [$(0, 1)$], [false to degree $d$],
    [$d = oo$], [infinitely far], [$e^(-oo) = 0$], [${0} = bot$], [false],
    table.hline(stroke: 1pt),
  ),
)

= Logic rule


= Examples

== Neural networks as terms

The calculus has no primitive type of real numbers, but _any_ object of *CExtMet* may serve as a base type. We write $RR^n$ for $n$-dimensional space equipped with its (extended) $ell_2$ metric. A neural network is then assembled from a handful of constants, each typed with its _Lipschitz constant_ recorded as the sensitivity on the arrow. Since the calculus has no internal real arithmetic, these are _primitive constants_ (oracles): their "implementation" is their denotation in *CExtMet*, the concrete short map on the right, and the sensitivity index is forced to be a valid Lipschitz constant of that map.

#columns(3)[
  $ "aff"_(W, b) &: RR^n attach(multimap, br: ||W||) RR^m \
    "aff"_(W, b) &= lambda x. space W x + b $
  #colbreak()
  $ "relu" &: RR^m attach(multimap, br: 1) RR^m \
    "relu" &= lambda x. space (max(x_i, 0))_(i <= m) $
  #colbreak()
  
  $ sigma &: RR attach(multimap, br: 1/4) RR \
    sigma &= lambda z. space 1 / (1 + e^(-z)) $
]

The three sensitivities are the _optimal_ Lipschitz constants of these maps:
- *Affine.* $||W||$ is the operator norm of the weight matrix, by definition the least $r$ with $||W x - W x'|| <= r dot ||x - x'||$; the bias $b$ is a translation, an isometry, so it does not change the constant.
- *ReLU.* Each coordinate $z |-> max(z, 0)$ is $1$-Lipschitz, and applying $1$-Lipschitz maps coordinatewise stays non-expansive for the $ell_2$ metric, so $"relu"$ is short ($r = 1$). The same holds for any coordinatewise $1$-Lipschitz activation ($tanh$, leaky-ReLU, hard-sigmoid, $dots$).
- *Sigmoid.* $sigma'(z) = sigma(z)(1 - sigma(z))$ attains its maximum $1\/4$ at $z = 0$, so by the mean value theorem $sigma$ is $1\/4$-Lipschitz, and $1\/4$ is tight.

Nothing about these constants is special to neural networks: they are simply morphisms of *CExtMet*, and the sensitivity discipline does the Lipschitz bookkeeping for us.

The key structural fact is that _composition multiplies sensitivities_. Given $f : A multimap_r B$ and $g : B multimap_s C$, the (APP) rule scales the argument context by the arrow's index, so the body $g space (f space x)$ accumulates the product $s r$:

#let comp-deriv = prooftree(rule(
  name: [(ABS)],
  rule(
    name: [(APP)],
    $emptyctx ⊢ g : B attach(multimap, br: s) C$,
    rule(
      name: [(APP)],
      $emptyctx ⊢ f : A attach(multimap, br: r) B$,
      rule(name: [(VAR)], $x tcol(1) A ⊢ x : A$),
      $x tcol(r) A ⊢ f space x : B$,
    ),
    $x tcol(s r) A ⊢ g space (f space x) : C$,
  ),
  $emptyctx ⊢ lambda x. g space (f space x) : A attach(multimap, br: s r) C$,
))

#align(center, comp-deriv)

#example("A two-layer perceptron")[
  Let $W_1, b_1$ and $W_2, b_2$ be the parameters of two affine layers. The network
  $ cal(N) := lambda x. space "aff"_(W_2, b_2) space ("relu" space ("aff"_(W_1, b_1) space x)) $
  is typed by iterating the derivation above through the three constants, giving
  $ emptyctx ⊢ cal(N) : RR^n attach(multimap, br: r) RR^k, quad quad r = ||W_1|| dot 1 dot ||W_2||. $
  The sensitivity $r$ appearing in the _type_ is exactly the product-of-spectral-norms Lipschitz bound used in robustness certification — here it is read off the typing derivation rather than estimated after the fact.
]

#example("A probabilistic binary classifier")[
  Write $bold(2) := 1 + 1$ for the Booleans, with $"tt" := "inl" ()$ and $"ff" := "inr" ()$. A stochastic classifier emits a _distribution_ over labels, so it lands in the Wasserstein type $cal(W) bold(2)$:
  $ "net" := lambda x. space (delta space "tt") amp.inv_(p(x)) (delta space "ff"), quad quad p(x) = sigma("logit"(x)). $
  Here $delta$ injects a point label as a Dirac measure (rule ($delta$)) and $amp.inv_(p)$ forms the convex combination $p mu + (1 - p) nu$ (rule ($amp.inv_p$)), so $"net"(x)$ is the Bernoulli measure of confidence $p(x)$. Since $cal(W)$ is non-expansive and $amp.inv_p$ is short, the whole term is typed
  $ emptyctx ⊢ "net" : RR^n attach(multimap, br: r) cal(W) bold(2) $
  with $r$ the Lipschitz constant of $x |-> p(x)$ — the metric on $cal(W) bold(2)$ being the Kantorovich distance of Wasserstein monad.
]

== Properties of neural networks

Given a neural network $cal(N) : RR^m -> RR^n$, a verification property usually takes the form of a Hoare triple $forall x. space cal(P)(x) multimap cal(Q)(x)$, where the pre- and post-conditions $cal(P), cal(Q) : RR multimap prop$ are predicates of the inner logic.

#definition([$epsilon$-$delta$-robustness])[
  Given a neural network $N$ and a vector $v$, consider the specification that requires that for all inputs $x$ that are within $epsilon$ distance from $v$,
  the output of $cal(N)(x)$ should not deviate by more than $δ$ from $cal(N)(v)$:

  $
    forall x. |x - v| <= epsilon multimap |cal(N)(x) - cal(N)(v)| <= delta
  $
]

Recall that the inner logic has no Boolean equality: the equality predicate $(t =_A u) = e^(-d_A (t, u))$ takes values in $(0, 1]$, is _true_ ($= 1$) exactly when $t = u$, and degrades smoothly as the points move apart. Under the residuation $times.o ⊣ multimap$ the implication $phi multimap psi$ evaluates to the log-quotient $⟦psi⟧ \/ ⟦phi⟧$, true iff $⟦phi⟧ <= ⟦psi⟧$. Robustness is therefore expressed _natively_ — without a metric threshold — by scaling the hypothesis with the sensitivity:

#definition([Quantitative robustness predicate])[
  For a network $cal(N) : RR^n multimap RR^k$ and a tolerance $r$, the predicate
  $ "Rob"_r (cal(N), v) ::= r(x =_(RR^n) v) multimap (cal(N) space x =_(RR^k) cal(N) space v) $
  evaluates to $e^(r dot d(x, v) - d(cal(N) x, cal(N) v))$, hence is _true_ ($>= 1$) at $x$ exactly when $d(cal(N) x, cal(N) v) <= r dot d(x, v)$. The thresholded $epsilon$-$delta$ reading is recovered by instantiating $d(x, v) <= epsilon$ and $delta = r epsilon$.
]

#proposition([Robustness for free from the sensitivity type])[
  If $emptyctx ⊢ cal(N) : RR^n attach(multimap, br: r) RR^k$ is derivable, then for every $v$ and every reference measure $m$ the worst-case judgement
  $ v : RR^n thin | thin top ent(oo) fa(oo) (x tilde m). space "Rob"_r (cal(N), v) $
  holds. _Proof._ The typing makes $⟦cal(N)⟧$ an $r$-Lipschitz map, i.e. $d(cal(N) x, cal(N) v) <= r dot d(x, v)$ pointwise, so each integrand of $"Rob"_r$ is $>= 1$; the hard mean $fa(oo)$ ($= inf_x$) of values $>= 1$ is again $>= 1$. No reasoning about the weights is required — only the index on the arrow. $qed$
]

#example([Individual fairness $=$ non-expansiveness])[
  The $r = 1$ case is the metric reading of _individual fairness_ — "similar inputs receive similar outputs":
  $ forall x space forall x'. space (x =_A x') multimap (cal(N) space x =_B cal(N) space x'). $
  This predicate is uniformly true iff $cal(N)$ is non-expansive, i.e. iff $cal(N) : A multimap_1 B$ in the calculus. Fairness is thus not an extra proof obligation but the meaning of a $1$-sensitive type.
]

#example([Soft / average-case robustness])[
  Replacing the hard $fa(oo)$ by a soft grade $s in [0, oo)$ over a _data distribution_ $m in cal(W) RR^n$ yields
  $ "AvgRob"^s_r ::= fa(s) (x tilde m). space "Rob"_r (cal(N), v), $
  the harmonic $s$-mean $(integral "Rob"_r (cal(N), v)(x)^(-s) dif m(x))^(-1\/s)$. At $s = oo$ this is worst-case robustness over $"supp"(m)$ (the previous proposition); for finite $s$ it tolerates a small mass of violating inputs, graded continuously by $s$ — an _average-case_ certificate that no Boolean specification can express. By (RELAX) a hard certificate entails every softer one, $top ent(oo) "AvgRob"^oo_r$ implies $top ent(s) "AvgRob"^s_r$ for all $s$.
]

#example([Probabilistic robustness of the classifier])[
  For the stochastic classifier $"net" : RR^n multimap_r cal(W) bold(2)$, output closeness is measured by the Kantorovich distance, so $"Rob"_r$ instantiates with $=_(cal(W) bold(2))$:
  $ fa(s) (x tilde m). space r(x =_(RR^n) v) multimap (("net" space x) =_(cal(W) bold(2)) ("net" space v)). $
  Because the Wasserstein functor and $amp.inv_p$ are non-expansive, the sensitivity $r$ on $"net"$ certifies this directly: a perturbation of size $epsilon$ shifts the predicted label distribution by at most $r epsilon$ in Kantorovich distance, i.e. the confidence $p(x)$ moves by at most $r epsilon$.
]
