(* The internal logic of the calculus (paper, Sect. "Logic"): the truth values
   Prop = [0, +oo] and their connectives, the predicates and their typing, the
   graded entailment and its rules, and their semantics.  The properties
   proved are those of the equality predicate and the adjunctions of the
   quantifiers to reindexing (Lawvere), with Frobenius and Beck-Chevalley. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import sequences exp.
From ExtMetQLL Require Import analysis_extras extmet cextmet propmetric syntax.
From ExtMetQLL Require Import semantics.

(**md**************************************************************************)
(* # The quantitative logic                                                   *)
(*                                                                            *)
(* Predicates are terms of type Prop, the truth values [0, +oo] with the log  *)
(* metric, and reasoning is a graded entailment Δ ∣ Ψ ⊢[ p ] φ whose grade p  *)
(* is the softness.  The properties proved are those of the equality         *)
(* predicate (an equivalence, substitutive for the predicates non-expansive  *)
(* for the log metric) and of the quantifiers: at every grade s they are the *)
(* Prop-enriched adjoints of the reindexing along a projection (Lawvere),    *)
(* with Frobenius reciprocity and the Beck-Chevalley condition (Section      *)
(* QuantAdjoint), and they are non-expansive in the predicate for the sup of *)
(* the log metric.  Their non-expansiveness in the reference measure, that   *)
(* of the connectives and of ⟦φ⟧, and the soundness of the entailment are    *)
(* left as TODOs.                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*            prop R == the truth values [0, +oo] with the log metric       *)
(*                      prop_dist (propmetric.v); ptrue a == 1 <= a and     *)
(*                      a ⊑ b == a <= b, the entailment of truth values      *)
(*   ptop, pbot, pone == ⊤ = +oo, ⊥ = 0 and the unit 1                       *)
(*         ptens a b == a ⊗ b = a b with 0 ⊗ +oo = 0                         *)
(*           pstar a == a* = 1 / a with 0* = +oo                              *)
(*          ppar a b == a ⊗* b = (a* ⊗ b* )*, with 0 ⊗* +oo = +oo              *)
(*          pimp a b == a ⊸ b = a* ⊗* b                                      *)
(*        pscale r a == r a = a^r, the scaling by r in [0, +oo]               *)
(*  por s a b, pand s a b == a ⊕^s b = (a^s + b^s)^(1/s) and its harmonic    *)
(*                      dual a ⊕^(-s) b = (a* ⊕^s b* )*; max and min at +oo  *)
(*             peq d == e^(-d), the equality predicate of a distance d;      *)
(*                      peq_refl, peq_sym, peq_trans, peq_subst; true iff   *)
(*                      d = 0 (peq_trueP), an isometry from the additive    *)
(*                      distance adist (peq_isometry), non-expansive on     *)
(*                      A ⊗ A (peq_edist_le)                                 *)
(*          hsum p q == the harmonic sum of grades (p^-1 + q^-1)^-1          *)
(*                      Section prop_algebra: a** = a, a* antitone, ⊗        *)
(*                      commutative, associative with unit 1, (a ⊗ b)* =    *)
(*                      a* ⊗* b*, a ⊸ b = (a ⊗ b* )*, (a ⊗ b) ⊸ c =          *)
(*                      a ⊸ (b ⊸ c), a ⊸ a true                              *)
(*            pred R == the predicates φ, ψ ::= t | ⊤ | ⊥ | t =[ A ] u | φ ⊗ ψ *)
(*                      (t a term of type Prop, p_atom t)                  *)
(*                      | φ ⅋ ψ (⊗* ) | φ ⊸ ψ | r *: φ | φ ^* | φ ∨[ s ] ψ    *)
(*                      | φ ∧[ s ] ψ | ∀[ s ] m , φ | ∃[ s ] m , φ           *)
(*                      (pred_scope, %pred; the quantified variable is #0,   *)
(*                      bound at the softness s that the quantifier records) *)
(*   tm_shift k t, pred_shift k φ == the de Bruijn lifting of the variables  *)
(*                      >= k                                                  *)
(*       Γ ⊩[ σ ] φ == the predicate typing ptyped Γ σ φ (Γ ⊢ φ : Prop)      *)
(*        discrete Δ == the environment of the discrete context Δ: every     *)
(*                      variable at sensitivity +oo and at softness +oo      *)
(*   Δ ∣ Ψ ⊢[ p ] φ == the graded entailment entails Δ Ψ p φ; logical        *)
(*                      contexts are lists, last formula first               *)
(*          wmeans W == the s-means wmean s mu g = (∫ g^s dmu)^(1/s) of the  *)
(*                      monad, the interpretation of the quantifiers, with  *)
(*                      their laws: wmean_cst (mean of a constant),         *)
(*                      wmean_le (monotone), wmean_tens (homogeneous),      *)
(*                      wmean_map (change of variables), wmean_join (Fubini) *)
(*     hmean M s mu g == the harmonic s-mean (wmean s mu g* )*               *)
(*   wmean_ne, hmean_ne == the means are non-expansive in the predicate: a  *)
(*                      pointwise log distance <= e bounds that of the means *)
(*   qexists_ne, qforall_ne == the same for the quantifiers along π         *)
(*   phom M s mu φ ψ == [φ, ψ]^s_mu = ∀^s_(x ~ mu) (φ x ⊸ ψ x), the Prop-    *)
(*                      enriched hom of the predicates on T at grade s       *)
(*       psem W M d == ⟦Γ ⊩ φ⟧ : ⟦Γ⟧ -> Prop, by recursion on d              *)
(*  valid W M mu p Ψ φ == 1 <= [⊗Ψ, φ]^p_mu, the validity of the entailment  *)
(*                      under the reference measure mu on ⟦Δ⟧                *)
(*                      Section QuantAdjoint, for π : X × Y -> X:            *)
(*          reindex φ == π^* φ = φ ∘ π, the reindexing (weakening)           *)
(* qexists s m ψ, qforall s m ψ == ∃^s (y ~ m x). ψ (x, y) and               *)
(*                      ∀^s (y ~ m x). ψ (x, y), the quantifiers along π     *)
(*         wpair mu m == the kernel product mu ⋈ m on X × Y (wmean_pair)     *)
(* qexists_adj, qforall_adj == the graded adjunctions ∃^s ⊣ π^* ⊣ ∀^s, as    *)
(*                      equalities of homs at grade s; at the threshold the *)
(*                      rules qforall_I, qexists_E (invertible), the unit    *)
(*                      qexists_unit and counit qforall_counit; pointwise    *)
(*                      the lax forms qexists_le, qforall_ge                 *)
(* qforall_dual, qexists_dual == De Morgan, (∀^s ψ)* = ∃^s ψ* and            *)
(*                      (∃^s ψ)* = ∀^s ψ* (psem_dual_forall, psem_dual_exists *)
(*                      for the predicates)                                  *)
(* qexists_frobenius, qforall_frobenius, qforall_imp == Frobenius           *)
(*                      reciprocity ∃^s (ψ ⊗ π^* φ) = ∃^s ψ ⊗ φ and its duals *)
(* qexists_bc, qforall_bc == the Beck-Chevalley condition for a base change  *)
(* qexists_map, qforall_map == the change of variables along id × g          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope senv_scope.

(** * The truth values *)

(* Prop = [0, +oo] and its log metric are defined in propmetric.v. *)

Section truth_values.
Context {R : realType}.
Implicit Types (a b : prop R) (x d : \bar R).

Definition ptop : prop R := (+oo : \bar R)%:nng.
Definition pbot : prop R := (0%R%:E)%:nng.
Definition pone : prop R := 1%:E%:nng.

(* a is true iff 1 <= a, and a ⊢ b (a ⊑ b) iff a <= b. *)
Definition ptrue a : Prop := 1 <= a%:num.
Definition ple a b : Prop := a%:num <= b%:num.

(* a ⊗ b = a b, with 0 ⊗ +oo = 0 (the convention of mule). *)
Definition ptens a b : prop R := (a%:num * b%:num)%:nng.

(* The involution a* = 1 / a (estar, in propmetric.v). *)
Definition pstar a : prop R := mkprop (estar_ge0 (ge0e a)).

(* a ⊗* b = a b with 0 ⊗* +oo = +oo, the dual of ⊗. *)
Definition ppar a b : prop R := pstar (ptens (pstar a) (pstar b)).

(* a ⊸ b = sup {c | a ⊗ c <= b} = a* ⊗* b. *)
Definition pimp a b : prop R := ppar (pstar a) b.

(* The scaling r a = a^r for r in [0, +oo], r-Lipschitz for the log
   metric. *)
Definition epow x (r : \bar R) : \bar R :=
  match r with
  | r'%:E => x `^ r'
  | +oo => if x < 1 then 0 else if x == 1 then 1 else +oo
  | -oo => 0
  end.

Lemma epow_ge0 x (r : \bar R) : 0 <= x -> 0 <= epow x r.
Proof.
move=> x0; case: r => [r||] //=; first exact: poweR_ge0.
by case: ifP => // _; case: ifP => // _; rw ?lee01 ?leey.
Qed.

Definition pscale (r : Ω R) a : prop R := mkprop (epow_ge0 r%:num (ge0e a)).

(* The s-sum a ⊕^s b = (a^s + b^s)^(1/s) (max a b for s = +oo) and its
   harmonic dual a ⊕^(-s) b = (a^(-s) + b^(-s))^(-1/s) = (a* ⊕^s b* )* (min a b
   for s = +oo): the soft disjunction and conjunction. *)
Definition por (s : Ω R) a b : prop R :=
  mkprop (@lp_dist_ge0 R s%:num a%:num b%:num (ge0e a) (ge0e b)).

Definition pand (s : Ω R) a b : prop R := pstar (por s (pstar a) (pstar b)).

(* e^(-d): the equality predicate of a distance d, 0 at d = +oo. *)
Definition eexp_neg d : \bar R :=
  match d with r%:E => (expR (- r))%:E | +oo => 0 | -oo => +oo end.

Lemma eexp_neg_ge0 d : 0 <= eexp_neg d.
Proof. by case: d => [r||] //=; rw lee_fin expR_ge0. Qed.

Definition peq d : prop R := mkprop (eexp_neg_ge0 d).

Lemma ptensE a b : (ptens a b)%:num = a%:num * b%:num. Proof. by []. Qed.
Lemma pstarE a : (pstar a)%:num = estar a%:num. Proof. by []. Qed.
Lemma pscaleE r a : (pscale r a)%:num = epow a%:num r%:num. Proof. by []. Qed.
Lemma porE s a b : (por s a b)%:num = lp_dist s%:num a%:num b%:num.
Proof. by []. Qed.
Lemma peqE d : (peq d)%:num = eexp_neg d. Proof. by []. Qed.

(* e^(-d) is 1 at 0, at most 1, antitone and turns sums into products. *)
Lemma eexp_neg0 : eexp_neg 0 = 1.
Proof. by rw /= oppr0 expR0. Qed.

Lemma peq0 : peq 0 = pone.
Proof. by apply/val_inj; rw /= ?eexp_neg0 ?oppr0 ?expR0. Qed.

Lemma eexp_neg_le1 d : 0 <= d -> eexp_neg d <= 1.
Proof.
case: d => [r||] /= => [r0|_|//].
  by rw lee_fin expR_le1 oppr_le0.
exact: lee01.
Qed.

Lemma eexp_neg_anti d d' : d <= d' -> eexp_neg d' <= eexp_neg d.
Proof.
case: d d' => [r||] [r'||] /= => [rr'|_|//|//|_|//|_|_|_].
- by rw lee_fin ler_expR lerN2.
- by rw lee_fin expR_ge0.
- exact: lexx.
- exact: leey.
- exact: leey.
- exact: lexx.
Qed.

Lemma eexp_negD d d' : 0 <= d -> 0 <= d' ->
  eexp_neg (d + d') = eexp_neg d * eexp_neg d'.
Proof.
case: d d' => [r||] [r'||] /= => [_ _|_ _|//|_ _|_ _|//|//|//|//].
- by rw -EFinM -expRD opprD.
- by rw mule0.
- by rw mul0e.
- by rw mule0.
Qed.

(* TODO: the non-expansiveness of the connectives for the log metric. *)

(* The harmonic sum of grades p ⊕* q = (p^-1 + q^-1)^-1, with unit +oo. *)
Definition hsum (p q : Ω R) : Ω R := pstar (sens_add (pstar p) (pstar q)).

End truth_values.

Declare Scope prop_scope.
Delimit Scope prop_scope with prop.
Bind Scope prop_scope with prop.

Notation "⊤" := ptop : prop_scope.
Notation "⊥" := pbot : prop_scope.
Notation "a ⊗ b" := (ptens a b) (at level 40, left associativity) : prop_scope.
Notation "a ⅋ b" := (ppar a b) (at level 40, left associativity) : prop_scope.
Notation "a ⊸ b" := (pimp a b) (at level 65, right associativity) : prop_scope.
Notation "r *: a" := (pscale r a) : prop_scope.
Notation "a ^*" := (pstar a) (at level 1, left associativity, format "a ^*")
  : prop_scope.
Notation "a ∨[ s ] b" := (por s a b)
  (at level 85, right associativity, format "a  ∨[ s ]  b") : prop_scope.
Notation "a ∧[ s ] b" := (pand s a b)
  (at level 80, right associativity, format "a  ∧[ s ]  b") : prop_scope.
Notation "a ⊑ b" := (ple a b) (at level 70, format "a  ⊑  b") : prop_scope.

(** * The algebra of the truth values *)

(* The involution a* is antitone and a** = a; ⊗ is commutative, associative
   with unit 1; (a ⊗ b)* = a* ⊗* b*, a ⊸ b = (a ⊗ b* )*, so that
   (a ⊗ b) ⊸ c = a ⊸ (b ⊸ c) (currying) and a ⊸ a is true. *)
Section prop_algebra.
Context {R : realType}.
Implicit Types (a b c : prop R) (x y : \bar R) (r : R).
Local Open Scope prop_scope.

Lemma estar0 : estar (0 : \bar R) = +oo.
Proof. by rw /estar eqxx. Qed.

Lemma estary : estar (+oo : \bar R) = 0.
Proof. by rw /estar (gt_eqF lt0y) eqxx. Qed.

Lemma estar_fin r : (0 < r)%R -> estar r%:E = (r^-1)%:E.
Proof. by move=> r0; rw /estar eqe gt_eqF // (lt_eqF (ltry r)). Qed.

Lemma estarK x : 0 <= x -> estar (estar x) = x.
Proof.
case: x => [r||] //= => [r0|_]; last by rw estary estar0.
have [->|rn0] := eqVneq r 0%R; first by rw estar0 estary.
have r0' : (0 < r)%R by rw lt_def rn0.
by rw !estar_fin ?invr_gt0 // invrK.
Qed.

Lemma estar_le x y : 0 <= x -> x <= y -> estar y <= estar x.
Proof.
case: x y => [r||] [r'||] //= => [r0 rr'|r0 _].
- have [->|rn0] := eqVneq r 0%R; first by rw estar0 leey.
  have r0' : (0 < r)%R by rw lt_def rn0.
  have r0'' : (0 < r')%R by exact: lt_le_trans r0' rr'.
  by rw !estar_fin // lee_fin lef_pV2 ?posrE.
- by rw estary; exact: estar_ge0.
Qed.

Lemma pstarK a : a^*^* = a.
Proof. by apply/val_inj => /=; exact: (estarK (ge0e a)). Qed.

Lemma pstar_le a b : a ⊑ b -> b^* ⊑ a^*.
Proof. exact: estar_le (ge0e a). Qed.

Lemma ple_pstar a b : b^* ⊑ a^* <-> a ⊑ b.
Proof.
split=> [h|]; last exact: pstar_le.
by rw -(pstarK a) -(pstarK b); exact: pstar_le.
Qed.

Lemma ptensC a b : a ⊗ b = b ⊗ a.
Proof. by apply/val_inj; rw /= muleC. Qed.

Lemma ptensA a b c : a ⊗ (b ⊗ c) = a ⊗ b ⊗ c.
Proof. by apply/val_inj; rw /= muleA. Qed.

Lemma ptens1 a : a ⊗ pone = a.
Proof. by apply/val_inj; rw /= mule1. Qed.

Lemma ptens1p a : pone ⊗ a = a.
Proof. by apply/val_inj; rw /= mul1e. Qed.

Lemma pparC a b : a ⅋ b = b ⅋ a.
Proof. by rw /ppar ptensC. Qed.

Lemma pimpE a b : a ⊸ b = (a ⊗ b^*)^*.
Proof. by rw /pimp /ppar pstarK. Qed.

Lemma pstar_imp a b : (a ⊸ b)^* = a ⊗ b^*.
Proof. by rw pimpE pstarK. Qed.

Lemma pstar_tens a b : (a ⊗ b)^* = a^* ⅋ b^*.
Proof. by rw /ppar !pstarK. Qed.

Lemma pstar_par a b : (a ⅋ b)^* = a^* ⊗ b^*.
Proof. by rw /ppar pstarK. Qed.

Lemma pimp_tens a b c : (a ⊗ b) ⊸ c = a ⊸ (b ⊸ c).
Proof. by rw !pimpE pstarK ptensA. Qed.

Lemma ptrueP a : ptrue a <-> pone ⊑ a.
Proof. by []. Qed.

Lemma ptrue_le a b : ptrue a -> a ⊑ b -> ptrue b.
Proof. exact: le_trans. Qed.

Lemma estar_self x : 0 <= x -> 1 <= estar (x * estar x).
Proof.
case: x => [r||] //= => [r0|_]; last by rw estary mule0 estar0 leey.
have [->|rn0] := eqVneq r 0%R; first by rw estar0 mul0e estar0 leey.
have r0' : (0 < r)%R by rw lt_def rn0.
rw estar_fin // -EFinM divff ?gt_eqF // estar_fin ?ltr01 // invr1.
exact: lexx.
Qed.

Lemma pimp_refl a : ptrue (a ⊸ a).
Proof. by rw /ptrue pimpE pstarE ptensE pstarE; exact: estar_self (ge0e a). Qed.

End prop_algebra.

(* The log metric and the algebra of Prop: a log distance at most e is the
   two-sided bound a ⊑ e^e ⊗ b and b ⊑ e^e ⊗ a (prop_dist_le_mul,
   prop_dist_le_of_mul, propmetric.v), and the involution is an isometry. *)
Section prop_metric.
Context {R : realType}.
Implicit Types (a b : prop R).
Local Open Scope prop_scope.

Lemma prop_distC a b : prop_dist a b = prop_dist b a.
Proof. by rw -!prop_edistE edist_sym. Qed.

Lemma pexp_ge0 (e : R) : (0 : \bar R) <= (expR e)%:E.
Proof. by rw lee_fin expR_ge0. Qed.

(* e^e as a truth value. *)
Definition pexp (e : R) : prop R := mkprop (pexp_ge0 e).

Lemma pexpE (e : R) : (pexp e)%:num = (expR e)%:E. Proof. by []. Qed.

Lemma prop_dist_pstar a b : prop_dist a^* b^* = prop_dist a b.
Proof. exact: prop_dist_estar. Qed.

End prop_metric.

(** * Equality is an equivalence *)

(* ⟦t = u⟧ = e^(-d(⟦t⟧, ⟦u⟧)) is reflexive (it is 1, true), symmetric and
   transitive (the triangle inequality, after -log), and substitutive: for a
   predicate g non-expansive for the log metric, (x = y) ⊗ g x ⊢ g y. *)
Section equality.
Context {R : realType} (X : pseudoMetricType R).
Implicit Types x y z : X.
Local Open Scope prop_scope.

Lemma peq_refl x : peq (edist (x, x)) = pone.
Proof. by rw edist_refl peq0. Qed.

Lemma peq_true x : ptrue (peq (edist (x, x))).
Proof. by rw peq_refl; exact: lexx. Qed.

Lemma peq_sym x y : peq (edist (x, y)) = peq (edist (y, x)).
Proof. by rw edist_sym. Qed.

Lemma peq_trans x y z :
  peq (edist (x, y)) ⊗ peq (edist (y, z)) ⊑ peq (edist (x, z)).
Proof.
rw /ple ptensE !peqE -eexp_negD ?edist_ge0 //.
exact: eexp_neg_anti (edist_triangle _ _ _).
Qed.

Lemma peq_subst (g : X -> prop R) :
  (forall x y, prop_dist (g x) (g y) <= edist (x, y)) ->
  forall x y, peq (edist (x, y)) ⊗ g x ⊑ g y.
Proof.
move=> gne x y; rw /ple ptensE peqE.
have := gne x y; rw /prop_dist.
have [-> _|gxy /=] := eqVneq (g x) (g y).
  rw -[X in _ <= X]mul1e; apply: (lee_wpmul2r (ge0e (g y))).
  exact: eexp_neg_le1 (edist_ge0 _).
case: ifP => [/andP[gx gy]|_]; last first.
  by rw leye_eq => /eqP -> /=; rw mul0e; exact: (ge0e (g y)).
have af : (g x)%:num \is a fin_num.
  by case/andP: gx => a0 ay; rw gt0_fin_numE.
have bf : (g y)%:num \is a fin_num.
  by case/andP: gy => b0 by'; rw gt0_fin_numE.
case: (edist (x, y)) => [r||] /= => [|_|//]; last first.
  by rw mul0e; exact: (ge0e (g y)).
rw lee_fin ler_norml => /andP[_]; rw lerBlDl => h.
rw -(fineK af) -(fineK bf) -EFinM lee_fin.
rw -[fine (g x)%:num]lnK ?posrE ?fine_gt0 //.
rw -[fine (g y)%:num]lnK ?posrE ?fine_gt0 //.
by rw -expRD ler_expR addrC lerBlDr.
Qed.

End equality.

(* The equality predicate is correct for the log metric: e^(-d) is true
   exactly at d = 0, e^(-(-)) is an isometry from the additive distance adist
   of [0, +oo] to the log metric (peq_isometry), and =_A : A ⊗ A -> Prop is
   non-expansive (peq_edist_le), as the paper's factorization
   e^(-(-)) ∘ d_A claims. *)
Section equality_metric.
Context {R : realType}.
Implicit Types (a b d : \bar R) (r : R).

Lemma peq_trueP d : 0 <= d -> ptrue (peq d) <-> d = 0.
Proof.
rw /ptrue peqE; case: d => [r||] //= r0.
  rw lee_fin -{1}expR0 ler_expR oppr_ge0; split=> [r1|/eqP].
    by apply/eqP; rw eqe eq_le r1 /=; exact: r0.
  by rw eqe => /eqP ->.
split=> [|h]; first by rw lee_fin leNgt ltr01.
by have := @lt0y R; rw h ltxx.
Qed.

Lemma peq_edist_trueP (X : extMetricType R) (x y : X) :
  ptrue (peq (edist (x, y))) <-> x = y.
Proof.
rw peq_trueP ?edist_ge0 //; split=> [/edist_eq0 //|->]; exact: edist_refl.
Qed.

(* The additive distance on [0, +oo]: |a - b|, with d(+oo, +oo) = 0. *)
Definition adist a b : \bar R := if a == b then 0 else `|a - b|.

Lemma peq_eqE a b : (peq a == peq b) = (eexp_neg a == eexp_neg b).
Proof. by rw -val_eqE. Qed.

Lemma peq_isometry a b : 0 <= a -> 0 <= b ->
  prop_dist (peq a) (peq b) = adist a b.
Proof.
rw /prop_dist /adist peq_eqE !peqE.
case: a b => [r||] [r'||] //= _ _.
- rw !eqe (inj_eq expR_inj) eqr_opp; case: ifP => // _.
  rw !lte_fin !expR_gt0 !ltry /= !expRK opprK.
  by rw [in RHS]distrC addrC.
- by rw eqe gt_eqF ?expR_gt0 // ltxx andbF.
- by rw [0 == _]eq_sym eqe gt_eqF ?expR_gt0 // ltxx.
- by rw !eqxx.
Qed.

Lemma edist_triangle4 (X : pseudoMetricType R) (x x' y y' : X) :
  edist (x, y) <= edist (x, x') + edist (x', y') + edist (y', y).
Proof.
apply: le_trans (edist_triangle _ x' _) _; rw -addeA.
by apply: leeD => //; exact: edist_triangle.
Qed.

Lemma ler_dist_sub (ra rb u v : R) :
  (ra <= u + rb + v)%R -> (rb <= u + ra + v)%R -> (`|ra - rb| <= u + v)%R.
Proof.
move=> t1 t2; rw ler_norml; apply/andP; split.
  by rw lerNl opprB lerBlDr addrAC.
by rw lerBlDr addrAC.
Qed.

(* d_A : A ⊗ A -> ([0, +oo], adist) is non-expansive. *)
Lemma adist_edist (X : pseudoMetricType R) (x x' y y' : X) :
  adist (edist (x, y)) (edist (x', y')) <= edist (x, x') + edist (y, y').
Proof.
rw /adist; case: ifP => [_|/negbT ab]; first exact: adde_ge0.
have [->|cfin] := eqVneq (edist (x, x') + edist (y, y')) +oo; first exact: leey.
have cfin' : edist (x, x') + edist (y, y') < +oo by rw ltey.
have xx' : edist (x, x') < +oo.
  exact: le_lt_trans (leeDl (edist (x, x')) (edist_ge0 _)) cfin'.
have yy' : edist (y, y') < +oo.
  exact: le_lt_trans (leeDr (edist (y, y')) (edist_ge0 _)) cfin'.
have x'x : edist (x', x) < +oo by rw edist_sym.
have y'y : edist (y', y) < +oo by rw edist_sym.
have t1 := edist_triangle4 x x' y y'.
have t2 := edist_triangle4 x' x y' y.
have [afin|] := boolP (edist (x, y) < +oo); last first.
  rw -leNgt leye_eq => /eqP ay.
  have [bfin|] := boolP (edist (x', y') < +oo); last first.
    by rw -leNgt leye_eq => /eqP by'; move: ab; rw ay by' eqxx.
  move: t1; rw ay leye_eq => /eqP s.
  by have := lte_add_pinfty (lte_add_pinfty xx' bfin) y'y; rw s ltxx.
have bfin : edist (x', y') < +oo.
  exact: le_lt_trans t2 (lte_add_pinfty (lte_add_pinfty x'x afin) yy').
have afn : edist (x, y) \is a fin_num by rw ge0_fin_numE ?edist_ge0.
have bfn : edist (x', y') \is a fin_num by rw ge0_fin_numE ?edist_ge0.
have xfn : edist (x, x') \is a fin_num by rw ge0_fin_numE ?edist_ge0.
have yfn : edist (y, y') \is a fin_num by rw ge0_fin_numE ?edist_ge0.
rw (edist_sym y' y) in t1; rw (edist_sym x' x) in t2.
rw -(fineK afn) -(fineK bfn) -(fineK xfn) -(fineK yfn) in t1 t2 *.
rw -!EFinD lee_fin in t1 t2; rw -EFinB abse_EFin -EFinD lee_fin.
exact: ler_dist_sub t1 t2.
Qed.

(* =_A : A ⊗ A -> Prop is a morphism of CExtMet. *)
Lemma peq_edist_le (X : pseudoMetricType R) (x x' y y' : X) :
  prop_dist (peq (edist (x, y))) (peq (edist (x', y'))) <=
  edist (x, x') + edist (y, y').
Proof. by rw peq_isometry ?edist_ge0 //; exact: adist_edist. Qed.

End equality_metric.

(** * Predicates *)

Section predicates.
Context {R : realType}.

(* The predicates in context; the variable of a quantifier is #0 in its body
   and the reference measure m lives in the enclosing context. *)
Inductive pred : Type :=
| p_atom of tm R                      (* t : Prop used as a predicate *)
| p_top                               (* ⊤ *)
| p_bot                               (* ⊥ *)
| p_eq of ty R & tm R & tm R          (* t =_A u *)
| p_tens of pred & pred               (* φ ⊗ ψ *)
| p_par of pred & pred                (* φ ⊗* ψ *)
| p_imp of pred & pred                (* φ ⊸ ψ *)
| p_scale of Ω R & pred               (* r φ *)
| p_dual of pred                      (* φ* *)
| p_or of Ω R & pred & pred           (* φ ∨^s ψ *)
| p_and of Ω R & pred & pred          (* φ ∧^s ψ *)
| p_forall of Ω R & tm R & pred       (* ∀^s (x ~ m). φ *)
| p_exists of Ω R & tm R & pred.      (* ∃^s (x ~ m). φ *)

(* De Bruijn lifting: the variables >= k are shifted by one (the side
   conditions x ∉ FV(Ψ) of the quantifier rules). *)
Fixpoint tm_shift (k : nat) (t : tm R) : tm R :=
  match t with
  | tm_var i => tm_var (if (i < k)%N then i else i.+1)
  | tm_unit => tm_unit
  | tm_abs t => tm_abs (tm_shift k.+1 t)
  | tm_app t u => tm_app (tm_shift k t) (tm_shift k u)
  | tm_pair t u => tm_pair (tm_shift k t) (tm_shift k u)
  | tm_proj1 t => tm_proj1 (tm_shift k t)
  | tm_proj2 t => tm_proj2 (tm_shift k t)
  | tm_inj1 t => tm_inj1 (tm_shift k t)
  | tm_inj2 t => tm_inj2 (tm_shift k t)
  | tm_case t u v =>
    tm_case (tm_shift k t) (tm_shift k.+1 u) (tm_shift k.+1 v)
  | tm_tensor t u => tm_tensor (tm_shift k t) (tm_shift k u)
  | tm_lettensor u t => tm_lettensor (tm_shift k u) (tm_shift k.+2 t)
  | tm_dirac t => tm_dirac (tm_shift k t)
  | tm_choice p t u => tm_choice p (tm_shift k t) (tm_shift k u)
  | tm_let u t => tm_let (tm_shift k u) (tm_shift k.+1 t)
  | tm_zero => tm_zero
  | succ t => succ (tm_shift k t)
  | rec z s n => rec (tm_shift k z) (tm_shift k.+2 s) (tm_shift k n)
  | tm_fix t => tm_fix (tm_shift k.+1 t)
  end.

Fixpoint pred_shift (k : nat) (φ : pred) : pred :=
  match φ with
  | p_atom t => p_atom (tm_shift k t)
  | p_top => p_top
  | p_bot => p_bot
  | p_eq A t u => p_eq A (tm_shift k t) (tm_shift k u)
  | p_tens φ ψ => p_tens (pred_shift k φ) (pred_shift k ψ)
  | p_par φ ψ => p_par (pred_shift k φ) (pred_shift k ψ)
  | p_imp φ ψ => p_imp (pred_shift k φ) (pred_shift k ψ)
  | p_scale r φ => p_scale r (pred_shift k φ)
  | p_dual φ => p_dual (pred_shift k φ)
  | p_or s φ ψ => p_or s (pred_shift k φ) (pred_shift k ψ)
  | p_and s φ ψ => p_and s (pred_shift k φ) (pred_shift k ψ)
  | p_forall s m φ => p_forall s (tm_shift k m) (pred_shift k.+1 φ)
  | p_exists s m φ => p_exists s (tm_shift k m) (pred_shift k.+1 φ)
  end.

(* The environment of a discrete context: every variable at sensitivity +oo
   (the discrete metric) and at softness +oo (hard, the grade of (Ass) and
   (=I)); see the entailment below. *)
Definition discrete (Δ : seq (ty R)) : senv R :=
  nseq (size Δ) (CEntry sensy sensy).

End predicates.

Arguments pred : clear implicits.

Declare Scope pred_scope.
Delimit Scope pred_scope with pred.
Bind Scope pred_scope with pred.

Notation "⊤" := p_top : pred_scope.
Notation "⊥" := p_bot : pred_scope.
Notation "t =[ A ] u" := (p_eq A t u) (at level 70, format "t  =[ A ]  u")
  : pred_scope.
Notation "φ ⊗ ψ" := (p_tens φ ψ) (at level 40, left associativity) : pred_scope.
Notation "φ ⅋ ψ" := (p_par φ ψ) (at level 40, left associativity) : pred_scope.
Notation "φ ⊸ ψ" := (p_imp φ ψ) (at level 65, right associativity) : pred_scope.
Notation "r *: φ" := (p_scale r φ) : pred_scope.
Notation "φ ^*" := (p_dual φ) (at level 1, left associativity, format "φ ^*")
  : pred_scope.
Notation "φ ∨[ s ] ψ" := (p_or s φ ψ)
  (at level 85, right associativity, format "φ  ∨[ s ]  ψ") : pred_scope.
Notation "φ ∧[ s ] ψ" := (p_and s φ ψ)
  (at level 80, right associativity, format "φ  ∧[ s ]  ψ") : pred_scope.
Notation "∀[ s ] m , φ" := (p_forall s m φ)
  (at level 10, φ at level 200, format "∀[ s ]  m ,  φ") : pred_scope.
Notation "∃[ s ] m , φ" := (p_exists s m φ)
  (at level 10, φ at level 200, format "∃[ s ]  m ,  φ") : pred_scope.

(** * Typing of the predicates *)

Reserved Notation "Γ ⊩[ σ ] φ" (at level 70, φ at level 98,
  format "Γ  ⊩[ σ ]  φ").

Section predicate_typing.
Context {R : realType}.
Implicit Types (Γ : seq (ty R)) (σ τ : senv R) (t u m : tm R) (A : ty R)
  (φ ψ : pred R) (r s : Ω R).

(* Γ ⊢ φ : Prop: predicates track sensitivity like terms, the tensor-like
   connectives sum their contexts.  A quantifier ∀^s (x ~ m). φ binds the
   variable x :^r_s A of its body and records its softness s, the exponent
   of the mean that interprets it: the softness changes the value of the
   quantifier, so it must be part of the formula once x has left the
   context.  The sensitivity r is not recorded: it only changes the metric
   the body is read at, not its values (psem does not depend on it), and it
   is absorbed by the context of the reference measure m, scaled by r as in
   the rule (Let) of the terms (r W A = W (r A)). *)
Inductive ptyped : seq (ty R) -> senv R -> pred R -> Type :=
| ptyped_atom Γ σ t :
    Γ ⊢[ σ ] t : ty_prop ->
    (*———————————————————————————— (P-atom) *)
    Γ ⊩[ σ ] p_atom t

| ptyped_top Γ σ :
    size σ = size Γ ->
    (*———————————————————————————— (⊤ᵢ) *)
    Γ ⊩[ σ ] ⊤

| ptyped_bot Γ σ :
    size σ = size Γ ->
    (*———————————————————————————— (⊥ᵢ) *)
    Γ ⊩[ σ ] ⊥

| ptyped_eq Γ σ τ t u A :
    Γ ⊢[ σ ] t : A ->
    Γ ⊢[ τ ] u : A ->
    (*———————————————————————————— (P-=) *)
    Γ ⊩[ σ ⧺ τ ] (t =[A] u)

| ptyped_tens Γ σ τ φ ψ :
    Γ ⊩[ σ ] φ ->
    Γ ⊩[ τ ] ψ ->
    (*———————————————————————————— (P-⊗) *)
    Γ ⊩[ σ ⧺ τ ] φ ⊗ ψ

| ptyped_par Γ σ τ φ ψ :
    Γ ⊩[ σ ] φ ->
    Γ ⊩[ τ ] ψ ->
    (*———————————————————————————— (P-⊗∗) *)
    Γ ⊩[ σ ⧺ τ ] φ ⅋ ψ

| ptyped_imp Γ σ τ φ ψ :
    Γ ⊩[ σ ] φ ->
    Γ ⊩[ τ ] ψ ->
    (*———————————————————————————— (⊸ᵢ) *)
    Γ ⊩[ σ ⧺ τ ] φ ⊸ ψ

| ptyped_scale Γ σ φ r :
    Γ ⊩[ σ ] φ ->
    (*———————————————————————————— (P-scale) *)
    Γ ⊩[ r *: σ ] r *: φ

| ptyped_dual Γ σ φ :
    Γ ⊩[ σ ] φ ->
    (*———————————————————————————— (P-∗) *)
    Γ ⊩[ σ ] φ ^*

| ptyped_or Γ σ φ ψ s :
    Γ ⊩[ σ ] φ ->
    Γ ⊩[ σ ] ψ ->
    (*———————————————————————————— (⊕ˢ) *)
    Γ ⊩[ σ ] φ ∨[s] ψ

| ptyped_and Γ σ φ ψ s :
    Γ ⊩[ σ ] φ ->
    Γ ⊩[ σ ] ψ ->
    (*———————————————————————————— (⊕⁻ˢ) *)
    Γ ⊩[ σ ] φ ∧[s] ψ

| ptyped_forall Γ σ τ φ m A r s :
    A :: Γ ⊩[ CEntry r s :: σ ] φ ->
    Γ ⊢[ τ ] m : 𝕎 A ->
    (*———————————————————————————— (∀ˢᵢ) *)
    Γ ⊩[ σ ⧺ r *: τ ] ∀[s] m , φ

| ptyped_exists Γ σ τ φ m A r s :
    A :: Γ ⊩[ CEntry r s :: σ ] φ ->
    Γ ⊢[ τ ] m : 𝕎 A ->
    (*———————————————————————————— (∃ˢᵢ) *)
    Γ ⊩[ σ ⧺ r *: τ ] ∃[s] m , φ
where "Γ ⊩[ σ ] φ" := (ptyped Γ σ φ).

End predicate_typing.

Notation "Γ ⊩[ σ ] φ" := (ptyped Γ σ φ) : type_scope.

(** * The graded entailment *)

Reserved Notation "Δ ∣ Ψ ⊢[ p ] φ" (at level 70, Ψ at level 69, φ at level 98,
  format "Δ  ∣  Ψ  ⊢[ p ]  φ").

Section entailment.
Context {R : realType}.
Local Open Scope pred_scope.
Implicit Types (Δ : seq (ty R)) (Ψ Φ : seq (pred R)) (φ ψ χ : pred R)
  (p q s : Ω R) (t m : tm R) (A : ty R).

(* Δ ∣ Ψ ⊢_p φ: Δ is a discrete typing context, Ψ the logical context (a
   list, last formula first), p in [0, +oo] the softness grade, with unit +oo
   and composition the harmonic sum under cut.  The grade is the softness of
   the judgement as a whole, that is the common softness of the variables of
   Δ: valid averages over ⟦Δ⟧ at the single exponent p, and the graded
   adjunctions (qforall_adj, qexists_adj) split such a mean along the last
   variable at the same exponent only.  Accordingly the rules (∀ˢ-I) and
   (∃ˢ-E) bind their variable at the softness s of the judgement, which is
   the softness the quantifier records (ptyped_forall, ptyped_exists).  The
   quantifier rules shift the formulas that must not mention the bound
   variable. *)
Inductive entails : seq (ty R) -> seq (pred R) -> Ω R -> pred R -> Type :=
| ent_ass Δ Ψ φ :
    (*———————————————————————————— (Ass) *)
    Δ ∣ φ :: Ψ ⊢[ sensy ] φ

| ent_cut Δ Ψ Φ φ χ p q :
    Δ ∣ Ψ ⊢[ p ] φ ->
    Δ ∣ φ :: Φ ⊢[ q ] χ ->
    (*———————————————————————————— (Cut) *)
    Δ ∣ Ψ ++ Φ ⊢[ hsum p q ] χ

| ent_relax Δ Ψ φ p q :
    Δ ∣ Ψ ⊢[ q ] φ ->
    p%:num <= q%:num ->
    (*———————————————————————————— (Relax) *)
    Δ ∣ Ψ ⊢[ p ] φ

| ent_weak Δ Ψ φ ψ p :
    Δ ∣ Ψ ⊢[ p ] φ ->
    (*———————————————————————————— (Weak) *)
    Δ ∣ ψ :: Ψ ⊢[ p ] φ

| ent_tensR Δ Ψ Φ φ ψ p q :
    Δ ∣ Ψ ⊢[ p ] φ ->
    Δ ∣ Φ ⊢[ q ] ψ ->
    (*———————————————————————————— (⊗R) *)
    Δ ∣ Ψ ++ Φ ⊢[ hsum p q ] φ ⊗ ψ

| ent_tensL Δ Ψ φ ψ χ p :
    Δ ∣ ψ :: φ :: Ψ ⊢[ p ] χ ->
    (*———————————————————————————— (⊗L) *)
    Δ ∣ (φ ⊗ ψ) :: Ψ ⊢[ p ] χ

| ent_impR Δ Ψ φ ψ p :
    Δ ∣ φ :: Ψ ⊢[ p ] ψ ->
    (*———————————————————————————— (⊸R) *)
    Δ ∣ Ψ ⊢[ p ] φ ⊸ ψ

| ent_impL Δ Ψ Φ φ ψ p q :
    Δ ∣ Ψ ⊢[ p ] φ ⊸ ψ ->
    Δ ∣ Φ ⊢[ q ] φ ->
    (*———————————————————————————— (⊸L) *)
    Δ ∣ Ψ ++ Φ ⊢[ hsum p q ] ψ

| ent_orIL Δ Ψ φ ψ p s :
    Δ ∣ Ψ ⊢[ p ] φ ->
    (*———————————————————————————— (⊕ˢ-IL) *)
    Δ ∣ Ψ ⊢[ p ] φ ∨[s] ψ

| ent_orIR Δ Ψ φ ψ p s :
    Δ ∣ Ψ ⊢[ p ] ψ ->
    (*———————————————————————————— (⊕ˢ-IR) *)
    Δ ∣ Ψ ⊢[ p ] φ ∨[s] ψ

| ent_eqI Δ Ψ t A :
    Δ ⊢[ discrete Δ ] t : A ->
    (*———————————————————————————— (=I) *)
    Δ ∣ Ψ ⊢[ sensy ] (t =[A] t)

| ent_allI Δ Ψ φ m A s :
    A :: Δ ∣ map (pred_shift 0) Ψ ⊢[ s ] φ ->
    Δ ⊢[ discrete Δ ] m : 𝕎 A ->
    (*———————————————————————————— (∀ˢ-I) *)
    Δ ∣ Ψ ⊢[ s ] ∀[s] m , φ

| ent_exE Δ Ψ φ χ m A s :
    A :: Δ ∣ φ :: map (pred_shift 0) Ψ ⊢[ s ] pred_shift 0 χ ->
    Δ ⊢[ discrete Δ ] m : 𝕎 A ->
    (*———————————————————————————— (∃ˢ-E) *)
    Δ ∣ (∃[s] m , φ) :: Ψ ⊢[ s ] χ
where "Δ ∣ Ψ ⊢[ p ] φ" := (entails Δ Ψ p φ).

End entailment.

Notation "Δ ∣ Ψ ⊢[ p ] φ" := (entails Δ Ψ p φ) : type_scope.

(** * Semantics *)

(* The s-means of the monad, (∫ g(x)^s dm(x))^(1/s) for s in [0, +oo] (the
   sup of g on the support of m at s = +oo), which interpret the quantifiers
   ∃^s_A : W A ⊗ (A ⊸ Prop) -> Prop; the harmonic mean of ∀^s is derived
   through the involution.  The value of a mean only depends on the carrier
   of X (the metric enters the non-expansiveness), and the record lists the
   laws of the means that the adjunctions of the quantifiers use: the mean
   of a constant (m is a probability), monotonicity, homogeneity in ⊗ (an
   s-mean commutes with the scaling by a constant), the change of variables
   along a pushforward and the iterated means of a join (Fubini).  The
   non-expansiveness in g (sup-log metric, every s) follows from
   monotonicity and homogeneity (wmean_ne).  TODO: the non-expansiveness in
   m, which fails for the Kantorovich distance at s > 0 (it holds for W_oo),
   and the Hölder inequality of the cut. *)
Unset Implicit Arguments.

Record wmeans (R : realType) (W : wmonad R) := WMeans {
  wmean : forall T : Type, Ω R -> WT W T -> (T -> prop R) -> prop R;
  (* (∫ a^s dm)^(1/s) = a *)
  wmean_cst : forall (T : Type) (s : Ω R) (m : WT W T) (a : prop R),
    wmean T s m (fun=> a) = a;
  (* g <= h pointwise implies (∫ g^s dm)^(1/s) <= (∫ h^s dm)^(1/s) *)
  wmean_le : forall (T : Type) (s : Ω R) (m : WT W T) (g h : T -> prop R),
    (forall x, ple (g x) (h x)) -> ple (wmean T s m g) (wmean T s m h);
  (* (∫ (a g)^s dm)^(1/s) = a (∫ g^s dm)^(1/s) *)
  wmean_tens : forall (T : Type) (s : Ω R) (m : WT W T) (a : prop R)
      (g : T -> prop R),
    wmean T s m (fun x => ptens a (g x)) = ptens a (wmean T s m g);
  (* ∫ g d(f_* m) = ∫ g ∘ f dm *)
  wmean_map : forall (X Y : pseudoMetricType R) (s : Ω R) (f : X -o Y)
      (m : WT W X) (g : Y -> prop R),
    wmean Y s (wmap W f m) g = wmean X s m (fun x => g (f x));
  (* ∫ g d(join M) = ∫ (∫ g dn) dM(n), taken at the power s on both sides *)
  wmean_join : forall (T : Type) (s : Ω R) (M : WT W (WT W T))
      (g : T -> prop R),
    wmean T s (wjoin W M) g = wmean (WT W T) s M (fun n => wmean T s n g)
}.

Arguments wmeans {R} W.
Arguments wmean {R W} w {T} s mu g.
Arguments wmean_cst {R W} w {T} s m a.
Arguments wmean_le {R W} w {T} s m g h.
Arguments wmean_tens {R W} w {T} s m a g.
Arguments wmean_map {R W} w {X Y} s f m g.
Arguments wmean_join {R W} w {T} s M g.

Set Implicit Arguments.

Section logic_semantics.
Context {R : realType} (W : wmonad R) (M : wmeans W).
Local Open Scope prop_scope.

(* The harmonic s-mean (∫ g^(-s) dm)^(-1/s) = ((∫ (g* )^s dm)^(1/s))*. *)
Definition hmean (T : Type) (s : Ω R) (mu : WT W T) (g : T -> prop R)
  : prop R := (wmean M s mu (fun x => (g x)^*))^*.

(* ⟦Γ ⊩ φ⟧ : ⟦Γ⟧ -> Prop, the clauses of the paper with split the identity
   on the common carrier of the contexts; r φ is the power a^r.  TODO:
   non-expansiveness for the log metric. *)
Fixpoint psem Γ σ φ (d : Γ ⊩[ σ ] φ) : ctxC W Γ σ -> prop R :=
  match d in ptyped Γ σ φ return ctxC W Γ σ -> prop R with
  | ptyped_atom Γ σ t d => fun γ => sem W d γ
  | ptyped_top _ _ _ => fun _ => ⊤
  | ptyped_bot _ _ _ => fun _ => ⊥
  | ptyped_eq Γ σ τ t u A d1 d2 =>
    fun γ => peq (edist (sem W d1 γ, sem W d2 γ))
  | ptyped_tens Γ σ τ φ ψ d1 d2 => fun γ => psem d1 γ ⊗ psem d2 γ
  | ptyped_par Γ σ τ φ ψ d1 d2 => fun γ => psem d1 γ ⅋ psem d2 γ
  | ptyped_imp Γ σ τ φ ψ d1 d2 => fun γ => psem d1 γ ⊸ psem d2 γ
  | ptyped_scale Γ σ φ r d => fun γ => r *: psem d γ
  | ptyped_dual Γ σ φ d => fun γ => (psem d γ)^*
  | ptyped_or Γ σ φ ψ s d1 d2 => fun γ => psem d1 γ ∨[s] psem d2 γ
  | ptyped_and Γ σ φ ψ s d1 d2 => fun γ => psem d1 γ ∧[s] psem d2 γ
  | ptyped_forall Γ σ τ φ m A r s dφ dm =>
    fun γ => hmean s (sem W dm γ) (fun a : sem_ty W A => psem dφ (γ, a))
  | ptyped_exists Γ σ τ φ m A r s dφ dm =>
    fun γ => wmean M s (sem W dm γ) (fun a : sem_ty W A => psem dφ (γ, a))
  end.

(* The equality predicate of the calculus is an equivalence (peq_refl,
   peq_sym, peq_trans; the substitution peq_subst awaits the non-expansiveness
   of ⟦φ⟧ for the log metric). *)
Lemma psem_eq_refl Γ σ t A (d : Γ ⊢[ σ ] t : A) (γ : ctxC W Γ (σ ⧺ σ)) :
  psem (ptyped_eq d d) γ = pone.
Proof. exact: peq_refl. Qed.

Lemma psem_eq_true Γ σ t A (d : Γ ⊢[ σ ] t : A) (γ : ctxC W Γ (σ ⧺ σ)) :
  ptrue (psem (ptyped_eq d d) γ).
Proof. exact: peq_true. Qed.

Lemma psem_eq_sym Γ σ τ t u A (d1 : Γ ⊢[ σ ] t : A) (d2 : Γ ⊢[ τ ] u : A)
    (γ : ctxC W Γ (σ ⧺ τ)) :
  psem (ptyped_eq d1 d2) γ = psem (ptyped_eq d2 d1) γ.
Proof. exact: peq_sym. Qed.

Lemma psem_eq_trans Γ σ τ ρ t u v A (d1 : Γ ⊢[ σ ] t : A)
    (d2 : Γ ⊢[ τ ] u : A) (d3 : Γ ⊢[ ρ ] v : A)
    (γ : ctxC W Γ (σ ⧺ τ ⧺ (τ ⧺ ρ))) :
  psem (ptyped_tens (ptyped_eq d1 d2) (ptyped_eq d2 d3)) γ ⊑
  psem (ptyped_eq d1 d3) γ.
Proof. exact: peq_trans. Qed.

(* De Morgan for the predicates: ⟦(∀^s (x ~ m). φ)*⟧ = ⟦∃^s (x ~ m). φ*⟧ and
   ⟦(∃^s (x ~ m). φ)*⟧ = ⟦∀^s (x ~ m). φ*⟧, the involution exchanging the
   s-mean and the harmonic s-mean. *)
Lemma psem_dual_forall Γ σ τ φ m A r s (dφ : A :: Γ ⊩[ CEntry r s :: σ ] φ)
    (dm : Γ ⊢[ τ ] m : 𝕎 A) (γ : ctxC W Γ (σ ⧺ r *: τ)) :
  psem (ptyped_dual (ptyped_forall dφ dm)) γ =
  psem (ptyped_exists (ptyped_dual dφ) dm) γ.
Proof. by rw /= /hmean pstarK. Qed.

Lemma psem_dual_exists Γ σ τ φ m A r s (dφ : A :: Γ ⊩[ CEntry r s :: σ ] φ)
    (dm : Γ ⊢[ τ ] m : 𝕎 A) (γ : ctxC W Γ (σ ⧺ r *: τ)) :
  psem (ptyped_dual (ptyped_exists dφ dm)) γ =
  psem (ptyped_forall (ptyped_dual dφ) dm) γ.
Proof.
by rw /= /hmean; congr pstar; congr wmean; apply/funext => a; rw pstarK.
Qed.

(* ⊗Ψ, the tensor of an interpreted logical context. *)
Definition ptens_all (E : Type) (Ψ : seq (E -> prop R)) (γ : E) : prop R :=
  foldr (fun ψ a => ψ γ ⊗ a) pone Ψ.

Lemma ptens_all_cons (E : Type) (ψ : E -> prop R) Ψ γ :
  ptens_all (ψ :: Ψ) γ = ψ γ ⊗ ptens_all Ψ γ.
Proof. by []. Qed.

(* [φ, ψ]^s_mu = ∀^s_(x ~ mu) (φ x ⊸ ψ x), the Prop-enriched hom of two
   predicates on T at grade s under the reference measure mu, whose truth is
   the validity of φ ⊢_s ψ. *)
Definition phom (T : Type) (s : Ω R) (mu : WT W T) (φ ψ : T -> prop R)
  : prop R := hmean s mu (fun x => φ x ⊸ ψ x).

(* The validity of Δ ∣ Ψ ⊢_p φ under a reference measure mu on ⟦Δ⟧: the
   harmonic p-mean of the implication (⊗Ψ) ⊸ φ is true, 1 <= ∫^(-p) (⊗Ψ ⊸ φ);
   p = +oo is the hard entailment on the support of mu.  TODO: soundness of
   the rules of entails. *)
Definition valid (Δ : seq (ty R)) (mu : WT W (ctxC W Δ (discrete Δ)))
    (p : Ω R) (Ψ : seq (ctxC W Δ (discrete Δ) -> prop R))
    (φ : ctxC W Δ (discrete Δ) -> prop R) : Prop :=
  ptrue (phom p mu (ptens_all Ψ) φ).

End logic_semantics.

(** * The quantifiers are adjoint to reindexing *)

(* Lawvere's description of the quantifiers: along the projection
   π : X × Y -> X, the reindexing π^* φ = φ ∘ π (weakening) has the
   quantifiers as adjoints, ∃ ⊣ π^* ⊣ ∀.  Here the predicates on X form a
   Prop-enriched category, with the hom at grade s under the reference
   measure mu the quantity phom s mu φ ψ = ∀^s_(x ~ mu) (φ x ⊸ ψ x) whose
   truth is the validity of φ ⊢_s ψ; on X × Y the reference measure is the
   kernel product wpair mu m (x ~ mu, y ~ m x).  The adjunctions hold as
   equalities of homs at the matching grade s, the paper's "graded
   adjoints":

     [∃^s_m ψ, φ]_mu = [ψ, π^* φ]_(mu ⋈ m)    [φ, ∀^s_m ψ]_mu = [π^* φ, ψ]_(mu ⋈ m)

   whose instances at the truth threshold are the rules (∀ˢ-I) and (∃ˢ-E)
   of the entailment (both invertible) and the unit ψ ⊢_s π^* ∃^s ψ and
   counit π^* ∀^s ψ ⊢_s ψ.  In the pointwise order the adjunctions are only
   lax, since an s-mean is not a bound at s < +oo.  Frobenius reciprocity
   ∃^s (ψ ⊗ π^* φ) = ∃^s ψ ⊗ φ (dually with ⊗* and ⊸ for ∀^s) is the
   homogeneity of the means; the Beck-Chevalley condition for a base change
   f : X' -> X holds on the nose, the quantifiers being computed fibrewise
   with the reindexed measure m ∘ f, and the change of variables along
   id × g pushes the reference measure forward.  Everything follows from the
   laws of wmeans and the algebra of Prop (prop_algebra). *)
Section QuantAdjoint.
Context {R : realType} (W : wmonad R) (M : wmeans W).
Local Open Scope prop_scope.

(* The harmonic means and the homs: constants, monotonicity, homogeneity in
   ⊗* and ⊸, and the graded reflexivity φ ⊢_s φ. *)
Section means.
Context (T : Type).
Implicit Types (s : Ω R) (mu : WT W T) (g h φ : T -> prop R) (a : prop R).

Lemma hmean_cst s mu a : hmean M s mu (fun=> a) = a.
Proof. by rw /hmean wmean_cst pstarK. Qed.

Lemma hmean_le s mu g h :
  (forall x, g x ⊑ h x) -> hmean M s mu g ⊑ hmean M s mu h.
Proof.
move=> gh; rw /hmean; apply/pstar_le/wmean_le => x.
exact: pstar_le (gh x).
Qed.

Lemma hmean_ge1 s mu g : (forall x, ptrue (g x)) -> ptrue (hmean M s mu g).
Proof.
move=> g1; apply/ptrueP; rw -[pone](hmean_cst s mu); apply: hmean_le => x.
exact: g1.
Qed.

Lemma hmean_par s mu a g :
  hmean M s mu (fun x => a ⅋ g x) = a ⅋ hmean M s mu g.
Proof.
rw /hmean -[in RHS](pstarK a) -pstar_tens -wmean_tens.
by congr pstar; congr wmean; apply/funext => x; rw pstar_par.
Qed.

Lemma hmean_imp s mu a g :
  hmean M s mu (fun x => a ⊸ g x) = a ⊸ hmean M s mu g.
Proof. by rw /pimp; exact: hmean_par. Qed.

Lemma phom_refl s mu φ : ptrue (phom M s mu φ φ).
Proof. by apply: hmean_ge1 => x; exact: pimp_refl. Qed.

(* The two means are dual to each other under the involution. *)
Lemma hmean_dual s mu g : (hmean M s mu g)^* = wmean M s mu (fun x => (g x)^*).
Proof. by rw /hmean pstarK. Qed.

Lemma wmean_dual s mu g : (wmean M s mu g)^* = hmean M s mu (fun x => (g x)^*).
Proof. by rw /hmean; congr pstar; congr wmean; apply/funext => x; rw pstarK. Qed.

(* The means are non-expansive in the predicate, for the sup of the log
   metric, at every grade s: by monotonicity and homogeneity in ⊗ (the
   s-mean), and through the involution (the harmonic s-mean). *)
Lemma wmean_ne s mu g h (e : \bar R) : 0 <= e ->
  (forall x, prop_dist (g x) (h x) <= e) ->
  prop_dist (wmean M s mu g) (wmean M s mu h) <= e.
Proof.
case: e => [e||] e0 gh.
- rw lee_fin in e0.
  have hle g' h' : (forall x, prop_dist (g' x) (h' x) <= e%:E) ->
      wmean M s mu g' ⊑ pexp e ⊗ wmean M s mu h'.
    move=> gh'; rw -wmean_tens; apply: wmean_le => x.
    by rw /ple ptensE pexpE; exact: prop_dist_le_mul (gh' x).
  have hg x : prop_dist (h x) (g x) <= e%:E by rw prop_distC; exact: gh.
  apply: prop_dist_le_of_mul e0 _ _.
    by have := hle g h gh; rw /ple ptensE pexpE.
  by have := hle h g hg; rw /ple ptensE pexpE.
- exact: leey.
- by rw leeNy_eq in e0.
Qed.

Lemma hmean_ne s mu g h (e : \bar R) : 0 <= e ->
  (forall x, prop_dist (g x) (h x) <= e) ->
  prop_dist (hmean M s mu g) (hmean M s mu h) <= e.
Proof.
move=> e0 gh; rw /hmean prop_dist_pstar; apply: wmean_ne e0 _ => x.
by rw prop_dist_pstar; exact: gh.
Qed.

End means.

(* The reindexing and the quantifiers along π : X × Y -> X, which only need
   the carriers: π^* φ = φ ∘ π (weakening), ∃^s (y ~ m x). ψ (x, y) and
   ∀^s (y ~ m x). ψ (x, y) at grade s with the reference measure m, computed
   fibrewise. *)
Section quantifiers.
Context (X Y : Type).
Implicit Types (s : Ω R) (m : X -> WT W Y) (φ χ : X -> prop R)
  (ψ : X * Y -> prop R) (Ψ : seq (X -> prop R)).

Definition reindex φ (u : X * Y) : prop R := φ u.1.

Definition qexists s m ψ : X -> prop R :=
  fun x => wmean M s (m x) (fun y => ψ (x, y)).

Definition qforall s m ψ : X -> prop R :=
  fun x => hmean M s (m x) (fun y => ψ (x, y)).

Lemma ptens_all_reindex Ψ : ptens_all (map reindex Ψ) = reindex (ptens_all Ψ).
Proof. by apply/funext => u; rw /ptens_all /reindex foldr_map. Qed.

(* In the pointwise order the adjunctions are lax: an s-mean lies between
   the bounds of the integrand (the converses hold at s = +oo on the support
   of m only); the exact adjunctions are the equalities of homs below. *)
Lemma qexists_le s m ψ φ :
  (forall u, ψ u ⊑ reindex φ u) -> forall x, qexists s m ψ x ⊑ φ x.
Proof.
move=> le x; rw /qexists -[φ x](wmean_cst M s (m x)); apply: wmean_le => y.
exact: le (x, y).
Qed.

Lemma qforall_ge s m φ ψ :
  (forall u, reindex φ u ⊑ ψ u) -> forall x, φ x ⊑ qforall s m ψ x.
Proof.
move=> le x; rw /qforall -[φ x](hmean_cst s (m x)); apply: hmean_le => y.
exact: le (x, y).
Qed.

(* Frobenius reciprocity ∃^s (ψ ⊗ π^* φ) = ∃^s ψ ⊗ φ, the homogeneity of the
   means, and its duals ∀^s (ψ ⊗* π^* φ) = ∀^s ψ ⊗* φ and
   ∀^s (π^* φ ⊸ ψ) = φ ⊸ ∀^s ψ. *)
Lemma qexists_frobenius s m ψ φ :
  qexists s m (fun u => ψ u ⊗ reindex φ u) = fun x => qexists s m ψ x ⊗ φ x.
Proof.
apply/funext => x; rw /qexists /reindex /= [RHS]ptensC -wmean_tens.
by congr wmean; apply/funext => y; rw ptensC.
Qed.

Lemma qforall_frobenius s m ψ φ :
  qforall s m (fun u => ψ u ⅋ reindex φ u) = fun x => qforall s m ψ x ⅋ φ x.
Proof.
apply/funext => x; rw /qforall /reindex /= [RHS]pparC -hmean_par.
by congr hmean; apply/funext => y; rw pparC.
Qed.

Lemma qforall_imp s m φ ψ :
  qforall s m (fun u => reindex φ u ⊸ ψ u) = fun x => φ x ⊸ qforall s m ψ x.
Proof. by apply/funext => x; rw /qforall /reindex /= hmean_imp. Qed.

(* De Morgan: (∀^s ψ)* = ∃^s ψ* and (∃^s ψ)* = ∀^s ψ*, so that each
   quantifier is the dual of the other, ∀^s ψ = (∃^s ψ* )*. *)
Lemma qforall_dual s m ψ :
  (fun x => (qforall s m ψ x)^*) = qexists s m (fun u => (ψ u)^*).
Proof. by apply/funext => x; rw /qforall hmean_dual. Qed.

Lemma qexists_dual s m ψ :
  (fun x => (qexists s m ψ x)^*) = qforall s m (fun u => (ψ u)^*).
Proof. by apply/funext => x; rw /qexists /qforall wmean_dual. Qed.

Lemma qforallE s m ψ :
  qforall s m ψ = fun x => (qexists s m (fun u => (ψ u)^*) x)^*.
Proof. by rw -qforall_dual; apply/funext => x /=; rw pstarK. Qed.

Lemma qexistsE s m ψ :
  qexists s m ψ = fun x => (qforall s m (fun u => (ψ u)^*) x)^*.
Proof. by rw -qexists_dual; apply/funext => x /=; rw pstarK. Qed.

(* The quantifiers are non-expansive in the predicate, for the sup of the
   log metric. *)
Lemma qexists_ne s m ψ ψ' (e : \bar R) : 0 <= e ->
  (forall u, prop_dist (ψ u) (ψ' u) <= e) ->
  forall x, prop_dist (qexists s m ψ x) (qexists s m ψ' x) <= e.
Proof. by move=> e0 h x; apply: wmean_ne e0 _ => y; exact: h. Qed.

Lemma qforall_ne s m ψ ψ' (e : \bar R) : 0 <= e ->
  (forall u, prop_dist (ψ u) (ψ' u) <= e) ->
  forall x, prop_dist (qforall s m ψ x) (qforall s m ψ' x) <= e.
Proof. by move=> e0 h x; apply: hmean_ne e0 _ => y; exact: h. Qed.

End quantifiers.

Arguments reindex {X Y} φ u.
Arguments qexists {X Y} s m ψ.
Arguments qforall {X Y} s m ψ.

(* The Beck-Chevalley condition: for a base change f : X' -> X the square

       X' × Y --f × id--> X × Y
         |π'                |π
         X'   -----f----->  X

   is a pullback, and f^* ∘ ∃^s_m = ∃^s_(m ∘ f) ∘ (f × id)^* (dually for ∀^s)
   holds on the nose, the quantifiers being computed fibrewise with the
   reindexed reference measure m ∘ f. *)
Section beck_chevalley.
Context (X X' Y : Type) (f : X' -> X).

Definition base_change (ψ : X * Y -> prop R) : X' * Y -> prop R :=
  fun u => ψ (f u.1, u.2).

Lemma qexists_bc s (m : X -> WT W Y) ψ :
  qexists s (m \o f) (base_change ψ) = fun x' => qexists s m ψ (f x').
Proof. by []. Qed.

Lemma qforall_bc s (m : X -> WT W Y) ψ :
  qforall s (m \o f) (base_change ψ) = fun x' => qforall s m ψ (f x').
Proof. by []. Qed.

End beck_chevalley.

Arguments base_change {X X' Y} f ψ.

(* The adjunctions, for a non-expansive reference measure m : X -o W Y and
   the kernel product mu ⋈ m as the reference measure on X × Y. *)
Section kernel_product.
Context (X Y : pseudoMetricType R).
Implicit Types (s : Ω R) (mu : WT W X) (m : X -o wsp W Y) (φ χ : X -> prop R)
  (ψ : X * Y -> prop R) (Ψ : seq (X -> prop R)).

(* The kernel product mu ⋈ m on X × Y (x ~ mu, y ~ m x): the join of the
   pushforward of mu along the pairing kernel x ↦ δ_x ⊗ m x, which is
   2-Lipschitz (as the diagonal of X ⊗ X), hence a morphism out of 2 X. *)
Lemma pair_ne (x : X) : @nonexpansive R Y (tensor X Y) (fun y => (x, y)).
Proof.
by apply/nonexpansiveP => y y'; rw tensor_edistE /= edist_refl add0e lexx.
Qed.

Definition pair_nemap x : Y -o tensor X Y := NEMap (pair_ne x).

Lemma two_ge0 : (0 : \bar R) <= 2%:R%:E.
Proof. by rw lee_fin ler0n. Qed.

Definition two : Ω R := mkprop two_ge0.

Lemma wpair_kernel_ne m : @nonexpansive R (scale two X) (wsp W (tensor X Y))
  (fun x => wmap W (pair_nemap x) (m x)).
Proof.
apply/nonexpansiveP => x x'; rw scale_edistE /two mkpropE mule_natl mule2n.
apply: le_trans (edist_triangle _ (wmap W (pair_nemap x') (m x) :
  wsp W (tensor X Y)) _) _.
apply: leeD.
  by apply: wmap_bound => y; rw tensor_edistE /pair_nemap /= edist_refl adde0 lexx.
by apply: le_trans (wmap_dist W (pair_nemap x') (m x) (m x')) _; exact: nemapP.
Qed.

Definition wpair mu m : WT W (X * Y) :=
  wjoin W (wmap W (NEMap (wpair_kernel_ne m)) (mu : WT W (scale two X))).

(* Fubini: the means over mu ⋈ m are the iterated means. *)
Lemma wmean_pair s mu m (g : X * Y -> prop R) :
  wmean M s (wpair mu m) g =
  wmean M s mu (fun x => wmean M s (m x) (fun y => g (x, y))).
Proof.
rw /wpair wmean_join (wmean_map M s (NEMap (wpair_kernel_ne m)) mu).
congr wmean; apply/funext => x /=.
by rw (wmean_map M s (pair_nemap x) (m x)).
Qed.

(* ∃^s ⊣ π^* at grade s: [∃^s_m ψ, φ]_mu = [ψ, π^* φ]_(mu ⋈ m). *)
Theorem qexists_adj s mu m ψ φ :
  phom M s mu (qexists s m ψ) φ = phom M s (wpair mu m) ψ (reindex φ).
Proof.
rw /phom /hmean wmean_pair; congr pstar; congr wmean; apply/funext => x.
rw /reindex /= pstar_imp ptensC /qexists -wmean_tens; congr wmean.
by apply/funext => y; rw pstar_imp ptensC.
Qed.

(* π^* ⊣ ∀^s at grade s: [φ, ∀^s_m ψ]_mu = [π^* φ, ψ]_(mu ⋈ m). *)
Theorem qforall_adj s mu m φ ψ :
  phom M s mu φ (qforall s m ψ) = phom M s (wpair mu m) (reindex φ) ψ.
Proof.
rw /phom /hmean wmean_pair; congr pstar; congr wmean; apply/funext => x.
rw /reindex /= pstar_imp /qforall /hmean pstarK -wmean_tens; congr wmean.
by apply/funext => y; rw pstar_imp.
Qed.

(* The unit ψ ⊢_s π^* ∃^s ψ and the counit π^* ∀^s ψ ⊢_s ψ are valid at
   grade s. *)
Lemma qexists_unit s mu m ψ :
  ptrue (phom M s (wpair mu m) ψ (reindex (qexists s m ψ))).
Proof. by rw -qexists_adj; exact: phom_refl. Qed.

Lemma qforall_counit s mu m ψ :
  ptrue (phom M s (wpair mu m) (reindex (qforall s m ψ)) ψ).
Proof. by rw -qforall_adj; exact: phom_refl. Qed.

(* The rules (∀ˢ-I) and (∃ˢ-E) of the entailment at the semantic level, with
   the reference measure mu ⋈ m on the extended context: the adjunctions at
   the truth threshold, hence invertible. *)
Lemma qforall_I s mu m Ψ ψ :
  ptrue (phom M s (wpair mu m) (ptens_all (map reindex Ψ)) ψ) <->
  ptrue (phom M s mu (ptens_all Ψ) (qforall s m ψ)).
Proof. by rw ptens_all_reindex -qforall_adj. Qed.

Lemma qexists_E s mu m Ψ ψ χ :
  ptrue (phom M s (wpair mu m) (ptens_all (ψ :: map reindex Ψ)) (reindex χ))
  <-> ptrue (phom M s mu (ptens_all (qexists s m ψ :: Ψ)) χ).
Proof.
suff -> : phom M s (wpair mu m) (ptens_all (ψ :: map reindex Ψ)) (reindex χ)
    = phom M s mu (ptens_all (qexists s m ψ :: Ψ)) χ by [].
transitivity
    (phom M s (wpair mu m) ψ (reindex (fun x => ptens_all Ψ x ⊸ χ x))).
  rw /phom; congr hmean; apply/funext => u.
  by rw ptens_all_cons ptens_all_reindex /reindex /= pimp_tens.
rw -qexists_adj /phom; congr hmean; apply/funext => x.
by rw ptens_all_cons pimp_tens.
Qed.

(* The change of variables along id × g : X × Y -> X × Y', which pushes the
   reference measure forward: ∃^s (y' ~ g_* m) ψ = ∃^s (y ~ m) ψ (g y). *)
Lemma qexists_map (Y' : pseudoMetricType R) s (m : X -> WT W Y) (g : Y -o Y')
    (ψ : X * Y' -> prop R) :
  qexists s (fun x => wmap W g (m x)) ψ = qexists s m (fun u => ψ (u.1, g u.2)).
Proof. by apply/funext => x; rw /qexists (wmean_map M s g (m x)). Qed.

Lemma qforall_map (Y' : pseudoMetricType R) s (m : X -> WT W Y) (g : Y -o Y')
    (ψ : X * Y' -> prop R) :
  qforall s (fun x => wmap W g (m x)) ψ = qforall s m (fun u => ψ (u.1, g u.2)).
Proof. by apply/funext => x; rw /qforall /hmean (wmean_map M s g (m x)). Qed.

End kernel_product.

End QuantAdjoint.
