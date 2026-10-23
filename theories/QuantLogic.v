(* The internal logic of the calculus (paper, Sect. "Logic"): the truth values
   Prop = [0, +oo] and their connectives, the predicates and their typing, the
   graded entailment and its rules, and their semantics.  No property is
   proved here. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import sequences exp.
From ExtMetQLL Require Import analysis_extras extmet cextmet syntax semantics.

(**md**************************************************************************)
(* # The quantitative logic                                                   *)
(*                                                                            *)
(* Predicates are terms of type Prop, the truth values [0, +oo] with the log  *)
(* metric, and reasoning is a graded entailment Δ ∣ Ψ ⊢[ p ] φ whose grade p  *)
(* is the softness.  Everything is defined; the only properties proved are   *)
(* those of the equality predicate (an equivalence, substitutive for the     *)
(* predicates non-expansive for the log metric).  The pseudometric structure *)
(* of Prop, the non-expansiveness of the connectives and of ⟦φ⟧, and the     *)
(* soundness of the entailment are left as TODOs.                            *)
(*                                                                            *)
(* ```                                                                        *)
(*            prop R == the truth values [0, +oo], the carrier of Ω with the  *)
(*                      log metric prop_dist; ptrue a == 1 <= a and         *)
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
(*            pred R == the predicates φ, ψ ::= ⊤ | ⊥ | t =[ A ] u | φ ⊗ ψ   *)
(*                      | φ ⅋ ψ (⊗* ) | φ ⊸ ψ | r *: φ | φ ^* | φ ∨[ s ] ψ    *)
(*                      | φ ∧[ s ] ψ | ∀[ s ] m , φ | ∃[ s ] m , φ            *)
(*                      (pred_scope, %pred; the quantified variable is #0)   *)
(*   tm_shift k t, pred_shift k φ == the de Bruijn lifting of the variables  *)
(*                      >= k                                                  *)
(*       Γ ⊩[ σ ] φ == the predicate typing ptyped Γ σ φ (Γ ⊢ φ : Prop)      *)
(*        discrete Δ == the environment of the discrete context Δ (all +oo)  *)
(*   Δ ∣ Ψ ⊢[ p ] φ == the graded entailment entails Δ Ψ p φ; logical        *)
(*                      contexts are lists, last formula first               *)
(*          wmeans W == the s-means (∫ g^s dm)^(1/s) of the monad, the       *)
(*                      interpretation of the quantifiers                    *)
(*       psem W M d == ⟦Γ ⊩ φ⟧ : ⟦Γ⟧ -> Prop, by recursion on d              *)
(*  valid W M mu p Ψ φ == 1 <= ∫^(-p)_(γ ~ mu) (⊗Ψ ⊸ φ)(γ), the validity of  *)
(*                      the entailment under the reference measure mu on ⟦Δ⟧ *)
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

(* Prop = [0, +oo]: the carrier of the sensitivities Ω (the paper's Ω), as a
   separate type since it carries the log metric. *)
Definition prop (R : realType) : Type := {nonneg \bar R}.

Section truth_values.
Context {R : realType}.
Implicit Types (a b : prop R) (x d : \bar R).

(* Truth values from non-negative extended reals. *)
Lemma mkprop_subproof x : 0 <= x ->
  Itv.spec (@ext_num_sem R) (Itv.Real `[0, +oo[%R) x.
Proof.
by move=> x0; rw /Itv.spec /= /ext_num_sem /= /Order.comparable in_itv /= x0.
Qed.

Definition mkprop x (x0 : 0 <= x) : prop R := Itv.mk (mkprop_subproof x0).

Lemma mkpropE x (x0 : 0 <= x) : (mkprop x0)%:num = x. Proof. by []. Qed.

Definition ptop : prop R := (+oo : \bar R)%:nng.
Definition pbot : prop R := (0%R%:E)%:nng.
Definition pone : prop R := 1%:E%:nng.

(* a is true iff 1 <= a, and a ⊢ b (a ⊑ b) iff a <= b. *)
Definition ptrue a : Prop := 1 <= a%:num.
Definition ple a b : Prop := a%:num <= b%:num.

(* a ⊗ b = a b, with 0 ⊗ +oo = 0 (the convention of mule). *)
Definition ptens a b : prop R := (a%:num * b%:num)%:nng.

(* The involution a* = 1 / a, with 0* = +oo and (+oo)* = 0. *)
Definition estar x : \bar R :=
  if x == 0 then +oo else if x == +oo then 0 else ((fine x)^-1)%:E.

Lemma estar_ge0 x : 0 <= x -> 0 <= estar x.
Proof.
rw /estar; case: ifP => // _; case: ifP => // _ x0.
by rw lee_fin invr_ge0 fine_ge0.
Qed.

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

(* The log metric d(a, b) = |ln a - ln b|, the crisp values 0 and +oo at
   infinite distance from the soft ones.  TODO: the pseudometric instance of
   prop R and the non-expansiveness of the connectives. *)
Definition prop_dist a b : \bar R :=
  if a == b then 0 else
  if (0 < a%:num < +oo) && (0 < b%:num < +oo) then
    `|ln (fine a%:num) - ln (fine b%:num)|%:E
  else +oo.

(* The harmonic sum of grades p ⊕* q = (p^-1 + q^-1)^-1, with unit +oo. *)
Definition hsum (p q : Ω R) : Ω R := pstar (sens_add (pstar p) (pstar q)).

End truth_values.

Arguments prop : clear implicits.

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

(* The environment of a discrete context: every variable at sensitivity +oo. *)
Definition discrete (Δ : seq (ty R)) : senv R := nseq (size Δ) sensy.

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
   connectives sum their contexts and a quantifier binds its variable at its
   grade s. *)
Inductive ptyped : seq (ty R) -> senv R -> pred R -> Type :=
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

| ptyped_forall Γ σ τ φ m A s :
    A :: Γ ⊩[ s :: σ ] φ ->
    Γ ⊢[ τ ] m : 𝕎 A ->
    (*———————————————————————————— (∀ˢᵢ) *)
    Γ ⊩[ σ ⧺ τ ] ∀[s] m , φ

| ptyped_exists Γ σ τ φ m A s :
    A :: Γ ⊩[ s :: σ ] φ ->
    Γ ⊢[ τ ] m : 𝕎 A ->
    (*———————————————————————————— (∃ˢᵢ) *)
    Γ ⊩[ σ ⧺ τ ] ∃[s] m , φ
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
   and composition the harmonic sum under cut.  The quantifier rules shift
   the formulas that must not mention the bound variable. *)
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
   through the involution.  TODO: non-expansiveness in g (sup-log metric, every
   s) and in m (Kantorovich). *)
Record wmeans (R : realType) (W : wmonad R) := WMeans {
  wmean : forall X : pseudoMetricType R, Ω R -> WT W X -> (X -> prop R) -> prop R
}.

Arguments wmean {R W} w {X} s mu g.

Section logic_semantics.
Context {R : realType} (W : wmonad R) (M : wmeans W).
Local Open Scope prop_scope.

(* The harmonic s-mean (∫ g^(-s) dm)^(-1/s) = ((∫ (g* )^s dm)^(1/s))*. *)
Definition hmean (X : pseudoMetricType R) (s : Ω R) (mu : WT W X)
  (g : X -> prop R) : prop R := (wmean M s mu (fun x => (g x)^*))^*.

(* ⟦Γ ⊩ φ⟧ : ⟦Γ⟧ -> Prop, the clauses of the paper with split the identity
   on the common carrier of the contexts; r φ is the power a^r.  TODO:
   non-expansiveness for the log metric. *)
Fixpoint psem Γ σ φ (d : Γ ⊩[ σ ] φ) : ctxC W Γ σ -> prop R :=
  match d in ptyped Γ σ φ return ctxC W Γ σ -> prop R with
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
  | ptyped_forall Γ σ τ φ m A s dφ dm =>
    fun γ => hmean s (sem W dm γ) (fun a : sem_ty W A => psem dφ (γ, a))
  | ptyped_exists Γ σ τ φ m A s dφ dm =>
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

(* ⊗Ψ, the tensor of an interpreted logical context. *)
Definition ptens_all (E : Type) (Ψ : seq (E -> prop R)) (γ : E) : prop R :=
  foldr (fun ψ a => ψ γ ⊗ a) pone Ψ.

(* The validity of Δ ∣ Ψ ⊢_p φ under a reference measure mu on ⟦Δ⟧: the
   harmonic p-mean of the implication (⊗Ψ) ⊸ φ is true, 1 <= ∫^(-p) (⊗Ψ ⊸ φ);
   p = +oo is the hard entailment on the support of mu.  TODO: soundness of
   the rules of entails. *)
Definition valid (Δ : seq (ty R)) (mu : WT W (ctxC W Δ (discrete Δ)))
    (p : Ω R) (Ψ : seq (ctxC W Δ (discrete Δ) -> prop R))
    (φ : ctxC W Δ (discrete Δ) -> prop R) : Prop :=
  ptrue (hmean p mu (fun γ => ptens_all Ψ γ ⊸ φ γ)).

End logic_semantics.
