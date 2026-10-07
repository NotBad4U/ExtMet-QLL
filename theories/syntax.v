(* Syntax and typing rules of the calculus for CExtMet (paper, Sect. "A
   calculus for CExtMet"). *)
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From ExtMetQLL Require Import analysis_extras.

(**md**************************************************************************)
(* # Syntax of the calculus for CExtMet                                       *)
(*                                                                            *)
(* Types, terms and the typing judgement of the graded lambda-calculus of    *)
(* the paper.  Variables are de Bruijn indices.  A context                   *)
(* Γ = x_1 :^{r_1} A_1, ..., x_n :^{r_n} A_n of the paper is split into its   *)
(* skeleton Γ : seq ty and its sensitivities σ : senv, both with the last    *)
(* binding first: Γ, x :^r A is A :: Γ together with r :: σ, and x is the    *)
(* variable 0.  All the contexts of a rule share the skeleton, so that the   *)
(* sum Γ ⧺ Γ' and the scaling rΓ of the paper (only defined on contexts over *)
(* the same variables) are the pointwise operations ⧺ and *: on σ.           *)
(* Weakening is implicit, as in the paper: the leaf rules accept arbitrary   *)
(* sensitivities, and only a variable that is used needs r >= 1.             *)
(*                                                                            *)
(* The scalars are those of the semantics: sensitivities are the scalars of  *)
(* scale (cextmet.v), contraction factors those of econtraction (extmet.v,   *)
(* fixpoint.v) and probabilities those of the convex combinations of the     *)
(* Wasserstein space (wasserstein.v).                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*            sens R == sensitivities r in [0, +oo], i.e. {nonneg \bar R};   *)
(*                      sens0, sens1, sensy are 0, 1, +oo and                 *)
(*                      sens_add, sens_mul the sum and product (0 * oo = 0)   *)
(*            prob R == probabilities p in ]0, 1[, i.e. {itv R & `]0, 1[}    *)
(*           contr R == contraction factors r in [0, 1[,                      *)
(*                      i.e. {itv \bar R & `[0, 1[}                            *)
(*   prob_sens p, prob_sensC p == p and 1 - p as sensitivities                *)
(*   contr_sens r, contr_sensC r == r and 1 - r as sensitivities              *)
(*              ty R == types A, B ::= ty_nat | ty_unit | A * B | A + B       *)
(*                      | A ⊗[ r , s ] B | A ⊸[ r ] B | ty_dist A              *)
(*                      (notations in ty_scope, delimiter %ty);              *)
(*                      A ⊗[ r , s ] B is rA ⊗ sB and A ⊸[ r ] B is rA ⊸ B     *)
(*           ib_ty E == E denotes an interpolative barycentric algebra       *)
(*              tm R == terms, with de Bruijn indices                         *)
(*            senv R == sensitivity environments σ : seq (sens R)             *)
(*     σ ⧺ τ, r *: σ == the sum and the scaling of contexts (senv_scope)      *)
(*   Γ ⊢[ σ ] t : A == the typing judgement typed Γ σ t A                      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Reserved Notation "A ⊗[ r , s ] B"
  (at level 40, left associativity, format "A  ⊗[ r ,  s ]  B").
Reserved Notation "A ⊸[ r ] B"
  (at level 65, right associativity, format "A  ⊸[ r ]  B").
Reserved Notation "σ ⧺ τ" (at level 50, left associativity).
Reserved Notation "Γ ⊢[ σ ] t : A"
  (at level 70, t at level 99, A at level 69,
   format "Γ  ⊢[ σ ]  t  :  A").

(** * Scalars *)

Section scalars.
Context {R : realType}.

(* Sensitivities r in [0, +oo], the scalars of the scaling functor. *)
Definition sens : Type := {nonneg \bar R}.

(* Probabilities p in ]0, 1[, the parameters of the convex combinations. *)
Definition prob : Type := {itv R & `]0, 1[}.

(* Contraction factors r in [0, 1[, the parameters of the guarded fixed
   points. *)
Definition contr : Type := {itv \bar R & `[0, 1[}.

Definition sens0 : sens := (0%R%:E)%:nng.
Definition sens1 : sens := 1%:E%:nng.
Definition sensy : sens := (+oo : \bar R)%:nng.

(* The sum and the product of sensitivities, with 0 * +oo = 0 (the
   convention of scale).  They are written with adde and oppe below because
   interval inference does not see through the generic + and - of
   ereal_scope. *)
Definition sens_add (r s : sens) : sens := (adde r%:num s%:num)%:nng.
Definition sens_mul (r s : sens) : sens := (r%:num * s%:num)%:nng.

Definition prob_sens (p : prob) : sens := (p%:num%:E)%:nng.
Definition prob_sensC (p : prob) : sens := ((1 - p%:num)%:E)%:nng.

Definition contr_sens (r : contr) : sens := (r%:num)%:nng.
Definition contr_sensC (r : contr) : sens := (adde 1 (oppe r%:num))%:nng.

Lemma sens0E : sens0%:num = 0. Proof. by []. Qed.
Lemma sens1E : sens1%:num = 1. Proof. by []. Qed.
Lemma sensyE : sensy%:num = +oo. Proof. by []. Qed.

Lemma sens_addE r s : (sens_add r s)%:num = r%:num + s%:num. Proof. by []. Qed.
Lemma sens_mulE r s : (sens_mul r s)%:num = r%:num * s%:num. Proof. by []. Qed.

Lemma prob_sensE p : (prob_sens p)%:num = p%:num%:E. Proof. by []. Qed.
Lemma prob_sensCE p : (prob_sensC p)%:num = (1 - p%:num)%:E. Proof. by []. Qed.

Lemma contr_sensE r : (contr_sens r)%:num = r%:num. Proof. by []. Qed.
Lemma contr_sensCE r : (contr_sensC r)%:num = 1 - r%:num. Proof. by []. Qed.

Lemma prob_sens_gt0 p : 0 < (prob_sens p)%:num.
Proof. by rw prob_sensE lte_fin. Qed.

Lemma prob_sensC_gt0 p : 0 < (prob_sensC p)%:num.
Proof. by rw prob_sensCE lte_fin subr_gt0. Qed.

Lemma contr_sens_lt1 r : (contr_sens r)%:num < 1.
Proof. by rw contr_sensE; case: r => x /= /andP[_]; rw /= in_itv /= => /andP[]. Qed.

End scalars.

Arguments sens : clear implicits.
Arguments prob : clear implicits.
Arguments contr : clear implicits.

(** * Types, terms and contexts *)

Section syntax.
Context {R : realType}.

(* Types.  The rescaling of spaces is not a type former: it is built into the
   tensor and the function types, ty_tensor r A s B = rA ⊗ sB and
   ty_lolli r A B = rA ⊸ B. *)
Inductive ty : Type :=
| ty_nat                                  (* N *)
| ty_unit                                 (* 1 *)
| ty_prod of ty & ty                      (* A × B, the cartesian product *)
| ty_sum of ty & ty                       (* A + B *)
| ty_tensor of sens R & ty & sens R & ty  (* A ⊗[r, s] B = rA ⊗ sB *)
| ty_lolli of sens R & ty & ty            (* A ⊸[r] B = rA ⊸ B *)
| ty_dist of ty.                          (* W A *)

(* The types whose denotation is an interpolative barycentric algebra, the
   side condition of the rule (LET): W A and the unit, closed under the
   cartesian and the monoidal products and under the exponentials, with the
   pointwise convex combinations.  N and the sums are excluded, two distinct
   points of N or of different summands being at distance +oo. *)
Fixpoint ib_ty (E : ty) : bool :=
  match E with
  | ty_nat | ty_sum _ _ => false
  | ty_unit | ty_dist _ => true
  | ty_prod A B | ty_tensor _ A _ B => ib_ty A && ib_ty B
  | ty_lolli _ _ B => ib_ty B
  end.

(* Terms, with de Bruijn indices: a binder binds the variable 0 of its body,
   and the binders of let (x, y) = u in t and rec (z, (x, y). s, n) bind x to
   1 and y to 0. *)
Inductive tm : Type :=
| tm_var of nat                 (* x *)
| tm_unit                       (* () *)
| tm_abs of tm                  (* λ x. t *)
| tm_app of tm & tm             (* t u *)
| tm_pair of tm & tm            (* ⟨t, u⟩ *)
| tm_proj1 of tm                (* π_1 t *)
| tm_proj2 of tm                (* π_2 t *)
| tm_inj1 of tm                 (* inj_1 t *)
| tm_inj2 of tm                 (* inj_2 t *)
| tm_case of tm & tm & tm       (* case t of inj_1 x => u | inj_2 y => v *)
| tm_tensor of tm & tm          (* (t, u) *)
| tm_lettensor of tm & tm       (* let (x, y) = u in t *)
| tm_dirac of tm                (* δ t *)
| tm_choice of prob R & tm & tm (* t ⅋_p u *)
| tm_let of tm & tm             (* let x = u in t *)
| tm_zero                       (* zero *)
| tm_succ of tm                 (* succ t *)
| tm_natrec of tm & tm & tm     (* rec (z, (x, y). s, n); tm_rec is the
                                   recursion principle of tm *)
| tm_fix of tm.                 (* fix x. t *)

(* Sensitivity environments: the sensitivities of a context, last binding
   first. *)
Definition senv : Type := seq (sens R).

(* The sum Γ ⧺ Γ' and the scaling rΓ of contexts over the same variables. *)
Definition senv_add (σ τ : senv) : senv :=
  [seq sens_add p.1 p.2 | p <- zip σ τ].

Definition senv_scale (r : sens R) (σ : senv) : senv :=
  [seq sens_mul r s | s <- σ].

End syntax.

Arguments ty : clear implicits.
Arguments tm : clear implicits.
Arguments senv : clear implicits.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

Notation "A * B" := (ty_prod A B) : ty_scope.
Notation "A + B" := (ty_sum A B) : ty_scope.
Notation "A ⊗[ r , s ] B" := (ty_tensor r A s B) : ty_scope.
Notation "A ⊸[ r ] B" := (ty_lolli r A B) : ty_scope.

Declare Scope senv_scope.
Delimit Scope senv_scope with senv.
Bind Scope senv_scope with senv.

Notation "σ ⧺ τ" := (senv_add σ τ) : senv_scope.
Notation "r *: σ" := (senv_scale r σ) : senv_scope.

Local Open Scope senv_scope.

Section senv_theory.
Context {R : realType}.
Implicit Types (r s : sens R) (σ τ : senv R).

(* The defining equations of the paper. *)
Lemma senv_add_nil : [::] ⧺ [::] = [::] :> senv R. Proof. by []. Qed.

Lemma senv_scale_nil r : r *: [::] = [::] :> senv R. Proof. by []. Qed.

Lemma senv_add_cons r s σ τ : (r :: σ) ⧺ (s :: τ) = sens_add r s :: σ ⧺ τ.
Proof. by []. Qed.

Lemma senv_scale_cons r s σ : r *: (s :: σ) = sens_mul r s :: r *: σ.
Proof. by []. Qed.

Lemma size_senv_add σ τ : size (σ ⧺ τ) = minn (size σ) (size τ).
Proof. by rw size_map size_zip. Qed.

Lemma size_senv_scale r σ : size (r *: σ) = size σ.
Proof. by rw size_map. Qed.

Lemma nth_senv_add σ τ i : size σ = size τ -> (i < size σ)%N ->
  nth sens0 (σ ⧺ τ) i = sens_add (nth sens0 σ i) (nth sens0 τ i).
Proof.
move=> st si; rw (nth_map (sens0, sens0)) ?size_zip -?st ?minnn //.
by rw nth_zip.
Qed.

Lemma nth_senv_scale r σ i : (i < size σ)%N ->
  nth sens0 (r *: σ) i = sens_mul r (nth sens0 σ i).
Proof. by move=> si; rw (nth_map sens0). Qed.

End senv_theory.

(** * Typing *)

Section typing.
Context {R : realType}.
Implicit Types (Γ : seq (ty R)) (σ τ ρ : senv R) (t u v z step n : tm R)
  (A B C E : ty R) (r s : sens R) (p : prob R).

(* Γ ⊢[ σ ] t : A, for Γ and σ of the same length (typed_size).  Derivations
   live in Type so that the semantics (semantics.v) is defined by recursion
   on them, as in the paper.  The rules
   are those of the paper, with the context Γ, x :^r A read as A :: Γ and
   r :: σ.  The rule (LET-⊗) is read with the scalars of the type matching
   those of the bound variables, x :^r A, y :^s B for u : A ⊗[r, s] B, and
   with u the pair and t the body, which is what its semantics computes. *)
Inductive typed : seq (ty R) -> senv R -> tm R -> ty R -> Type :=
| typed_var Γ σ i A :
    (i < size Γ)%N -> nth ty_unit Γ i = A -> 1 <= (nth sens0 σ i)%:num ->
    size σ = size Γ ->
    Γ ⊢[ σ ] tm_var i : A
| typed_abs Γ σ t A B r :
    A :: Γ ⊢[ r :: σ ] t : B ->
    Γ ⊢[ σ ] tm_abs t : A ⊸[r] B
| typed_app Γ σ τ t u A B r :
    Γ ⊢[ σ ] t : A ⊸[r] B -> Γ ⊢[ τ ] u : A ->
    Γ ⊢[ σ ⧺ r *: τ ] tm_app t u : B
| typed_unit Γ σ :
    size σ = size Γ ->
    Γ ⊢[ σ ] tm_unit : ty_unit
| typed_pair Γ σ t u A B :
    Γ ⊢[ σ ] t : A -> Γ ⊢[ σ ] u : B ->
    Γ ⊢[ σ ] tm_pair t u : A * B
| typed_proj1 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 * A2 ->
    Γ ⊢[ σ ] tm_proj1 t : A1
| typed_proj2 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 * A2 ->
    Γ ⊢[ σ ] tm_proj2 t : A2
| typed_inj1 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 ->
    Γ ⊢[ σ ] tm_inj1 t : A1 + A2
| typed_inj2 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A2 ->
    Γ ⊢[ σ ] tm_inj2 t : A1 + A2
| typed_case Γ σ τ t u v A B C r :
    Γ ⊢[ τ ] t : A + B ->
    A :: Γ ⊢[ r :: σ ] u : C -> B :: Γ ⊢[ r :: σ ] v : C -> 0 < r%:num ->
    Γ ⊢[ σ ⧺ r *: τ ] tm_case t u v : C
| typed_tensor Γ σ τ ρ t u A B r s :
    Γ ⊢[ σ ] t : A -> Γ ⊢[ τ ] u : B -> size ρ = size Γ ->
    Γ ⊢[ r *: σ ⧺ s *: τ ⧺ ρ ] tm_tensor t u : A ⊗[r, s] B
| typed_lettensor Γ σ τ t u A B C r s :
    B :: A :: Γ ⊢[ s :: r :: σ ] t : C -> Γ ⊢[ τ ] u : A ⊗[r, s] B ->
    Γ ⊢[ σ ⧺ τ ] tm_lettensor u t : C
| typed_dirac Γ σ t A :
    Γ ⊢[ σ ] t : A ->
    Γ ⊢[ σ ] tm_dirac t : ty_dist A
| typed_choice Γ σ τ t u A p :
    Γ ⊢[ σ ] t : ty_dist A -> Γ ⊢[ τ ] u : ty_dist A ->
    Γ ⊢[ prob_sens p *: σ ⧺ prob_sensC p *: τ ] tm_choice p t u : ty_dist A
| typed_let Γ σ τ t u A E r :
    A :: Γ ⊢[ r :: σ ] t : E -> Γ ⊢[ τ ] u : ty_dist A ->
    ib_ty E -> r%:num < +oo ->
    Γ ⊢[ σ ⧺ r *: τ ] tm_let u t : E
| typed_zero Γ σ :
    size σ = size Γ ->
    Γ ⊢[ σ ] tm_zero : ty_nat
| typed_succ Γ σ t :
    Γ ⊢[ σ ] t : ty_nat ->
    Γ ⊢[ σ ] tm_succ t : ty_nat
| typed_natrec Γ σ τ ρ z step n A :
    Γ ⊢[ σ ] z : A -> ty_nat :: A :: Γ ⊢[ sens1 :: sens1 :: τ ] step : A ->
    Γ ⊢[ ρ ] n : ty_nat ->
    Γ ⊢[ σ ⧺ sensy *: τ ⧺ ρ ] tm_natrec z step n : A
(* (FIX): the premise (1 - r)Γ, x :^r A ⊢ t : A with r < 1.  Its semantics
   needs, in addition, a seed at finite displacement or a single-galaxy
   codomain (fixpoint.v). *)
| typed_fix Γ σ t A (r : contr R) :
    A :: Γ ⊢[ contr_sens r :: contr_sensC r *: σ ] t : A ->
    Γ ⊢[ σ ] tm_fix t : A
where "Γ ⊢[ σ ] t : A" := (typed Γ σ t A).

Let size_cons_inj {T U : Type} {x : T} {y : U} {s : seq T} {t : seq U} :
  size (x :: s) = size (y :: t) -> size s = size t.
Proof. by move=> /= []. Qed.

(* Typed terms have as many sensitivities as variables. *)
Lemma typed_size Γ σ t A : Γ ⊢[ σ ] t : A -> size σ = size Γ.
Proof.
elim=> {Γ σ t A} //.
- by move=> Γ σ t A B r _ H; exact: (size_cons_inj H).
- move=> Γ σ τ t u A B r _ sG _ tG.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ t u v A B C r _ tG _ H _ _ _; have sG := size_cons_inj H.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ ρ t u A B r s _ sG _ tG rG.
  by rw !size_senv_add !size_senv_scale sG tG rG !minnn.
- move=> Γ σ τ t u A B C r s _ H _ tG.
  have sG := size_cons_inj (size_cons_inj H).
  by rw size_senv_add sG tG minnn.
- move=> Γ σ τ t u A p _ sG _ tG.
  by rw size_senv_add !size_senv_scale sG tG minnn.
- move=> Γ σ τ t u A E r _ H _ tG _ _; have sG := size_cons_inj H.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ ρ z step n A _ sG _ H _ rG.
  have tG := size_cons_inj (size_cons_inj H).
  by rw !size_senv_add size_senv_scale sG tG rG !minnn.
- move=> Γ σ t A r _ H; move: (size_cons_inj H).
  by rw size_senv_scale.
Qed.

Lemma typed_size_cons Γ σ t A B r : A :: Γ ⊢[ r :: σ ] t : B -> size σ = size Γ.
Proof. by move/typed_size => /= []. Qed.

Lemma typed_size_cons2 Γ σ t A B C r s :
  B :: A :: Γ ⊢[ s :: r :: σ ] t : C -> size σ = size Γ.
Proof. by move/typed_size => /= []. Qed.

(* The identity, λ x. x : A ⊸[r] A for every r >= 1 (a transparent derivation,
   so that its semantics computes). *)
Example typed_id A r : 1 <= r%:num -> [::] ⊢[ [::] ] tm_abs (tm_var 0) : A ⊸[r] A.
Proof. by move=> r1; apply/typed_abs/typed_var. Defined.

End typing.

Notation "Γ ⊢[ σ ] t : A" := (typed Γ σ t A) : type_scope.
