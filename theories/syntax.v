(* Syntax and typing rules of the calculus for CExtMet (paper, Sect. "A
   calculus for CExtMet"). *)
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From ExtMetQLL Require Import analysis_extras propmetric.

(**md**************************************************************************)
(* # Syntax of the calculus for CExtMet                                       *)
(*                                                                            *)
(* Types, terms and the typing judgement of the graded lambda-calculus of    *)
(* the paper.  Variables are de Bruijn indices.  A context                   *)
(* Γ = x_1 :^{r_1}_{s_1} A_1, ..., x_n :^{r_n}_{s_n} A_n of the paper is     *)
(* split into its skeleton Γ : seq ty and its entries σ : senv, both with    *)
(* the last binding first: Γ, x :^r_s A is A :: Γ together with              *)
(* CEntry r s :: σ, and x is the variable 0.  Every variable carries two     *)
(* independent grades: a sensitivity r (superscript), the scalar of the      *)
(* metric r⟦A⟧ it is read at, and a softness s (subscript), the exponent     *)
(* of the mean a quantifier of the logic (QuantLogic.v) averages it with.    *)
(* The terms only use the sensitivities (the semantics ignores esoft): a     *)
(* term binder leaves the softness of its variable free, and only a          *)
(* quantifier records the softness of the variable it binds.  All the        *)
(* contexts of a rule share the skeleton, so that the sum Γ ⧺ Γ' and the     *)
(* scaling rΓ of the paper (only defined on contexts over the same           *)
(* variables) are the pointwise operations ⧺ and *: on σ: ⧺ adds the         *)
(* sensitivities and takes the harmonic sum of the softnesses (the           *)
(* composition of grades under cut), *: scales the sensitivities only.       *)
(* Weakening is implicit, as in the paper: the leaf rules accept arbitrary   *)
(* entries, and only a variable that is used needs r >= 1.                   *)
(*                                                                            *)
(* The scalars are those of the semantics: sensitivities are the scalars of  *)
(* scale (cextmet.v), contraction factors those of econtraction (extmet.v,   *)
(* fixpoint.v) and probabilities those of the convex combinations of the     *)
(* Wasserstein space (wasserstein.v).                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*            Ω R == sensitivities r in [0, +oo], i.e. {nonneg \bar R};   *)
(*                      sens0, sens1, sensy are 0, 1, +oo and                 *)
(*                      sens_add, sens_mul the sum and product (0 * oo = 0)   *)
(*   ℙ_convex R, ]0,1[ R == probabilities p in ]0, 1[, {itv R & `]0, 1[} *)
(*           contr R == contraction factors r in [0, 1[,                      *)
(*                      i.e. {itv \bar R & `[0, 1[}                            *)
(*   prob_sens p, prob_sensC p == p (a coercion) and 1 - p as sensitivities,  *)
(*                      with sens_sub the truncated difference (omega_scope) *)
(*   contr_sens r, contr_sensC r == r and 1 - r as sensitivities              *)
(*   sens_hsum r s == the harmonic sum (r^-1 + s^-1)^-1 of softnesses         *)
(*              ty R == types A, B ::= ℕ | unit | A × B | A + B               *)
(*                      | A ⊗[ r , s ] B | A ⊸[ r ] B | 𝕎 A | Prop            *)
(*                      (notations in ty_scope, delimiter %ty);              *)
(*                      A ⊗[ r , s ] B is rA ⊗ sB and A ⊸[ r ] B is rA ⊸ B;    *)
(*                      Prop is ty_prop, the truth values                  *)
(*           ib_ty E == E denotes an interpolative barycentric algebra       *)
(*              tm R == terms, with de Bruijn indices (notations in          *)
(*                      tm_scope, delimiter %tm)                              *)
(*          centry R == context entries CEntry r s: a sensitivity esens and  *)
(*                      a softness esoft, both in Ω R; centry0 = (0, +oo)    *)
(*                      is the unit of their sum                             *)
(*            senv R == context environments σ : seq (centry R)              *)
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
Definition Ω : Type := {nonneg \bar R}.

(* Probabilities p in ]0, 1[, the parameters of the convex combinations. *)
Definition ℙ_convex : Type := {itv R & `]0, 1[}.

(* Contraction factors r in [0, 1[, the parameters of the guarded fixed
   points. *)
Definition contr : Type := {itv \bar R & `[0, 1[}.

Definition sens0 : Ω := (0%R%:E)%:nng.
Definition sens1 : Ω := 1%:E%:nng.
Definition sensy : Ω := (+oo : \bar R)%:nng.

(* The sum and the product of sensitivities, with 0 * +oo = 0 (the
   convention of scale).  They are written with adde and oppe below because
   interval inference does not see through the generic + and - of
   ereal_scope. *)
Definition sens_add (r s : Ω) : Ω := (adde r%:num s%:num)%:nng.
Definition sens_mul (r s : Ω) : Ω := (r%:num * s%:num)%:nng.

(* The truncated difference max (r - s) 0, written r - s in omega_scope. *)
Definition sens_sub (r s : Ω) : Ω :=
  (maxe (adde r%:num (oppe s%:num)) (0%R%:E))%:nng.

(* A probability is a sensitivity (a coercion), and 1 - p its complement. *)
Definition prob_sens (p : ℙ_convex) : Ω := (p%:num%:E)%:nng.
Coercion prob_sens : ℙ_convex >-> Ω.
Definition prob_sensC (p : ℙ_convex) : Ω := sens_sub sens1 (prob_sens p).

Definition contr_sens (r : contr) : Ω := (r%:num)%:nng.
Definition contr_sensC (r : contr) : Ω := (adde 1 (oppe r%:num))%:nng.

(* The harmonic sum r ⊕* s = (r^-1 + s^-1)^-1 of softnesses, with unit +oo,
   through the involution of [0, +oo] (estar, propmetric.v). *)
Definition sens_inv (r : Ω) : Ω := mkprop (estar_ge0 (ge0e r)).
Definition sens_hsum (r s : Ω) : Ω := sens_inv (sens_add (sens_inv r) (sens_inv s)).

Lemma sens0E : sens0%:num = 0. Proof. by []. Qed.
Lemma sens1E : sens1%:num = 1. Proof. by []. Qed.
Lemma sensyE : sensy%:num = +oo. Proof. by []. Qed.

Lemma sens_addE r s : (sens_add r s)%:num = r%:num + s%:num. Proof. by []. Qed.
Lemma sens_mulE r s : (sens_mul r s)%:num = r%:num * s%:num. Proof. by []. Qed.
Lemma sens_subE r s : (sens_sub r s)%:num = maxe (r%:num - s%:num) 0.
Proof. by []. Qed.

Lemma prob_sensE p : (prob_sens p)%:num = p%:num%:E. Proof. by []. Qed.
Lemma prob_sensCE p : (prob_sensC p)%:num = (1 - p%:num)%:E.
Proof.
have p1 : (p%:num <= 1)%R by exact/ltW/lt1.
by rw sens_subE sens1E prob_sensE -EFinB max_l // lee_fin subr_ge0.
Qed.

Lemma contr_sensE r : (contr_sens r)%:num = r%:num. Proof. by []. Qed.
Lemma contr_sensCE r : (contr_sensC r)%:num = 1 - r%:num. Proof. by []. Qed.

Lemma prob_sens_gt0 p : 0 < (prob_sens p)%:num.
Proof. by rw prob_sensE lte_fin. Qed.

Lemma prob_sensC_gt0 p : 0 < (prob_sensC p)%:num.
Proof. by rw prob_sensCE lte_fin subr_gt0. Qed.

Lemma contr_sens_lt1 r : (contr_sens r)%:num < 1.
Proof. by rw contr_sensE; case: r => x /= /andP[_]; rw /= in_itv /= => /andP[]. Qed.

End scalars.

Arguments Ω : clear implicits.
Arguments ℙ_convex : clear implicits.
Arguments contr : clear implicits.

(* 1 and the truncated difference on sensitivities, so that the rule (⅋ₚ)
   reads p *: σ ⧺ (1 - p) *: τ. *)
Declare Scope omega_scope.
Delimit Scope omega_scope with Ω.
Bind Scope omega_scope with Ω.

Notation "1" := sens1 : omega_scope.
Notation "r - s" := (sens_sub r s) : omega_scope.

(* The probabilities written as the open interval: ]0,1[ R (one token;
   MathComp's `]0, 1[ is the interval itself, and a keyword 1[ would break
   its `[0, 1[). *)
Notation "]0,1[ R" := (ℙ_convex R) (at level 0, R at level 0,
  format "]0,1[  R") : type_scope.

(** * Types, terms and contexts *)

Section syntax.
Context {R : realType}.

(* Types.  The rescaling of spaces is not a type former: it is built into the
   tensor and the function types, ty_tensor r A s B = rA ⊗ sB and
   ty_lolli r A B = rA ⊸ B. *)
Inductive ty : Type :=
| ℕ                                       (* N *)
| unit                                    (* 1 *)
| ty_prod of ty & ty                      (* A × B, the cartesian product *)
| ty_sum of ty & ty                       (* A + B *)
| ty_tensor of Ω R & ty & Ω R & ty  (* A ⊗[r, s] B = rA ⊗ sB *)
| ty_lolli of Ω R & ty & ty            (* A ⊸[r] B = rA ⊸ B *)
| ty_dist of ty                           (* W A *)
| ty_prop.                                (* Prop, the truth values *)

(* The types whose denotation is an interpolative barycentric algebra, the
   side condition of the rule (LET): W A and the unit, closed under the
   cartesian and the monoidal products and under the exponentials, with the
   pointwise convex combinations.  N and the sums are excluded, two distinct
   points of N or of different summands being at distance +oo; Prop is
   excluded too, the semantics having no algebra W Prop -> Prop. *)
Fixpoint ib_ty (E : ty) : bool :=
  match E with
  | ℕ | ty_sum _ _ | ty_prop => false
  | unit | ty_dist _ => true
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
| tm_choice of ]0,1[ R & tm & tm (* t ⅋_p u *)
| tm_let of tm & tm             (* let x = u in t *)
| tm_zero                       (* zero *)
| succ of tm                 (* succ t *)
| rec of tm & tm & tm           (* rec (z, (x, y). s, n) *)
| tm_fix of tm.                 (* fix x. t *)

(* A context entry x :^r_s A: the sensitivity r and the softness s of the
   variable, two independent grades in [0, +oo]. *)
Record centry : Type := CEntry { esens : Ω R; esoft : Ω R }.

(* The unit (0, +oo) of the sum of entries (the default of nth). *)
Definition centry0 : centry := CEntry sens0 sensy.

(* Two uses of a variable add their sensitivities and combine their
   softnesses by harmonic sum. *)
Definition centry_add (e e' : centry) : centry :=
  CEntry (sens_add (esens e) (esens e')) (sens_hsum (esoft e) (esoft e')).

(* Scaling a context scales the sensitivities and leaves the softnesses
   unchanged. *)
Definition centry_scale (r : Ω R) (e : centry) : centry :=
  CEntry (sens_mul r (esens e)) (esoft e).

(* Context environments: the entries of a context, last binding first. *)
Definition senv : Type := seq centry.

(* The sum Γ ⧺ Γ' and the scaling rΓ of contexts over the same variables. *)
Definition senv_add (σ τ : senv) : senv :=
  [seq centry_add p.1 p.2 | p <- zip σ τ].

Definition senv_scale (r : Ω R) (σ : senv) : senv :=
  [seq centry_scale r e | e <- σ].

End syntax.

Arguments ty : clear implicits.
Arguments tm : clear implicits.
Arguments centry : clear implicits.
Arguments senv : clear implicits.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

Notation "A × B" := (ty_prod A B) (at level 40, left associativity) : ty_scope.
Notation "A + B" := (ty_sum A B) : ty_scope.
Notation "A ⊗[ r , s ] B" := (ty_tensor r A s B) : ty_scope.
Notation "A ⊸[ r ] B" := (ty_lolli r A B) : ty_scope.
Notation "'𝕎' A" := (ty_dist A) (at level 10, format "𝕎  A") : ty_scope.

Declare Scope tm_scope.
Delimit Scope tm_scope with tm.
Bind Scope tm_scope with tm.

Notation "'#' i" := (tm_var i%N) (at level 0, i at level 0, format "# i")
  : tm_scope.
Notation "'λ' t" := (tm_abs t) (at level 35, right associativity, format "λ  t")
  : tm_scope.
Notation "t @ u" := (tm_app t u) (at level 60, format "t  @  u")
  : tm_scope.
Notation "⟨ t , u ⟩" := (tm_pair t u) (format "⟨ t ,  u ⟩") : tm_scope.
Notation "'π1' t" := (tm_proj1 t) (at level 35, right associativity, format "π1  t")
  : tm_scope.
Notation "'π2' t" := (tm_proj2 t) (at level 35, right associativity, format "π2  t")
  : tm_scope.
Notation "'ι1' t" := (tm_inj1 t) (at level 35, right associativity, format "ι1  t")
  : tm_scope.
Notation "'ι2' t" := (tm_inj2 t) (at level 35, right associativity, format "ι2  t")
  : tm_scope.
Notation "t ⊗ u" := (tm_tensor t u) (at level 40, left associativity)
  : tm_scope.
Notation "'δ' t" := (tm_dirac t) (at level 35, right associativity, format "δ  t")
  : tm_scope.
Notation "t ⅋[ p ] u" := (tm_choice p t u)
  (at level 50, left associativity, format "t  ⅋[ p ]  u") : tm_scope.
Notation "'μ' t" := (tm_fix t) (at level 35, right associativity, format "μ  t")
  : tm_scope.
(* let (x, y) = u in t, without names: the pair is bound to #1 and #0. *)
Notation "'let' ( , ) := u 'in' t" := (tm_lettensor u t)
  (at level 10, u at level 200, t at level 200,
   format "'let'  ( , )  :=  u  'in'  t") : tm_scope.

Declare Scope senv_scope.
Delimit Scope senv_scope with senv.
Bind Scope senv_scope with senv.

Notation "σ ⧺ τ" := (senv_add σ τ) : senv_scope.
Notation "r *: σ" := (senv_scale r σ) : senv_scope.

Local Open Scope senv_scope.

Section senv_theory.
Context {R : realType}.
Implicit Types (r s : Ω R) (e : centry R) (σ τ : senv R) (Γ : seq (ty R))
  (A : ty R).

(* The defining equations of the paper (Definition "context scaling
   operations"), the contexts being over the same variables. *)

(*   ⟨⟩ ⧺ ⟨⟩ ≡ ⟨⟩ *)
Lemma senv_add_nil : [::] ⧺ [::] = [::] :> senv R. Proof. by []. Qed.

(*   r ⟨⟩ ≡ ⟨⟩ *)
Lemma senv_scale_nil r : r *: [::] = [::] :> senv R. Proof. by []. Qed.

(*   (Γ, x :^r_s A) ⧺ (Γ', x :^r'_s' A) ≡ Γ ⧺ Γ', x :^(r + r')_(s ⊕* s') A *)
Lemma senv_add_cons e e' σ τ : (e :: σ) ⧺ (e' :: τ) = centry_add e e' :: σ ⧺ τ.
Proof. by []. Qed.

(*   r (Γ, x :^r' A) ≡ r Γ, x :^(r · r') A, the softness unchanged *)
Lemma senv_scale_cons r e σ : r *: (e :: σ) = centry_scale r e :: r *: σ.
Proof. by []. Qed.

Lemma esens_add e e' : esens (centry_add e e') = sens_add (esens e) (esens e').
Proof. by []. Qed.

Lemma esoft_add e e' : esoft (centry_add e e') = sens_hsum (esoft e) (esoft e').
Proof. by []. Qed.

Lemma esens_scale r e : esens (centry_scale r e) = sens_mul r (esens e).
Proof. by []. Qed.

Lemma esoft_scale r e : esoft (centry_scale r e) = esoft e.
Proof. by []. Qed.

(* Γ ⧺ Γ' is only defined on contexts over the same variables: the sum is
   truncated to the shorter environment, and scaling preserves the length. *)
Lemma size_senv_add σ τ : size (σ ⧺ τ) = minn (size σ) (size τ).
Proof. by rw size_map size_zip. Qed.

Lemma size_senv_scale r σ : size (r *: σ) = size σ.
Proof. by rw size_map. Qed.

Lemma nth_senv_add σ τ i : size σ = size τ -> (i < size σ)%N ->
  nth centry0 (σ ⧺ τ) i = centry_add (nth centry0 σ i) (nth centry0 τ i).
Proof.
move=> st si; rw (nth_map (centry0, centry0)) ?size_zip -?st ?minnn //.
by rw nth_zip.
Qed.

Lemma nth_senv_scale r σ i : (i < size σ)%N ->
  nth centry0 (r *: σ) i = centry_scale r (nth centry0 σ i).
Proof. by move=> si; rw (nth_map centry0). Qed.

End senv_theory.

(** * Typing *)

Section typing.
Context {R : realType}.
Implicit Types (Γ : seq (ty R)) (σ τ ρ : senv R) (t u v z step n : tm R)
  (A B C E : ty R) (r s o : Ω R) (p : ]0,1[ R).

(* Γ ⊢[ σ ] t : A, for σ a context over Γ (typed_size).  Derivations live
   in Type so that the semantics (semantics.v) is defined by recursion on
   them, as in the paper.  The rules are those of the paper, with the
   context Γ, x :^r_o A read as A :: Γ and CEntry r o :: σ.  The softness o
   of a variable bound by a term binder is a free parameter of the rule:
   the terms do not average over their variables, so nothing constrains it
   and the binder forgets it; the quantifiers of the logic (QuantLogic.v)
   are the binders that record the softness of their variable.  The rule
   (LET-⊗) is read with the scalars of the type matching
   those of the bound variables, x :^r A, y :^s B for u : A ⊗[r, s] B, and
   with u the pair and t the body, which is what its semantics computes. *)
Inductive typed : seq (ty R) -> senv R -> tm R -> ty R -> Type :=
| typed_var Γ σ i A :
    (i < size Γ)%N ->
    nth unit Γ i = A ->
    1 <= (esens (nth centry0 σ i))%:num ->
    size σ = size Γ ->
    (*———————————————————————————— (Var) *)
    Γ ⊢[ σ ] # i : A

| typed_abs Γ σ t A B r o :
    A :: Γ ⊢[ CEntry r o :: σ ] t : B ->
    (*———————————————————————————— (Abs) *)
    Γ ⊢[ σ ] λ t : A ⊸[r] B

| typed_app Γ σ τ t u A B r :
    Γ ⊢[ σ ] t : A ⊸[r] B ->
    Γ ⊢[ τ ] u : A ->
    (*———————————————————————————— (App) *)
    Γ ⊢[ σ ⧺ r *: τ ] t @ u : B

| typed_unit Γ σ :
    size σ = size Γ ->
    (*———————————————————————————— (Unit) *)
    Γ ⊢[ σ ] tm_unit : unit

| typed_pair Γ σ t u A B :
    Γ ⊢[ σ ] t : A ->
    Γ ⊢[ σ ] u : B ->
    (*———————————————————————————— (Pair) *)
    Γ ⊢[ σ ] ⟨t, u⟩ : A × B

| typed_proj1 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 × A2 ->
    (*———————————————————————————— (π₁) *)
    Γ ⊢[ σ ] π1 t : A1

| typed_proj2 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 × A2 ->
    (*———————————————————————————— (π₂) *)
    Γ ⊢[ σ ] π2 t : A2

| typed_inj1 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A1 ->
    (*———————————————————————————— (inj₁) *)
    Γ ⊢[ σ ] ι1 t : A1 + A2

| typed_inj2 Γ σ t A1 A2 :
    Γ ⊢[ σ ] t : A2 ->
    (*———————————————————————————— (inj₂) *)
    Γ ⊢[ σ ] ι2 t : A1 + A2

| typed_case Γ σ τ t u v A B C r o o' :
    Γ ⊢[ τ ] t : A + B ->
    A :: Γ ⊢[ CEntry r o :: σ ] u : C ->
    B :: Γ ⊢[ CEntry r o' :: σ ] v : C ->
    0 < r%:num ->
    (*———————————————————————————— (Case) *)
    Γ ⊢[ σ ⧺ r *: τ ] tm_case t u v : C

| typed_tensor Γ σ τ ρ t u A B r s :
    Γ ⊢[ σ ] t : A ->
    Γ ⊢[ τ ] u : B ->
    size ρ = size Γ ->
    (*———————————————————————————— (⊗) *)
    Γ ⊢[ r *: σ ⧺ s *: τ ⧺ ρ ] t ⊗ u : A ⊗[r, s] B

| typed_lettensor Γ σ τ t u A B C r s o o' :
    B :: A :: Γ ⊢[ CEntry s o' :: CEntry r o :: σ ] t : C ->
    Γ ⊢[ τ ] u : A ⊗[r, s] B ->
    (*———————————————————————————— (Let-⊗) *)
    Γ ⊢[ σ ⧺ τ ] (let (,) := u in t) : C

| typed_dirac Γ σ t A :
    Γ ⊢[ σ ] t : A ->
    (*———————————————————————————— (δ) *)
    Γ ⊢[ σ ] δ t : 𝕎 A

| typed_choice Γ σ τ t u A p :
    Γ ⊢[ σ ] t : 𝕎 A ->
    Γ ⊢[ τ ] u : 𝕎 A ->
    (*———————————————————————————— (⅋ₚ) *)
    Γ ⊢[ p *: σ ⧺ (1 - p) *: τ ] t ⅋[p] u : 𝕎 A

| typed_let Γ σ τ t u A E r o :
    A :: Γ ⊢[ CEntry r o :: σ ] t : E ->
    Γ ⊢[ τ ] u : 𝕎 A ->
    ib_ty E ->
    r%:num < +oo ->
    (*———————————————————————————— (Let) *)
    Γ ⊢[ σ ⧺ r *: τ ] tm_let u t : E

| typed_zero Γ σ :
    size σ = size Γ ->
    (*———————————————————————————— (Zero) *)
    Γ ⊢[ σ ] tm_zero : ℕ

| typed_succ Γ σ t :
    Γ ⊢[ σ ] t : ℕ ->
    (*———————————————————————————— (Succ) *)
    Γ ⊢[ σ ] succ t : ℕ

| typed_natrec Γ σ τ ρ z step n A o o' :
    Γ ⊢[ σ ] z : A ->
    ℕ :: A :: Γ ⊢[ CEntry sens1 o' :: CEntry sens1 o :: τ ] step : A ->
    Γ ⊢[ ρ ] n : ℕ ->
    (*———————————————————————————— (Rec) *)
    Γ ⊢[ σ ⧺ sensy *: τ ⧺ ρ ] rec z step n : A

(* (Fix): the premise (1 - r)Γ, x :^r A ⊢ t : A with r < 1.  Its semantics
   needs, in addition, a seed at finite displacement or a single-galaxy
   codomain (fixpoint.v). *)
| typed_fix Γ σ t A (r : contr R) o :
    A :: Γ ⊢[ CEntry (contr_sens r) o :: contr_sensC r *: σ ] t : A ->
    (*———————————————————————————— (Fix) *)
    Γ ⊢[ σ ] μ t : A
where "Γ ⊢[ σ ] t : A" := (typed Γ σ t A).

Let size_cons_inj {T U : Type} {x : T} {y : U} {s : seq T} {t : seq U} :
  size (x :: s) = size (y :: t) -> size s = size t.
Proof. by move=> /= []. Qed.

(* Typed terms have as many entries as variables. *)
Lemma typed_size Γ σ t A : Γ ⊢[ σ ] t : A -> size σ = size Γ.
Proof.
elim=> {Γ σ t A} //.
- by move=> Γ σ t A B r o _ H; exact: (size_cons_inj H).
- move=> Γ σ τ t u A B r _ sG _ tG.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ t u v A B C r o o' _ tG _ H _ _ _; have sG := size_cons_inj H.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ ρ t u A B r s _ sG _ tG rG.
  by rw !size_senv_add !size_senv_scale sG tG rG !minnn.
- move=> Γ σ τ t u A B C r s o o' _ H _ tG.
  have sG := size_cons_inj (size_cons_inj H).
  by rw size_senv_add sG tG minnn.
- move=> Γ σ τ t u A p _ sG _ tG.
  by rw size_senv_add !size_senv_scale sG tG minnn.
- move=> Γ σ τ t u A E r o _ H _ tG _ _; have sG := size_cons_inj H.
  by rw size_senv_add size_senv_scale sG tG minnn.
- move=> Γ σ τ ρ z step n A o o' _ sG _ H _ rG.
  have tG := size_cons_inj (size_cons_inj H).
  by rw !size_senv_add size_senv_scale sG tG rG !minnn.
- move=> Γ σ t A r o _ H; move: (size_cons_inj H).
  by rw size_senv_scale.
Qed.

Lemma typed_size_cons Γ σ t A B e : A :: Γ ⊢[ e :: σ ] t : B -> size σ = size Γ.
Proof. by move/typed_size => /= []. Qed.

Lemma typed_size_cons2 Γ σ t A B C e e' :
  B :: A :: Γ ⊢[ e' :: e :: σ ] t : C -> size σ = size Γ.
Proof. by move/typed_size => /= []. Qed.

(* The identity, λ x. x : A ⊸[r] A for every r >= 1, the bound variable at
   the softness +oo (a transparent derivation, so that its semantics
   computes). *)
Example typed_id A r : 1 <= r%:num -> [::] ⊢[ [::] ] λ # 0 : A ⊸[r] A.
Proof. by move=> r1; apply: (typed_abs (o := sensy)); apply: typed_var. Defined.

End typing.

Notation "Γ ⊢[ σ ] t : A" := (typed Γ σ t A) : type_scope.
