(* Denotational semantics of the calculus in CExtMet (paper, Sect.
   "Semantics", and the diagrams of spreadsheet.typ). *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import discrete_topology.
From ExtMetQLL Require Import analysis_extras extmet cextmet fixpoint syntax.

(**md**************************************************************************)
(* # Semantics of the calculus in CExtMet                                     *)
(*                                                                            *)
(* Types denote complete pseudometric spaces (the objects of CExtMet, up to  *)
(* the separation of points at distance 0, which the scaling by 0 breaks),  *)
(* contexts denote tensors of scaled types, and typing derivations denote    *)
(* non-expansive maps, by recursion on the derivation (syntax.v).            *)
(*                                                                            *)
(* The Wasserstein monad enters through an interface, wmonad: wasserstein.v  *)
(* builds W_p on standard Borel spaces, while the semantics needs it on      *)
(* every object (function spaces have no measurable structure), so the       *)
(* semantics is parametric in a model W of the operations and inequalities  *)
(* the rules use.  FIX is interpreted by semfix, Banach's fixed point from   *)
(* the seed point when it is at finite displacement (fixpoint.v shows the    *)
(* paper's rule has no fixed point otherwise), and the point itself else;   *)
(* this is non-expansive on the nose (semfix_param), so every derivation     *)
(* denotes a morphism (sem_nonexpansive) and fix x. t is a fixed point of t  *)
(* wherever the seed is at finite displacement (sem_fixP).                   *)
(*                                                                            *)
(* ```                                                                        *)
(*            cprod X Y == the cartesian product X × Y (max distance)        *)
(*             pfix y0 f == the limit of the iterates of f from y0 (Banach)  *)
(*          semfix F y0 x == the fixed point of F x from the seed y0, or y0   *)
(*      wfunctor, wmonad == the interface of the probability monad: the      *)
(*                          carrier WT, the distance wdist and its scaling   *)
(*                          law, the unit wret, the pushforward wmap, the    *)
(*                          marginals, the convex combinations wconv, the   *)
(*                          join wjoin, each non-expansive, and completeness *)
(*               wsp W X == W X as a (complete) pseudometric space           *)
(*            sem_ty W A == ⟦A⟧, a complete pseudometric space               *)
(*          ctx_choice Γ == the carrier of ⟦Γ⟧, a nested product            *)
(*            ctxC W Γ σ == ⟦Γ ; σ⟧, this carrier with the distance          *)
(*                          ctx_dist Γ σ of ⟦Γ⟧ ⊗ r_1⟦A_1⟧ ⊗ ...; the maps   *)
(*                          split, dist, weak of the paper are identities   *)
(*                          (ctx_dist_add, ctx_dist_scale)                   *)
(*           ctx_var Γ i == the projection on the variable i                 *)
(*              walg W E == the algebra W⟦E⟧ -> ⟦E⟧ of an IB type E          *)
(*     sem W d : ⟦Γ⟧ -o ⟦A⟧ == the interpretation of d : Γ ⊢[ σ ] t : A, a    *)
(*                          non-expansive map (sem_nonexpansive)             *)
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

(** * The cartesian product *)

(* X × Y with the max distance, a fresh type since X * Y carries Analysis's
   product structure and lp_prod the tensor (HB keys instances on the head
   constant, so the l^oo product cannot share lp_prod with the l^1 one). *)
Definition cprod {R : realType} (X Y : pseudoMetricType R) : Type := (X * Y)%type.

Section cprod.
Context {R : realType} (X Y : pseudoMetricType R).
Local Notation P := (cprod X Y).

HB.instance Definition _ := Choice.on P.

Definition cprod_dist (u v : P) : \bar R :=
  maxe (edist (u.1, v.1)) (edist (u.2, v.2)).

Let cprod_dist_ge0 u v : 0 <= cprod_dist u v.
Proof. by rw le_max edist_ge0. Qed.

Let cprod_dist_xx : self_inverse 0 cprod_dist.
Proof. by move=> u; rw /cprod_dist !edist_refl maxxx. Qed.

Let cprod_distC : commutative cprod_dist.
Proof. by move=> u v; rw /cprod_dist edist_sym [edist (u.2, _)]edist_sym. Qed.

Let cprod_dist_triangle u v w :
  cprod_dist u w <= cprod_dist u v + cprod_dist v w.
Proof.
rw /cprod_dist ge_max; apply/andP; split.
  by apply: le_trans (edist_triangle _ v.1 _) _; apply: leeD; rw le_max lexx.
by apply: le_trans (edist_triangle _ v.2 _) _; apply: leeD; rw le_max lexx orbT.
Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R P
  cprod_dist_ge0 cprod_dist_xx cprod_distC cprod_dist_triangle.

Lemma cprod_edistE (u v : P) :
  edist (u, v) = maxe (edist (u.1, v.1)) (edist (u.2, v.2)).
Proof. exact: (@edistE _ _ cprod_dist). Qed.

End cprod.

(** * Complete pseudometric spaces *)

Section complete_space_lemmas.
Context {R : realType}.

Lemma complete_space_cvg (T : pseudoPMetricType R) : complete_space T ->
  forall F : set_system T, ProperFilter F -> cauchy F -> cvg F.
Proof. by move=> cT F FF cF; have [x Fx] := cT F FF cF; exact: cvgP Fx. Qed.

Lemma nonexpansive_cst (X Y : pseudoMetricType R) (y : Y) :
  nonexpansive (fun _ : X => y).
Proof. by apply/nonexpansiveP => x x'; rw edist_refl. Qed.

Lemma unit_complete : complete_space (unit : pseudoMetricType R).
Proof.
move=> F FF _; exists tt; apply/cvg_edistP => e e0; near=> y.
by rw unit_edistE lte_fin.
Unshelve. all: by end_near. Qed.

(* 0 X is indiscrete, hence complete. *)
Lemma scale_complete_all (r : sens R) (X : pseudoMetricType R) :
  complete_space X -> complete_space (scale r X).
Proof.
move=> cX; have [r0|r0] := eqVneq r%:num 0; last first.
  by apply: scale_complete => //; rw lt_def r0 /=.
move=> F FF _; have [x _] := filter_ex (filterT : F setT); exists x.
apply/cvg_edistP => e e0; near=> y.
by rw scale_edistE r0 mul0e lte_fin.
Unshelve. all: by end_near. Qed.

Lemma cprod_complete (X Y : pseudoMetricType R) :
  complete_space X -> complete_space Y -> complete_space (cprod X Y).
Proof.
move=> cX cY F FF /cauchy_edistP Fc.
have Fc1 : cauchy (fst @ F).
  apply/cauchy_edistP => e e0; have [[x y] Fxy] := Fc e e0.
  exists x; rw /fmap /=; apply: filterS Fxy => -[x' y'] /=; rw cprod_edistE /=.
  by apply: le_lt_trans; rw le_max lexx.
have Fc2 : cauchy (snd @ F).
  apply/cauchy_edistP => e e0; have [[x y] Fxy] := Fc e e0.
  exists y; rw /fmap /=; apply: filterS Fxy => -[x' y'] /=; rw cprod_edistE /=.
  by apply: le_lt_trans; rw le_max lexx orbT.
have [a /cvg_edistP Fa] := cX _ _ Fc1.
have [b /cvg_edistP Fb] := cY _ _ Fc2.
exists ((a, b) : cprod X Y); apply/cvg_edistP => e e0.
near=> u; rw cprod_edistE gt_max; apply/andP; split; near: u.
  exact: (Fa _ e0).
exact: (Fb _ e0).
Unshelve. all: by end_near. Qed.

End complete_space_lemmas.

(* The type formers of CExtMet preserve completeness: instances. *)
Section complete_instances.
Context {R : realType}.

HB.instance Definition _ :=
  Uniform_isComplete.Build unit (complete_space_cvg (@unit_complete R)).

Section prod_instances.
Context (X Y : completePseudoMetricType R).

HB.instance Definition _ := isPointed.Build (cprod X Y) ((point, point) : cprod X Y).
HB.instance Definition _ := Uniform_isComplete.Build (cprod X Y)
  (complete_space_cvg (cprod_complete (@completeType_complete X)
    (@completeType_complete Y))).

HB.instance Definition _ := isPointed.Build (tensor X Y) ((point, point) : tensor X Y).
HB.instance Definition _ := Uniform_isComplete.Build (tensor X Y)
  (complete_space_cvg (tensor_complete (@completeType_complete X)
    (@completeType_complete Y))).

HB.instance Definition _ := isPointed.Build (coprod X Y) (inl point : coprod X Y).
HB.instance Definition _ := Uniform_isComplete.Build (coprod X Y)
  (complete_space_cvg (coprod_complete (@completeType_complete X)
    (@completeType_complete Y))).

End prod_instances.

Section scale_instances.
Context (r : sens R) (X : completePseudoMetricType R).

HB.instance Definition _ := isPointed.Build (scale r X) (point : X).
HB.instance Definition _ := Uniform_isComplete.Build (scale r X)
  (complete_space_cvg (@scale_complete_all R r X (@completeType_complete X))).

End scale_instances.

Section nemap_instances.
Context (X : pseudoMetricType R) (Y : completePseudoMetricType R).

HB.instance Definition _ :=
  isPointed.Build (X -o Y) (NEMap (@nonexpansive_cst R X Y point)).
HB.instance Definition _ := Uniform_isComplete.Build (X -o Y)
  (complete_space_cvg (@nemap_complete R X Y (@completeType_complete Y))).

End nemap_instances.

End complete_instances.

(** * Fixed points on complete pseudometric spaces *)

Section pfix.
Context {R : realType} {Y : completePseudoMetricType R}.

(* The limit of the iterates of f from y0. *)
Definition pfix (y0 : Y) (f : Y -> Y) : Y := limn (fun n => iter n f y0).

Variables (r : contr R) (f : Y -> Y).
Hypothesis fr : econtraction r f.

Let q0 := econtraction_fine_ge0 r.
Let q1 := econtraction_fine_lt1 r.
Let fq := econtractionE fr.

(* Banach: from a seed at finite displacement, pfix is a fixed point (up to
   distance 0, the spaces being pseudometric) in the galaxy of the seed. *)
Lemma pfix_edist0 y0 : edist (y0, f y0) < +oo ->
  edist (pfix y0 f, f (pfix y0 f)) = 0.
Proof. by move=> y0fin; exact: (banach_fixed q0 q1 fq y0fin). Qed.

Lemma pfix_fin y0 : edist (y0, f y0) < +oo -> edist (y0, pfix y0 f) < +oo.
Proof.
by move=> y0fin; exact: le_lt_trans (banach_dist_lim q0 q1 fq y0fin) (ltry _).
Qed.

End pfix.

(* The estimate behind the non-expansiveness of FIX (fixpoint.v,
   fixed_point_edist_le), for fixed points up to distance 0. *)
Lemma pfixed_point_edist_le {R : realType} {Y : pseudoMetricType R}
    (r : contr R) (f g : Y -> Y) (a b : Y) :
  econtraction r f -> edist (a, f a) = 0 -> edist (b, g b) = 0 ->
  edist (a, b) < +oo ->
  (1 - r%:num) * edist (a, b) <= edist (f b, g b).
Proof.
move=> fr fa gb abfin.
have le : edist (a, b) <= r%:num * edist (a, b) + edist (f b, g b).
  apply: le_trans (edist_triangle _ (f a) _) _; rw fa add0e.
  apply: le_trans (edist_triangle _ (f b) _) _.
  apply: le_trans (leeD (fr _ _) (edist_triangle _ (g b) _)) _.
  by rw [edist (g b, b)]edist_sym gb adde0.
have Dfin : edist (a, b) \is a fin_num by rw ge0_fin_numE.
have rfin := econtraction_fin r.
by rw muleBl ?fin_num_adde_defr // mul1e leeBlDr ?fin_numM // addeC.
Qed.

(* FIX: the fixed point of F x from the seed y0 when the seed is at finite
   displacement, and y0 otherwise.  As Banach's theorem only applies from a
   seed at finite displacement (fixpoint.v), this is the total version of the
   paper's fix; it is non-expansive since the finiteness of the displacement
   is constant on the galaxies of X. *)
Section semfix.
Context {R : realType} {X : pseudoMetricType R} {Y : completePseudoMetricType R}.
Variables (r : contr R) (F : X -> Y -> Y) (y0 : Y).
Hypotheses (Fr : forall x, econtraction r (F x))
  (FX : forall x x' y, edist (F x y, F x' y) <= edist (x, x')).

Definition semfix (x : X) : Y :=
  if edist (y0, F x y0) < +oo then pfix y0 (F x) else y0.

Let good_galaxy x x' : edist (x, x') < +oo ->
  edist (y0, F x y0) < +oo -> edist (y0, F x' y0) < +oo.
Proof.
move=> xx' x0; apply: le_lt_trans (edist_triangle _ (F x y0) _) _.
by rw lte_add_pinfty // (le_lt_trans (FX _ _ _)).
Qed.

Lemma semfix_param x x' :
  (1 - r%:num) * edist (semfix x, semfix x') <= edist (x, x').
Proof.
have [->|] := eqVneq (edist (x, x')) +oo; first exact: leey.
rw -ltey => xx'; rw /semfix.
have [x0|x0] := boolP (edist (y0, F x y0) < +oo).
  have x0' := good_galaxy xx' x0; rw x0' /=.
  apply: le_trans (FX _ _ (pfix y0 (F x'))).
  apply: pfixed_point_edist_le (Fr x) (pfix_edist0 (Fr x) x0)
    (pfix_edist0 (Fr x') x0') _.
  apply: le_lt_trans (edist_triangle _ y0 _) _.
  by rw [edist (pfix _ _, y0)]edist_sym lte_add_pinfty ?(pfix_fin (Fr x))
    ?(pfix_fin (Fr x')).
have x0' : ~~ (edist (y0, F x' y0) < +oo).
  apply: contra x0; apply: good_galaxy; by rw edist_sym.
by rw ifN //= edist_refl mule0.
Qed.

End semfix.

(** * The probability monad: interface *)

(* The projections of the monoidal product, as morphisms. *)
Section tensor_proj.
Context {R : realType} (X Y : pseudoMetricType R).

Lemma tensor_fst_ne : @nonexpansive R (tensor X Y) X fst.
Proof. by apply/nonexpansiveP => u v; rw tensor_edistE leeDl. Qed.

Lemma tensor_snd_ne : @nonexpansive R (tensor X Y) Y snd.
Proof. by apply/nonexpansiveP => u v; rw tensor_edistE leeDr. Qed.

Definition tensor_fst : tensor X Y -o X := NEMap tensor_fst_ne.
Definition tensor_snd : tensor X Y -o Y := NEMap tensor_snd_ne.

Lemma cprod_fst_ne : @nonexpansive R (cprod X Y) X fst.
Proof. by apply/nonexpansiveP => u v; rw cprod_edistE le_max lexx. Qed.

Lemma cprod_snd_ne : @nonexpansive R (cprod X Y) Y snd.
Proof. by apply/nonexpansiveP => u v; rw cprod_edistE le_max lexx orbT. Qed.

Definition cprod_fst : cprod X Y -o X := NEMap cprod_fst_ne.
Definition cprod_snd : cprod X Y -o Y := NEMap cprod_snd_ne.

(* Evaluation at a point, as a morphism (X -o Y) -o Y. *)
Lemma nemap_ev_ne (x : X) : @nonexpansive R (X -o Y) Y (fun f => f x).
Proof. by apply/nonexpansiveP => f g; exact: nemap_edist_ub. Qed.

Definition nemap_ev (x : X) : (X -o Y) -o Y := NEMap (nemap_ev_ne x).

End tensor_proj.

(* The Wasserstein monad W on CExtMet, as the semantics uses it.
   wasserstein.v constructs W_p and its unit, pushforward and convex
   combinations on standard Borel spaces; the interface lists the structure
   the typing rules need on every object (the measurable structure of
   function spaces is not available), so that the semantics is parametric in
   a model of this interface.  The first record is the functor with its
   distance (W X is built from it as a pseudometric space, wsp), the second
   its operations with their non-expansiveness. *)
Unset Implicit Arguments.

Record wfunctor (R : realType) := WFunctor {
  WT : Type -> Type;
  WT_eqMixin : forall T : choiceType, hasDecEq (WT T);
  WT_choiceMixin : forall T : choiceType, hasChoice (WT T);
  (* the Wasserstein distance over the distance of X *)
  wdist : forall X : pseudoMetricType R, WT X -> WT X -> \bar R;
  wdist_ge0 : forall (X : pseudoMetricType R) (m m' : WT X), 0 <= wdist X m m';
  wdist_xx : forall (X : pseudoMetricType R) (m : WT X), wdist X m m = 0;
  wdistC : forall (X : pseudoMetricType R) (m m' : WT X),
    wdist X m m' = wdist X m' m;
  wdist_triangle : forall (X : pseudoMetricType R) (m m' m'' : WT X),
    wdist X m m'' <= wdist X m m' + wdist X m' m'';
  (* W (r X) = r (W X) *)
  wdist_scale : forall (r : sens R) (X : pseudoMetricType R) (m m' : WT X),
    wdist (scale r X) m m' = r%:num * wdist X m m'
}.

Arguments WT {R} w T.
Arguments WT_eqMixin {R} w T.
Arguments WT_choiceMixin {R} w T.
Arguments wdist {R} w X m m'.
Arguments wdist_ge0 {R} w X m m'.
Arguments wdist_xx {R} w X m.
Arguments wdistC {R} w X m m'.
Arguments wdist_triangle {R} w X m m' m''.
Arguments wdist_scale {R} w r X m m'.

Set Implicit Arguments.

(* W X as a pseudometric space. *)
Definition wsp {R : realType} (W : wfunctor R) (X : pseudoMetricType R)
  : Type := WT W X.

Section wsp.
Context {R : realType} (W : wfunctor R) (X : pseudoMetricType R).

HB.instance Definition _ : hasDecEq (wsp W X) := WT_eqMixin W X.
HB.instance Definition _ : hasChoice (wsp W X) := WT_choiceMixin W X.
HB.instance Definition _ := isExtPseudoMetric.Build R (wsp W X)
  (wdist_ge0 W X) (wdist_xx W X) (wdistC W X) (wdist_triangle W X).

Lemma wsp_edistE (m m' : wsp W X) : edist (m, m') = wdist W X m m'.
Proof. by apply: edistE => [a b|a b e]; first exact: wdist_ge0. Qed.

End wsp.

Unset Implicit Arguments.

Record wmonad (R : realType) := WMonad {
  wfun :> wfunctor R;
  (* the unit δ *)
  wret : forall T : Type, T -> WT wfun T;
  wret_dist : forall (X : pseudoMetricType R) (x y : X),
    edist ((wret X x : wsp wfun X), wret X y) <= edist (x, y);
  (* the action on morphisms, the pushforward *)
  wmap : forall X Y : pseudoMetricType R, (X -o Y) -> WT wfun X -> WT wfun Y;
  wmap_dist : forall (X Y : pseudoMetricType R) (f : X -o Y) (m m' : wsp wfun X),
    edist ((wmap X Y f m : wsp wfun Y), wmap X Y f m') <= edist (m, m');
  wmap_bound : forall (X Y : pseudoMetricType R) (f g : X -o Y) (e : \bar R),
    (forall x, edist (f x, g x) <= e) ->
    forall m : WT wfun X, edist ((wmap X Y f m : wsp wfun Y), wmap X Y g m) <= e;
  (* the marginals W (X ⊗ Y) -> W X ⊗ W Y are non-expansive *)
  wtensor_dist : forall (X Y : pseudoMetricType R) (m m' : wsp wfun (tensor X Y)),
    edist ((wmap _ X (tensor_fst X Y) m : wsp wfun X), wmap _ X (tensor_fst X Y) m') +
    edist ((wmap _ Y (tensor_snd X Y) m : wsp wfun Y), wmap _ Y (tensor_snd X Y) m') <=
    edist (m, m');
  (* the convex combinations, interpolative barycentric *)
  wconv : forall T : Type, prob R -> WT wfun T -> WT wfun T -> WT wfun T;
  wconv_dist : forall (X : pseudoMetricType R) (p : prob R) (a b a' b' : wsp wfun X),
    edist ((wconv X p a b : wsp wfun X), wconv X p a' b') <=
    p%:num%:E * edist (a, a') + (1 - p%:num)%:E * edist (b, b');
  (* the join *)
  wjoin : forall T : Type, WT wfun (WT wfun T) -> WT wfun T;
  wjoin_dist : forall (X : pseudoMetricType R) (m m' : wsp wfun (wsp wfun X)),
    edist ((wjoin X m : wsp wfun X), wjoin X m') <= edist (m, m');
  (* W preserves completeness *)
  wsp_complete : forall X : pseudoMetricType R,
    complete_space X -> complete_space (wsp wfun X)
}.

Arguments wret {R} w {T} x.
Arguments wret_dist {R} w {X} x y.
Arguments wmap {R} w {X Y} f m.
Arguments wmap_dist {R} w {X Y} f m m'.
Arguments wmap_bound {R} w {X Y} f g e.
Arguments wtensor_dist {R} w {X Y} m m'.
Arguments wconv {R} w {T} p a b.
Arguments wconv_dist {R} w {X} p a b a' b'.
Arguments wjoin {R} w {T} m.
Arguments wjoin_dist {R} w {X} m m'.
Arguments wsp_complete {R} w {X}.

Set Implicit Arguments.

Section wsp_complete_instances.
Context {R : realType} (W : wmonad R) (X : completePseudoMetricType R).

HB.instance Definition _ := isPointed.Build (wsp W X) (wret W point : wsp W X).
HB.instance Definition _ := Uniform_isComplete.Build (wsp W X)
  (complete_space_cvg (wsp_complete W (@completeType_complete X))).

End wsp_complete_instances.

(* The recursor of the natural numbers, rec (z, (x, y). s, n). *)
Fixpoint natrec_fun (Y : Type) (z : Y) (st : Y -> nat -> Y) (k : nat) : Y :=
  if k is k'.+1 then st (natrec_fun z st k') k' else z.

(** * Interpretation of types and contexts *)

Section semantics.
Context {R : realType} (W : wmonad R).

Local Notation dnat := (discrete_topology nat).

(* ⟦A⟧, an object of CExtMet. *)
Fixpoint sem_ty (A : ty R) : completePseudoMetricType R :=
  match A with
  | ty_nat => dnat
  | ty_unit => unit
  | ty_prod A B => cprod (sem_ty A) (sem_ty B)
  | ty_sum A B => coprod (sem_ty A) (sem_ty B)
  | ty_tensor r A s B => tensor (scale r (sem_ty A)) (scale s (sem_ty B))
  | ty_lolli r A B => scale r (sem_ty A) -o sem_ty B
  | ty_dist A => wsp W (sem_ty A)
  end.

(* The carrier of ⟦Γ⟧, a nested product, which does not depend on the
   sensitivities; ⟦Γ ; σ⟧ is this carrier with the distance of
   ⟦Γ⟧ ⊗ r_1 ⟦A_1⟧ ⊗ ... (ctx_dist).  The structural maps split, dist and
   weak of the paper are then identities. *)
Fixpoint ctx_choice (Γ : seq (ty R)) : choiceType :=
  if Γ is A :: Γ' then (ctx_choice Γ' * sem_ty A)%type else unit.

Definition ctxC (Γ : seq (ty R)) (σ : senv R) : Type := ctx_choice Γ.

Fixpoint ctx_dist (Γ : seq (ty R)) (σ : senv R) :
    ctx_choice Γ -> ctx_choice Γ -> \bar R :=
  match Γ with
  | [::] => fun _ _ => 0
  | A :: Γ' => fun γ γ' =>
      @ctx_dist Γ' (behead σ) γ.1 γ'.1 + (head sens0 σ)%:num * edist (γ.2, γ'.2)
  end.

Arguments ctx_dist : clear implicits.

Lemma ctx_dist_ge0 Γ σ γ γ' : 0 <= ctx_dist Γ σ γ γ'.
Proof.
elim: Γ σ γ γ' => [|A Γ ih] σ γ γ' //=.
by apply: adde_ge0 => //; apply: mule_ge0 => //; exact: edist_ge0.
Qed.

Lemma ctx_dist_xx Γ σ γ : ctx_dist Γ σ γ γ = 0.
Proof. by elim: Γ σ γ => [|A Γ ih] σ γ //=; rw ih edist_refl mule0 adde0. Qed.

Lemma ctx_distC Γ σ γ γ' : ctx_dist Γ σ γ γ' = ctx_dist Γ σ γ' γ.
Proof. by elim: Γ σ γ γ' => [|A Γ ih] σ γ γ' //=; rw ih edist_sym. Qed.

Lemma ctx_dist_triangle Γ σ γ γ' γ'' :
  ctx_dist Γ σ γ γ'' <= ctx_dist Γ σ γ γ' + ctx_dist Γ σ γ' γ''.
Proof.
elim: Γ σ γ γ' γ'' => [|A Γ ih] σ γ γ' γ'' /=; first by rw adde0.
rw addrACA; apply: leeD; first exact: ih.
by rw -ge0_muleDr //; apply: lee_wpmul2l => //; exact: edist_triangle.
Qed.

Section ctx_instances.
Context (Γ : seq (ty R)) (σ : senv R).

HB.instance Definition _ := Choice.on (ctxC Γ σ).
HB.instance Definition _ := isExtPseudoMetric.Build R (ctxC Γ σ)
  (@ctx_dist_ge0 Γ σ) (@ctx_dist_xx Γ σ) (@ctx_distC Γ σ)
  (@ctx_dist_triangle Γ σ).

Lemma ctx_edistE (γ γ' : ctxC Γ σ) : edist (γ, γ') = ctx_dist Γ σ γ γ'.
Proof. by apply: edistE => [a b|a b e]; first exact: ctx_dist_ge0. Qed.

End ctx_instances.

(* ⟦Γ ⧺ Γ'⟧ = ⟦Γ⟧ ⊗ ⟦Γ'⟧ and ⟦rΓ⟧ = r⟦Γ⟧, on the common carrier. *)
Lemma ctx_dist_add Γ σ τ γ γ' : size σ = size Γ -> size τ = size Γ ->
  ctx_dist Γ (σ ⧺ τ) γ γ' = ctx_dist Γ σ γ γ' + ctx_dist Γ τ γ γ'.
Proof.
elim: Γ σ τ γ γ' => [|A Γ ih] [|r σ] [|s τ] γ γ' //= => [_ _|[sG] [tG]].
  by rw adde0.
by rw ih // sens_addE ge0_muleDl // addrACA.
Qed.

Lemma ctx_dist_scale Γ r σ γ γ' : size σ = size Γ ->
  ctx_dist Γ (r *: σ) γ γ' = r%:num * ctx_dist Γ σ γ γ'.
Proof.
elim: Γ σ γ γ' => [|A Γ ih] [|s σ] γ γ' //= => [_|[sG]].
  by rw mule0.
by rw ih // sens_mulE ge0_muleDr ?ctx_dist_ge0 ?mule_ge0 // muleA.
Qed.

(* The projection on a variable. *)
Fixpoint ctx_var (Γ : seq (ty R)) (i : nat) :
    ctx_choice Γ -> sem_ty (nth ty_unit Γ i) :=
  match Γ, i return ctx_choice Γ -> sem_ty (nth ty_unit Γ i) with
  | [::], 0 => fun _ => tt
  | [::], _.+1 => fun _ => tt
  | A :: Γ', 0 => fun γ => γ.2
  | A :: Γ', i'.+1 => fun γ => @ctx_var Γ' i' γ.1
  end.

Arguments ctx_var : clear implicits.

Lemma ctx_var_dist Γ σ i γ γ' : size σ = size Γ -> (i < size Γ)%N ->
  (nth sens0 σ i)%:num * edist (ctx_var Γ i γ, ctx_var Γ i γ') <=
  ctx_dist Γ σ γ γ'.
Proof.
elim: Γ σ i γ γ' => [|A Γ ih] [|r σ] [|i] γ γ' //= [sG] iG.
  by apply: leeDr; exact: ctx_dist_ge0.
by apply: le_trans (ih _ _ _ _ sG iG) _; apply: leeDl; exact: mule_ge0.
Qed.

(** * Interpretation of the typing rules *)

(* ⟦Γ ⊢ t : A⟧ : ⟦Γ⟧ -> ⟦A⟧ is built by recursion on the derivation, each
   rule as a non-expansive map of its premises (the diagrams of the paper,
   with split, dist and weak the identities on the common carrier). *)

Lemma nemapP (X Y : pseudoMetricType R) (f : X -o Y) x x' :
  edist (f x, f x') <= edist (x, x').
Proof. exact: (nonexpansiveP _).1 (nemap_ne f) x x'. Qed.

Lemma ge0_addey (x : \bar R) : 0 <= x -> x + +oo = +oo.
Proof. by move=> x0; rw addey // gt_eqF // (lt_le_trans _ x0) // ltNy0. Qed.

Lemma ge0_addye (x : \bar R) : 0 <= x -> +oo + x = +oo.
Proof. by move=> x0; rw addeC ge0_addey. Qed.

(* (VAR): the projection, non-expansive since r >= 1. *)
Lemma sem_var_ne Γ σ i : size σ = size Γ -> (i < size Γ)%N ->
  1 <= (nth sens0 σ i)%:num ->
  @nonexpansive R (ctxC Γ σ) (sem_ty (nth ty_unit Γ i)) (ctx_var Γ i).
Proof.
move=> sG iG r1; apply/nonexpansiveP => γ γ'; rw ctx_edistE.
apply: le_trans _ (@ctx_var_dist Γ σ i γ γ' sG iG).
by rw -[X in X <= _]mul1e; apply: lee_wpmul2r; [exact: edist_ge0 | exact: r1].
Qed.

Definition sem_var Γ σ i A (iG : (i < size Γ)%N) (e : nth ty_unit Γ i = A)
    (r1 : 1 <= (nth sens0 σ i)%:num) (sG : size σ = size Γ) :
    ctxC Γ σ -o sem_ty A :=
  eq_rect _ (fun B => ctxC Γ σ -o sem_ty B) (NEMap (sem_var_ne sG iG r1)) _ e.

(* (ABS): currying. *)
Lemma sem_abs_subproof Γ σ A B r (f : ctxC (A :: Γ) (r :: σ) -o sem_ty B)
    (γ : ctxC Γ σ) :
  @nonexpansive R (scale r (sem_ty A)) (sem_ty B) (fun a => f (γ, a)).
Proof.
apply/nonexpansiveP => a a'; apply: le_trans (nemapP f (γ, a) (γ, a')) _.
by rw ctx_edistE /= ctx_dist_xx add0e scale_edistE.
Qed.

Definition sem_abs Γ σ A B r (f : ctxC (A :: Γ) (r :: σ) -o sem_ty B)
  (γ : ctxC Γ σ) : sem_ty (A ⊸[r] B) := NEMap (sem_abs_subproof f γ).

Lemma sem_abs_ne Γ σ A B r (f : ctxC (A :: Γ) (r :: σ) -o sem_ty B) :
  @nonexpansive R (ctxC Γ σ) (sem_ty (A ⊸[r] B)) (sem_abs f).
Proof.
apply/nonexpansiveP => γ γ'; apply: nemap_edist_le => [|a /=].
  exact: edist_ge0.
apply: le_trans (nemapP f (γ, a) (γ', a)) _.
by rw !ctx_edistE /= edist_refl mule0 adde0.
Qed.

(* (APP): evaluation. *)
Lemma sem_app_ne Γ σ τ A B r (f : ctxC Γ σ -o sem_ty (A ⊸[r] B))
    (u : ctxC Γ τ -o sem_ty A) :
  size σ = size Γ -> size τ = size Γ ->
  @nonexpansive R (ctxC Γ (σ ⧺ r *: τ)) (sem_ty B) (fun γ => f γ (u γ)).
Proof.
move=> sG tG; apply/nonexpansiveP => γ γ'.
rw ctx_edistE ctx_dist_add ?size_senv_scale // ctx_dist_scale //.
apply: le_trans (edist_triangle (f γ (u γ)) (f γ (u γ')) (f γ' (u γ'))) _.
rw [X in _ <= X]addeC; apply: leeD.
  apply: le_trans (nemapP (f γ) (u γ) (u γ')) _; rw scale_edistE.
  by apply: lee_wpmul2l => //; rw -ctx_edistE; exact: nemapP u γ γ'.
apply: le_trans (nemap_edist_ub (f γ) (f γ') (u γ')) _.
by rw -ctx_edistE; exact: nemapP f γ γ'.
Qed.

(* (PAIR), (π_i): the cartesian product. *)
Lemma sem_pair_ne Γ σ A B (t : ctxC Γ σ -o sem_ty A) (u : ctxC Γ σ -o sem_ty B) :
  @nonexpansive R (ctxC Γ σ) (sem_ty (A * B)) (fun γ => (t γ, u γ)).
Proof.
apply/nonexpansiveP => γ γ'; rw cprod_edistE /= ge_max; apply/andP; split.
  exact: nemapP t γ γ'.
exact: nemapP u γ γ'.
Qed.

Lemma sem_proj1_ne Γ σ A1 A2 (t : ctxC Γ σ -o sem_ty (A1 * A2)) :
  @nonexpansive R (ctxC Γ σ) (sem_ty A1) (fun γ => (t γ).1).
Proof.
apply/nonexpansiveP => γ γ'; apply: le_trans _ (nemapP t γ γ').
by rw cprod_edistE le_max lexx.
Qed.

Lemma sem_proj2_ne Γ σ A1 A2 (t : ctxC Γ σ -o sem_ty (A1 * A2)) :
  @nonexpansive R (ctxC Γ σ) (sem_ty A2) (fun γ => (t γ).2).
Proof.
apply/nonexpansiveP => γ γ'; apply: le_trans _ (nemapP t γ γ').
by rw cprod_edistE le_max lexx orbT.
Qed.

(* (inj_i), (CASE): the coproduct. *)
Lemma sem_inj1_ne Γ σ A1 A2 (t : ctxC Γ σ -o sem_ty A1) :
  @nonexpansive R (ctxC Γ σ) (sem_ty (A1 + A2)) (fun γ => inl (t γ)).
Proof.
apply/nonexpansiveP => γ γ'.
by rw (@inl_isometry R (sem_ty A1) (sem_ty A2) (t γ) (t γ')); exact: nemapP t γ γ'.
Qed.

Lemma sem_inj2_ne Γ σ A1 A2 (t : ctxC Γ σ -o sem_ty A2) :
  @nonexpansive R (ctxC Γ σ) (sem_ty (A1 + A2)) (fun γ => inr (t γ)).
Proof.
apply/nonexpansiveP => γ γ'.
by rw (@inr_isometry R (sem_ty A1) (sem_ty A2) (t γ) (t γ')); exact: nemapP t γ γ'.
Qed.

Definition sem_case Γ σ τ A B C r (t : ctxC Γ τ -o sem_ty (A + B))
    (u : ctxC (A :: Γ) (r :: σ) -o sem_ty C)
    (v : ctxC (B :: Γ) (r :: σ) -o sem_ty C)
    (γ : ctxC Γ (σ ⧺ r *: τ)) : sem_ty C :=
  match t γ with inl a => u (γ, a) | inr b => v (γ, b) end.

(* The two summands are at distance +oo, hence r > 0. *)
Lemma sem_case_ne Γ σ τ A B C r (t : ctxC Γ τ -o sem_ty (A + B))
    (u : ctxC (A :: Γ) (r :: σ) -o sem_ty C)
    (v : ctxC (B :: Γ) (r :: σ) -o sem_ty C) :
  size σ = size Γ -> size τ = size Γ -> 0 < r%:num ->
  @nonexpansive R (ctxC Γ (σ ⧺ r *: τ)) (sem_ty C) (sem_case t u v).
Proof.
move=> sG tG r0; apply/nonexpansiveP => γ γ'; rw /sem_case.
rw ctx_edistE ctx_dist_add ?size_senv_scale // ctx_dist_scale //.
have := nemapP t γ γ'; rw ctx_edistE coprod_edistE.
case: (t γ) (t γ') => [a|b] [a'|b'] /= tt'.
- apply: le_trans (nemapP u (γ, a) (γ', a')) _; rw ctx_edistE /=.
  by apply: leeD => //; exact: lee_wpmul2l.
- move: tt'; rw leye_eq => /eqP ->.
  by rw gt0_muley // ge0_addey ?leey //; exact: ctx_dist_ge0.
- move: tt'; rw leye_eq => /eqP ->.
  by rw gt0_muley // ge0_addey ?leey //; exact: ctx_dist_ge0.
- apply: le_trans (nemapP v (γ, b) (γ', b')) _; rw ctx_edistE /=.
  by apply: leeD => //; exact: lee_wpmul2l.
Qed.

(* (⊗), (LET-⊗): the monoidal product. *)
Lemma sem_tensor_ne Γ σ τ ρ A B r s (t : ctxC Γ σ -o sem_ty A)
    (u : ctxC Γ τ -o sem_ty B) :
  size σ = size Γ -> size τ = size Γ -> size ρ = size Γ ->
  @nonexpansive R (ctxC Γ (r *: σ ⧺ s *: τ ⧺ ρ)) (sem_ty (A ⊗[r, s] B))
    (fun γ => (t γ, u γ)).
Proof.
move=> sG tG rG; apply/nonexpansiveP => γ γ'.
have sz1 : size (r *: σ) = size Γ by rw size_senv_scale.
have sz2 : size (s *: τ) = size Γ by rw size_senv_scale.
have sz12 : size (r *: σ ⧺ s *: τ) = size Γ by rw size_senv_add sz1 sz2 minnn.
rw ctx_edistE ctx_dist_add // ctx_dist_add // !ctx_dist_scale //.
rw tensor_edistE /= !scale_edistE.
apply: le_trans _ (leeDl (r%:num * ctx_dist Γ σ γ γ' + s%:num * ctx_dist Γ τ γ γ')
  (@ctx_dist_ge0 Γ ρ γ γ')).
apply: leeD; apply: lee_wpmul2l => //; rw -ctx_edistE.
  exact: nemapP t γ γ'.
exact: nemapP u γ γ'.
Qed.

Definition sem_lettensor Γ σ τ A B C r s
    (t : ctxC (B :: A :: Γ) (s :: r :: σ) -o sem_ty C)
    (u : ctxC Γ τ -o sem_ty (A ⊗[r, s] B)) (γ : ctxC Γ (σ ⧺ τ)) : sem_ty C :=
  t ((γ, (u γ).1), (u γ).2).

Lemma sem_lettensor_ne Γ σ τ A B C r s
    (t : ctxC (B :: A :: Γ) (s :: r :: σ) -o sem_ty C)
    (u : ctxC Γ τ -o sem_ty (A ⊗[r, s] B)) :
  size σ = size Γ -> size τ = size Γ ->
  @nonexpansive R (ctxC Γ (σ ⧺ τ)) (sem_ty C) (sem_lettensor t u).
Proof.
move=> sG tG; apply/nonexpansiveP => γ γ'; rw /sem_lettensor.
apply: le_trans (nemapP t ((γ, (u γ).1), (u γ).2) ((γ', (u γ').1), (u γ').2)) _.
rw !ctx_edistE /= ctx_dist_add // -addeA; apply: leeD => //.
have := nemapP u γ γ'; rw ctx_edistE tensor_edistE /= !scale_edistE.
exact.
Qed.

(* (δ), (⅋_p), (LET): the monad. *)
Lemma sem_dirac_ne Γ σ A (t : ctxC Γ σ -o sem_ty A) :
  @nonexpansive R (ctxC Γ σ) (sem_ty (ty_dist A)) (fun γ => wret W (t γ)).
Proof.
apply/nonexpansiveP => γ γ'; apply: le_trans (wret_dist W (t γ) (t γ')) _.
exact: nemapP t γ γ'.
Qed.

Lemma sem_choice_ne Γ σ τ A (p : prob R) (t : ctxC Γ σ -o sem_ty (ty_dist A))
    (u : ctxC Γ τ -o sem_ty (ty_dist A)) :
  size σ = size Γ -> size τ = size Γ ->
  @nonexpansive R (ctxC Γ (prob_sens p *: σ ⧺ prob_sensC p *: τ))
    (sem_ty (ty_dist A)) (fun γ => wconv W p (t γ) (u γ)).
Proof.
move=> sG tG; apply/nonexpansiveP => γ γ'.
rw ctx_edistE ctx_dist_add ?size_senv_scale // !ctx_dist_scale //.
apply: le_trans (wconv_dist W p _ _ _ _) _; rw -prob_sensE -prob_sensCE.
apply: leeD.
  apply: (lee_wpmul2l (ltW (@prob_sens_gt0 R p))); rw -ctx_edistE.
  exact: nemapP t γ γ'.
apply: (lee_wpmul2l (ltW (@prob_sensC_gt0 R p))); rw -ctx_edistE.
exact: nemapP u γ γ'.
Qed.

(* The algebra maps W⟦E⟧ -> ⟦E⟧: the join on W A, pointwise on products,
   tensors and exponentials, and the point elsewhere (they are only used on
   IB types). *)
Lemma wjoin_ne (X : pseudoMetricType R) :
  @nonexpansive R (wsp W (wsp W X)) (wsp W X) (@wjoin R W X).
Proof. by apply/nonexpansiveP => m m'; exact: wjoin_dist. Qed.

Lemma walg_prod_ne (X Y : pseudoMetricType R) (aX : wsp W X -o X)
    (aY : wsp W Y -o Y) :
  @nonexpansive R (wsp W (cprod X Y)) (cprod X Y)
    (fun m => (aX (wmap W (cprod_fst X Y) m), aY (wmap W (cprod_snd X Y) m))).
Proof.
apply/nonexpansiveP => m m'; rw cprod_edistE /= ge_max; apply/andP; split.
  exact: le_trans (nemapP aX (wmap W (cprod_fst X Y) m) (wmap W (cprod_fst X Y) m'))
    (wmap_dist W (cprod_fst X Y) m m').
exact: le_trans (nemapP aY (wmap W (cprod_snd X Y) m) (wmap W (cprod_snd X Y) m'))
  (wmap_dist W (cprod_snd X Y) m m').
Qed.

Lemma walg_tensor_ne (X Y : pseudoMetricType R) (r s : sens R)
    (aX : wsp W X -o X) (aY : wsp W Y -o Y) :
  @nonexpansive R (wsp W (tensor (scale r X) (scale s Y)))
    (tensor (scale r X) (scale s Y))
    (fun m => (aX (wmap W (tensor_fst (scale r X) (scale s Y)) m),
               aY (wmap W (tensor_snd (scale r X) (scale s Y)) m))).
Proof.
apply/nonexpansiveP => m m'; rw tensor_edistE /= !scale_edistE.
apply: le_trans _ (wtensor_dist W m m').
rw !wsp_edistE !wdist_scale -!wsp_edistE.
apply: leeD; apply: lee_wpmul2l => //.
  exact: nemapP aX (wmap W (tensor_fst _ _) m) (wmap W (tensor_fst _ _) m').
exact: nemapP aY (wmap W (tensor_snd _ _) m) (wmap W (tensor_snd _ _) m').
Qed.

Lemma walg_lolli_subproof (X Y : pseudoMetricType R) (aY : wsp W Y -o Y)
    (m : wsp W (X -o Y)) :
  @nonexpansive R X Y (fun x => aY (wmap W (@nemap_ev R X Y x) m)).
Proof.
apply/nonexpansiveP => x x'.
apply: le_trans (nemapP aY (wmap W (@nemap_ev R X Y x) m) (wmap W (@nemap_ev R X Y x') m)) _.
by apply: wmap_bound => f /=; exact: nemapP f x x'.
Qed.

Definition walg_lolli (X Y : pseudoMetricType R) (aY : wsp W Y -o Y)
  (m : wsp W (X -o Y)) : X -o Y := NEMap (walg_lolli_subproof aY m).

Lemma walg_lolli_ne (X Y : pseudoMetricType R) (aY : wsp W Y -o Y) :
  @nonexpansive R (wsp W (X -o Y)) (X -o Y) (walg_lolli aY).
Proof.
apply/nonexpansiveP => m m'; apply: nemap_edist_le => [|x /=].
  exact: edist_ge0.
exact: le_trans (nemapP aY (wmap W (@nemap_ev R X Y x) m) (wmap W (@nemap_ev R X Y x) m'))
  (wmap_dist W (@nemap_ev R X Y x) m m').
Qed.

Fixpoint walg (E : ty R) : wsp W (sem_ty E) -o sem_ty E :=
  match E with
  | ty_nat =>
    NEMap (@nonexpansive_cst R (wsp W (sem_ty ty_nat)) (sem_ty ty_nat) point)
  | ty_unit =>
    NEMap (@nonexpansive_cst R (wsp W (sem_ty ty_unit)) (sem_ty ty_unit) point)
  | ty_prod A B => NEMap (walg_prod_ne (walg A) (walg B))
  | ty_sum A B =>
    NEMap (@nonexpansive_cst R (wsp W (sem_ty (A + B))) (sem_ty (A + B)) point)
  | ty_tensor r A s B =>
    NEMap (@walg_tensor_ne (sem_ty A) (sem_ty B) r s (walg A) (walg B))
  | ty_lolli r A B =>
    NEMap (@walg_lolli_ne (scale r (sem_ty A)) (sem_ty B) (walg B))
  | ty_dist A => NEMap (@wjoin_ne (sem_ty A))
  end.

(* let x = u in t: the algebra applied to the pushforward of the measure
   ⟦u⟧ γ along the curried ⟦t⟧ γ; the latter is r-Lipschitz, whence rΓ'. *)
Definition sem_let Γ σ τ A E r (t : ctxC (A :: Γ) (r :: σ) -o sem_ty E)
    (u : ctxC Γ τ -o sem_ty (ty_dist A)) (γ : ctxC Γ (σ ⧺ r *: τ)) : sem_ty E :=
  walg E (wmap W (sem_abs t γ) (u γ)).

Lemma sem_let_ne Γ σ τ A E r (t : ctxC (A :: Γ) (r :: σ) -o sem_ty E)
    (u : ctxC Γ τ -o sem_ty (ty_dist A)) :
  size σ = size Γ -> size τ = size Γ ->
  @nonexpansive R (ctxC Γ (σ ⧺ r *: τ)) (sem_ty E) (sem_let t u).
Proof.
move=> sG tG; apply/nonexpansiveP => γ γ'; rw /sem_let.
rw ctx_edistE ctx_dist_add ?size_senv_scale // ctx_dist_scale //.
apply: le_trans (nemapP (walg E) (wmap W (sem_abs t γ) (u γ))
  (wmap W (sem_abs t γ') (u γ'))) _.
apply: le_trans (edist_triangle (wmap W (sem_abs t γ) (u γ) : wsp W (sem_ty E))
  (wmap W (sem_abs t γ') (u γ)) (wmap W (sem_abs t γ') (u γ'))) _.
apply: leeD.
  apply: wmap_bound => a /=.
  apply: le_trans (nemapP t (γ, a) (γ', a)) _.
  by rw ctx_edistE /= edist_refl mule0 adde0.
apply: le_trans (wmap_dist W (sem_abs t γ') (u γ) (u γ')) _.
rw wsp_edistE wdist_scale -wsp_edistE; apply: lee_wpmul2l => //.
by rw -ctx_edistE; exact: nemapP u γ γ'.
Qed.

(* (ZERO), (SUCC), (REC): the natural numbers, with the discrete distance. *)
Lemma sem_succ_ne Γ σ (t : ctxC Γ σ -o sem_ty ty_nat) :
  @nonexpansive R (ctxC Γ σ) (sem_ty ty_nat) (fun γ => (t γ).+1).
Proof.
apply/nonexpansiveP => γ γ'; apply: le_trans _ (nemapP t γ γ').
by rw !discrete_edistE eqSS.
Qed.

Definition sem_natrec Γ σ τ ρ A (z : ctxC Γ σ -o sem_ty A)
    (st : ctxC (ty_nat :: A :: Γ) (sens1 :: sens1 :: τ) -o sem_ty A)
    (n : ctxC Γ ρ -o sem_ty ty_nat) (γ : ctxC Γ (σ ⧺ sensy *: τ ⧺ ρ)) :
    sem_ty A :=
  natrec_fun (z γ) (fun a k => st ((γ, a), k)) (n γ).

(* The step uses its context with sensitivity +oo and the argument with the
   discrete distance: both are either equal or at distance +oo. *)
Lemma sem_natrec_ne Γ σ τ ρ A (z : ctxC Γ σ -o sem_ty A)
    (st : ctxC (ty_nat :: A :: Γ) (sens1 :: sens1 :: τ) -o sem_ty A)
    (n : ctxC Γ ρ -o sem_ty ty_nat) :
  size σ = size Γ -> size τ = size Γ -> size ρ = size Γ ->
  @nonexpansive R (ctxC Γ (σ ⧺ sensy *: τ ⧺ ρ)) (sem_ty A) (sem_natrec z st n).
Proof.
move=> sG tG rG; apply/nonexpansiveP => γ γ'; rw /sem_natrec.
have szt : size (sensy *: τ) = size Γ by rw size_senv_scale.
have sz : size (σ ⧺ sensy *: τ) = size Γ by rw size_senv_add sG szt minnn.
rw ctx_edistE ctx_dist_add // ctx_dist_add // ctx_dist_scale // sensyE.
have := nemapP n γ γ'; rw ctx_edistE discrete_edistE.
case: eqP => [nE _|_]; last first.
  rw leye_eq => /eqP ->; rw ge0_addey ?leey //.
  by apply: adde_ge0; [exact: ctx_dist_ge0 | apply: mule_ge0 => //; exact: ctx_dist_ge0].
rw nE.
have [tau0|tau0] := eqVneq (ctx_dist Γ τ γ γ') 0; last first.
  rw gt0_mulye ?lt_def ?tau0 ?ctx_dist_ge0 //.
  by rw ge0_addey ?ctx_dist_ge0 // ge0_addye ?ctx_dist_ge0 // leey.
rw tau0 mule0 adde0.
have step a a' k : edist (a, a') <= ctx_dist Γ σ γ γ' + ctx_dist Γ ρ γ γ' ->
    edist (st ((γ, a), k), st ((γ', a'), k)) <=
    ctx_dist Γ σ γ γ' + ctx_dist Γ ρ γ γ'.
  move=> aa'; apply: le_trans (nemapP st ((γ, a), k) ((γ', a'), k)) _.
  by rw ctx_edistE /= tau0 add0e edist_refl mule0 adde0 sens1E mul1e.
elim: (n γ') => [|k ih] /=; last exact: step.
apply: le_trans (nemapP z γ γ') _; rw ctx_edistE; apply: leeDl.
exact: ctx_dist_ge0.
Qed.

(* (FIX): the guarded fixed point semfix, from the seed point. *)
Lemma sem_fix_contr Γ σ A (r : contr R)
    (t : ctxC (A :: Γ) (contr_sens r :: contr_sensC r *: σ) -o sem_ty A)
    (γ : ctxC Γ (contr_sensC r *: σ)) :
  econtraction r (fun a : sem_ty A => t (γ, a)).
Proof.
move=> a a' /=; apply: le_trans (nemapP t (γ, a) (γ, a')) _.
by rw ctx_edistE /= ctx_dist_xx add0e.
Qed.

Definition sem_fix Γ σ A (r : contr R)
    (t : ctxC (A :: Γ) (contr_sens r :: contr_sensC r *: σ) -o sem_ty A)
    (γ : ctxC Γ σ) : sem_ty A :=
  semfix (X := ctxC Γ (contr_sensC r *: σ)) (fun γ a => t (γ, a)) point γ.

Lemma sem_fix_ne Γ σ A (r : contr R)
    (t : ctxC (A :: Γ) (contr_sens r :: contr_sensC r *: σ) -o sem_ty A) :
  size σ = size Γ -> @nonexpansive R (ctxC Γ σ) (sem_ty A) (sem_fix t).
Proof.
move=> sG; apply/nonexpansiveP => γ γ'; rw /sem_fix.
have FX (γ0 γ1 : ctxC Γ (contr_sensC r *: σ)) a :
    edist (t (γ0, a), t (γ1, a)) <= edist (γ0, γ1).
  apply: le_trans (nemapP t (γ0, a) (γ1, a)) _.
  by rw !ctx_edistE /= edist_refl mule0 adde0.
have q1 : (0 < 1 - fine r%:num)%R by rw subr_gt0 econtraction_fine_lt1.
move: (semfix_param (point : sem_ty A) (sem_fix_contr t) FX γ γ').
rw ctx_edistE ctx_dist_scale // contr_sensCE -ctx_edistE.
by rw -[r%:num]fineK ?econtraction_fin // -EFinB lee_pmul2l // lte_fin.
Qed.

(** * The interpretation of derivations *)

Fixpoint sem Γ σ t A (d : Γ ⊢[ σ ] t : A) : ctxC Γ σ -o sem_ty A :=
  match d in typed Γ σ t A return ctxC Γ σ -o sem_ty A with
  | typed_var Γ σ i A iG e r1 sG => sem_var iG e r1 sG
  | typed_abs Γ σ t A B r d => NEMap (sem_abs_ne (sem d))
  | typed_app Γ σ τ t u A B r d1 d2 =>
    NEMap (sem_app_ne (sem d1) (sem d2) (typed_size d1) (typed_size d2))
  | typed_unit Γ σ _ =>
    NEMap (@nonexpansive_cst R (ctxC Γ σ) (sem_ty ty_unit) tt)
  | typed_pair Γ σ t u A B d1 d2 => NEMap (sem_pair_ne (sem d1) (sem d2))
  | typed_proj1 Γ σ t A1 A2 d => NEMap (sem_proj1_ne (sem d))
  | typed_proj2 Γ σ t A1 A2 d => NEMap (sem_proj2_ne (sem d))
  | typed_inj1 Γ σ t A1 A2 d => NEMap (@sem_inj1_ne Γ σ A1 A2 (sem d))
  | typed_inj2 Γ σ t A1 A2 d => NEMap (@sem_inj2_ne Γ σ A1 A2 (sem d))
  | typed_case Γ σ τ t u v A B C r d1 d2 d3 r0 =>
    NEMap (sem_case_ne (sem d1) (sem d2) (sem d3) (typed_size_cons d2)
      (typed_size d1) r0)
  | typed_tensor Γ σ τ ρ t u A B r s d1 d2 rG =>
    NEMap (@sem_tensor_ne Γ σ τ ρ A B r s (sem d1) (sem d2) (typed_size d1)
      (typed_size d2) rG)
  | typed_lettensor Γ σ τ t u A B C r s d1 d2 =>
    NEMap (sem_lettensor_ne (sem d1) (sem d2) (typed_size_cons2 d1)
      (typed_size d2))
  | typed_dirac Γ σ t A d => NEMap (sem_dirac_ne (sem d))
  | typed_choice Γ σ τ t u A p d1 d2 =>
    NEMap (@sem_choice_ne Γ σ τ A p (sem d1) (sem d2) (typed_size d1)
      (typed_size d2))
  | typed_let Γ σ τ t u A E r d1 d2 _ _ =>
    NEMap (sem_let_ne (sem d1) (sem d2) (typed_size_cons d1) (typed_size d2))
  | typed_zero Γ σ _ =>
    NEMap (@nonexpansive_cst R (ctxC Γ σ) (sem_ty ty_nat) O)
  | typed_succ Γ σ t d => NEMap (sem_succ_ne (sem d))
  | typed_natrec Γ σ τ ρ z st n A d1 d2 d3 =>
    NEMap (sem_natrec_ne (sem d1) (sem d2) (sem d3) (typed_size d1)
      (typed_size_cons2 d2) (typed_size d3))
  | typed_fix Γ σ t A r d =>
    NEMap (sem_fix_ne (sem d) (etrans (esym (size_senv_scale _ _)) (typed_size_cons d)))
  end.

(* Soundness: judgements denote morphisms of CExtMet. *)
Theorem sem_nonexpansive Γ σ t A (d : Γ ⊢[ σ ] t : A) : nonexpansive (sem d).
Proof. exact: nemap_ne. Qed.

(* The semantic equations of the paper. *)
Lemma sem_absE Γ σ t A B r (d : A :: Γ ⊢[ r :: σ ] t : B) γ a :
  sem (typed_abs d) γ a = sem d (γ, a).
Proof. by []. Qed.

Lemma sem_appE Γ σ τ t u A B r (d1 : Γ ⊢[ σ ] t : A ⊸[r] B)
    (d2 : Γ ⊢[ τ ] u : A) γ :
  sem (typed_app d1 d2) γ = sem d1 γ (sem d2 γ).
Proof. by []. Qed.

Lemma sem_letE Γ σ τ t u A E r (d1 : A :: Γ ⊢[ r :: σ ] t : E)
    (d2 : Γ ⊢[ τ ] u : ty_dist A) (ibE : ib_ty E) (rfin : r%:num < +oo) γ :
  sem (typed_let d1 d2 ibE rfin) γ = walg E (wmap W (sem_abs (sem d1) γ) (sem d2 γ)).
Proof. by []. Qed.

(* fix x. t is a fixed point of t, at every environment whose seed is at
   finite displacement (always, in a single galaxy). *)
Lemma sem_fixP Γ σ t A (r : contr R)
    (d : A :: Γ ⊢[ contr_sens r :: contr_sensC r *: σ ] t : A) (γ : ctxC Γ σ) :
  edist (point, sem d (γ, point)) < +oo ->
  edist (sem (typed_fix d) γ, sem d (γ, sem (typed_fix d) γ)) = 0.
Proof.
move=> fin; rw /= /sem_fix /semfix /= fin.
by have := pfix_edist0 (sem_fix_contr (sem d) γ) fin.
Qed.

End semantics.
