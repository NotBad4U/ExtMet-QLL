(* The closed symmetric monoidal category CExtMet (paper, Sect. 2). *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module exp.
From ExtMetQLL Require Import analysis_extras extmet.

(**md**************************************************************************)
(* # The category CExtMet                                                     *)
(*                                                                            *)
(* Objects are extended (pseudo)metric spaces, morphisms non-expansive maps   *)
(* (extmet.v); completeness is complete_space (analysis_extras.v).            *)
(*                                                                            *)
(* ```                                                                        *)
(*       isometry f == edist (f x, f y) = edist (x, y)                        *)
(*             unit == the monoidal unit 1, with distance 0                   *)
(*        scale r X == r X, the space X with distance r * edist, for          *)
(*                     r : {nonneg \bar R} (with 0 * +oo = 0)                 *)
(*       pscale r X == scale r X for r : {posnum \bar R}; an extMetricType    *)
(*                     when X is                                              *)
(*      coprod X Y == X + Y, components at distance +oo                       *)
(*    copair f g == the copairing [f, g] : coprod X Y -> Z                    *)
(*          X -o Y == the non-expansive maps from X to Y (nemap X Y), with    *)
(*                     the sup distance                                       *)
(*        nemap_eval == evaluation (X -o Y) ⊗ X -> Y                         *)
(*  nemap_curry f, nemap_uncurry g == the closed monoidal adjunction          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition isometry {R : realType} {X Y : pseudoMetricType R} (f : X -> Y) :=
  forall x x', edist (f x, f x') = edist (x, x').

Lemma isometry_nonexpansive {R : realType} (X Y : pseudoMetricType R)
    (f : X -> Y) : isometry f -> nonexpansive f.
Proof. by move=> hf; apply/nonexpansiveP => x x'; rw hf. Qed.

(** * The monoidal unit *)

Section unit_space.
Context {R : realType}.

Let unit_dist (_ _ : unit) : \bar R := 0.

Let unit_dist_ge0 x y : 0 <= unit_dist x y. Proof. by []. Qed.
Let unit_dist_xx : self_inverse 0 unit_dist. Proof. by []. Qed.
Let unit_distC : commutative unit_dist. Proof. by []. Qed.
Let unit_dist_triangle x y z : unit_dist x z <= unit_dist x y + unit_dist y z.
Proof. by rw /unit_dist adde0. Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R unit
  unit_dist_ge0 unit_dist_xx unit_distC unit_dist_triangle.

Lemma unit_edistE (x y : unit) : edist (x, y) = 0 :> \bar R.
Proof. exact: (@edistE _ _ unit_dist). Qed.

Let unit_edist_eq0 (x y : unit) : edist (x, y) = 0 :> \bar R -> x = y.
Proof. by case: x; case: y. Qed.

HB.instance Definition _ := PseudoMetric_isExtMetric.Build R unit
  unit_edist_eq0.

Lemma nonexpansive_unit (X : pseudoMetricType R) :
  nonexpansive (fun _ : X => tt).
Proof. by apply/nonexpansiveP => x x'; rw unit_edistE. Qed.

Lemma unit_map_unique (X : Type) (f g : X -> unit) : f = g.
Proof. by apply/funext => x; case: (f x); case: (g x). Qed.

End unit_space.

(** * Scaling *)

Definition scale {R : realType} (r : {nonneg \bar R}) (X : pseudoMetricType R)
  : Type := X.

Section scale.
Context {R : realType} (r : {nonneg \bar R}) (X : pseudoMetricType R).
Local Notation S := (scale r X).

HB.instance Definition _ := Choice.on S.

Definition scale_dist (x y : S) : \bar R := r%:num * edist ((x : X), (y : X)).

Let scale_dist_ge0 x y : 0 <= scale_dist x y.
Proof. exact: mule_ge0. Qed.

Let scale_dist_xx : self_inverse 0 scale_dist.
Proof. by move=> x; rw /scale_dist edist_refl mule0. Qed.

Let scale_distC : commutative scale_dist.
Proof. by move=> x y; rw /scale_dist edist_sym. Qed.

Let scale_dist_triangle x y z :
  scale_dist x z <= scale_dist x y + scale_dist y z.
Proof.
rw /scale_dist -ge0_muleDr //; apply: lee_wpmul2l => //.
exact: edist_triangle.
Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R S
  scale_dist_ge0 scale_dist_xx scale_distC scale_dist_triangle.

Lemma scale_edistE (x y : S) : edist (x, y) = r%:num * edist ((x : X), (y : X)).
Proof. exact: (@edistE _ _ scale_dist). Qed.

(* Non-expansive maps out of r X are the r-Lipschitz maps out of X. *)
Lemma nonexpansive_scale (Y : pseudoMetricType R) (f : X -> Y) :
  @nonexpansive R S Y f <-> r.-elipschitz f.
Proof.
split=> [/nonexpansiveP hf x x' | hf]; first by rw -scale_edistE; exact: hf.
by apply/nonexpansiveP => x x'; rw scale_edistE; exact: hf.
Qed.

Lemma scale_edist_eq0 (x y : S) : 0 < r%:num -> edist (x, y) = 0 ->
  edist ((x : X), (y : X)) = 0.
Proof.
by move=> r0 /eqP; rw scale_edistE mule_eq0 gt_eqF //= => /eqP.
Qed.

End scale.

Section scale_props.
Context {R : realType}.
Implicit Types (r s : {nonneg \bar R}) (X Y : pseudoMetricType R).

Lemma scale0_edistE X (x y : scale (0%R%:E)%:nng X) : edist (x, y) = 0.
Proof. by rw scale_edistE mul0e. Qed.

(* 0 X is indiscrete: non-expansive maps from 0 X to a separated space are
   constant (the paper sets 0 X := 1, the quotient of 0 X). *)
Lemma scale0_nonexpansive_cst X (Y : extMetricType R)
    (f : scale (0%R%:E)%:nng X -> Y) :
  nonexpansive f -> forall x y, f x = f y.
Proof.
move=> /nonexpansiveP hf x y; apply: edist_eq0; apply/le_anti.
by rw edist_ge0 andbT -(scale0_edistE x y); exact: hf.
Qed.

(* +oo X is {0, +oo}-valued. *)
Lemma scaley_edistE X (x y : scale (+oo : \bar R)%:nng X) :
  edist (x, y) = if edist ((x : X), (y : X)) == 0 then 0 else +oo.
Proof.
rw scale_edistE /=; case: eqP => [->|/eqP d0]; first by rw mule0.
by rw gt0_mulye // lt_def d0 edist_ge0.
Qed.

Lemma scale1_isometry X : @isometry R X (scale 1%:E%:nng X) id.
Proof. by move=> x y; rw scale_edistE mul1e. Qed.

Lemma scale1_isometryV X : @isometry R (scale 1%:E%:nng X) X id.
Proof. by move=> x y; rw scale_edistE mul1e. Qed.

(* (r s) X ≅ r (s X) *)
Lemma scaleM_isometry r s X :
  @isometry R (scale r (scale s X)) (scale (r%:num * s%:num)%:nng X) id.
Proof. by move=> x y; rw !scale_edistE muleA. Qed.

Lemma scaleM_isometryV r s X :
  @isometry R (scale (r%:num * s%:num)%:nng X) (scale r (scale s X)) id.
Proof. by move=> x y; rw !scale_edistE muleA. Qed.

(* r 1 ≅ 1 *)
Lemma scale_unit_isometry r : @isometry R (scale r unit) unit id.
Proof. by move=> x y; rw scale_edistE !unit_edistE mule0. Qed.

(* r (X ⊗ Y) ≅ r X ⊗ r Y: scaling is strong monoidal. *)
Lemma scale_tensor_isometry r X Y :
  @isometry R (scale r (tensor X Y)) (tensor (scale r X) (scale r Y)) id.
Proof.
by move=> u v; rw scale_edistE !tensor_edistE !scale_edistE ge0_muleDr.
Qed.

Lemma scale_tensor_isometryV r X Y :
  @isometry R (tensor (scale r X) (scale r Y)) (scale r (tensor X Y)) id.
Proof.
by move=> u v; rw scale_edistE !tensor_edistE !scale_edistE ge0_muleDr.
Qed.

(* For 0 < r < +oo, r X and X have the same uniformity, hence the same
   topology. *)
Lemma scale_entourageE (r : {posnum R}) X :
  @entourage (scale (r%:num%:E)%:nng X) = @entourage X.
Proof.
apply/funext => A; apply/propext; rw !entourage_edistP.
split=> -[e e0 eA].
  exists (e / r%:num)%R; first exact: divr_gt0.
  move=> [x y] /= dxy; apply: eA => /=; rw scale_edistE /= -lte_pdivlMl //.
  by rw -EFinM mulrC.
exists (r%:num * e)%R; first exact: mulr_gt0.
move=> [x y] /=; rw scale_edistE /= EFinM => dxy; apply: eA => /=.
by move: dxy; rw lte_pmul2l.
Qed.

Lemma scale_nbhsE (r : {posnum R}) X :
  @nbhs _ (scale (r%:num%:E)%:nng X) = @nbhs _ X.
Proof. by rw -[LHS]nbhs_entourageE -[RHS]nbhs_entourageE scale_entourageE. Qed.

End scale_props.

(* Positive scalings of extended metric spaces are extended metric spaces. *)
Definition pscale {R : realType} (r : {posnum \bar R}) (X : extMetricType R)
  : Type := scale (r%:num)%:nng X.

Section pscale.
Context {R : realType} (r : {posnum \bar R}) (X : extMetricType R).

HB.instance Definition _ := PseudoMetric.on (pscale r X).

Let pscale_edist_eq0 (x y : pscale r X) : edist (x, y) = 0 -> x = y.
Proof.
move=> xy0; apply: edist_eq0.
apply: (@scale_edist_eq0 R (r%:num)%:nng X x y) => //.
by rw /=; exact: (gt0e r).
Qed.

HB.instance Definition _ := PseudoMetric_isExtMetric.Build R (pscale r X)
  pscale_edist_eq0.

End pscale.

(** * Coproducts *)

Definition coprod {R : realType} (X Y : pseudoMetricType R) : Type :=
  (X + Y)%type.

Section coprod.
Context {R : realType} (X Y : pseudoMetricType R).
Local Notation C := (coprod X Y).

HB.instance Definition _ := Choice.on C.

Definition coprod_dist (u v : C) : \bar R :=
  match u, v with
  | inl a, inl a' => edist (a, a')
  | inr b, inr b' => edist (b, b')
  | _, _ => +oo
  end.

Let coprod_dist_ge0 u v : 0 <= coprod_dist u v.
Proof. by case: u v => [a|b] [a'|b'] /=; rw ?leey. Qed.

Let coprod_dist_xx : self_inverse 0 coprod_dist.
Proof. by case=> x /=; rw edist_refl. Qed.

Let coprod_distC : commutative coprod_dist.
Proof. by case=> [a|b] [a'|b'] //=; rw edist_sym. Qed.

Let coprod_dist_triangle u v w :
  coprod_dist u w <= coprod_dist u v + coprod_dist v w.
Proof.
case: u v w => [a|b] [a'|b'] [a''|b''] /=; rw ?edist_triangle //;
  by rw ?addye ?addey ?leey.
Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R C
  coprod_dist_ge0 coprod_dist_xx coprod_distC coprod_dist_triangle.

Lemma coprod_edistE (u v : C) : edist (u, v) = coprod_dist u v.
Proof. exact: (@edistE _ _ coprod_dist). Qed.

Lemma inl_isometry : @isometry R X C inl.
Proof. by move=> a a'; rw coprod_edistE. Qed.

Lemma inr_isometry : @isometry R Y C inr.
Proof. by move=> b b'; rw coprod_edistE. Qed.

Lemma edist_inl_inr a b : edist ((inl a : C), (inr b : C)) = +oo.
Proof. by rw coprod_edistE. Qed.

Definition copair {Z : Type} (f : X -> Z) (g : Y -> Z) (u : C) : Z :=
  match u with inl a => f a | inr b => g b end.

Lemma nonexpansive_copair (Z : pseudoMetricType R) (f : X -> Z) (g : Y -> Z) :
  nonexpansive f -> nonexpansive g -> nonexpansive (copair f g).
Proof.
move=> /nonexpansiveP hf /nonexpansiveP hg; apply/nonexpansiveP.
by case=> [a|b] [a'|b']; rw coprod_edistE /= ?leey.
Qed.

End coprod.

Section coprod_metric.
Context {R : realType} (X Y : extMetricType R).

Let coprod_edist_eq0 (u v : coprod X Y) : edist (u, v) = 0 -> u = v.
Proof.
by rw coprod_edistE; case: u v => [a|b] [a'|b'] //= /edist_eq0 ->.
Qed.

HB.instance Definition _ := PseudoMetric_isExtMetric.Build R (coprod X Y)
  coprod_edist_eq0.

End coprod_metric.

(* r (X + Y) ≅ r X + r Y for r > 0 *)
Lemma scale_coprod_isometry {R : realType} (r : {nonneg \bar R})
    (X Y : pseudoMetricType R) : 0 < r%:num ->
  @isometry R (scale r (coprod X Y)) (coprod (scale r X) (scale r Y)) id.
Proof.
move=> r0 u v; rw scale_edistE !coprod_edistE.
by case: u v => [a|b] [a'|b'] /=; rw ?scale_edistE ?gt0_muley.
Qed.

Lemma scale_coprod_isometryV {R : realType} (r : {nonneg \bar R})
    (X Y : pseudoMetricType R) : 0 < r%:num ->
  @isometry R (coprod (scale r X) (scale r Y)) (scale r (coprod X Y)) id.
Proof. by move=> r0 u v; rw (@scale_coprod_isometry _ r X Y r0). Qed.

(** * Internal hom *)

Record nemap {R : realType} (X Y : pseudoMetricType R) := NEMap {
  nemap_fun :> X -> Y;
  nemap_ne : nonexpansive nemap_fun }.

Notation "X -o Y" := (nemap X Y) (at level 99, right associativity)
  : type_scope.

Section nemap.
Context {R : realType} (X Y : pseudoMetricType R).
Implicit Types f g h : X -o Y.

HB.instance Definition _ := gen_eqMixin (X -o Y).
HB.instance Definition _ := gen_choiceMixin (X -o Y).

Lemma nemap_ext f g : f =1 g -> f = g.
Proof.
case: f g => [f hf] [g hg] /= /funext fg; subst g; congr NEMap.
exact: Prop_irrelevance.
Qed.

(* the sup distance, clamped at 0 for an empty domain *)
Definition nemap_dist f g : \bar R :=
  maxe 0 (ereal_sup [set edist (f x, g x) | x in [set: X]]).

Let nemap_dist_ub f g x : edist (f x, g x) <= nemap_dist f g.
Proof.
rw le_max; apply/orP; right; apply: ereal_sup_ubound; by exists x.
Qed.

Let nemap_dist_le f g e : 0 <= e -> (forall x, edist (f x, g x) <= e) ->
  nemap_dist f g <= e.
Proof.
move=> e0 fge; rw ge_max e0 /=; apply: ge_ereal_sup => _ [x _ <-].
exact: fge.
Qed.

Let nemap_dist_ge0 f g : 0 <= nemap_dist f g.
Proof. by rw le_max lexx. Qed.

Let nemap_dist_xx : self_inverse 0 nemap_dist.
Proof.
by move=> f; apply/le_anti; rw nemap_dist_ge0 andbT nemap_dist_le // => x;
  rw edist_refl.
Qed.

Let nemap_distC : commutative nemap_dist.
Proof.
move=> f g; apply/le_anti/andP; split; apply: nemap_dist_le => // x;
  by rw edist_sym nemap_dist_ub.
Qed.

Let nemap_dist_triangle f g h :
  nemap_dist f h <= nemap_dist f g + nemap_dist g h.
Proof.
apply: nemap_dist_le => [|x]; first exact: adde_ge0.
apply: le_trans (edist_triangle _ (g x) _) _.
by apply: leeD; exact: nemap_dist_ub.
Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R (X -o Y)
  nemap_dist_ge0 nemap_dist_xx nemap_distC nemap_dist_triangle.

Lemma nemap_edistE f g : edist (f, g) = nemap_dist f g.
Proof. exact: (@edistE _ _ nemap_dist). Qed.

Lemma nemap_edist_ub f g x : edist (f x, g x) <= edist (f, g).
Proof. by rw nemap_edistE. Qed.

Lemma nemap_edist_le f g e : 0 <= e -> (forall x, edist (f x, g x) <= e) ->
  edist (f, g) <= e.
Proof. by rw nemap_edistE; exact: nemap_dist_le. Qed.

End nemap.

Section nemap_metric.
Context {R : realType} (X : pseudoMetricType R) (Y : extMetricType R).

Let nemap_edist_eq0 (f g : X -o Y) : edist (f, g) = 0 -> f = g.
Proof.
move=> fg0; apply: nemap_ext => x; apply: edist_eq0; apply/le_anti.
by rw edist_ge0 andbT -fg0 nemap_edist_ub.
Qed.

HB.instance Definition _ := PseudoMetric_isExtMetric.Build R (X -o Y)
  nemap_edist_eq0.

End nemap_metric.

Section closed_monoidal.
Context {R : realType}.
Implicit Types X Y Z : pseudoMetricType R.

(* The counit of the adjunction: evaluation (X -o Y) ⊗ X -> Y. *)
Definition nemap_eval X Y (u : tensor (X -o Y) X) : Y := nemap_fun u.1 u.2.

Lemma nonexpansive_eval X Y : nonexpansive (@nemap_eval X Y).
Proof.
apply/nonexpansiveP => -[f x] [g x']; rw tensor_edistE /nemap_eval /=.
apply: le_trans (edist_triangle _ (f x') _) _.
rw [X in _ <= X]addeC; apply: leeD.
  exact: (nonexpansiveP _).1 (nemap_ne f) x x'.
exact: nemap_edist_ub.
Qed.

Lemma nemap_curry_subproof X Y Z (f : tensor X Y -o Z) (x : X) :
  nonexpansive (fun y : Y => f (x, y)).
Proof.
apply/nonexpansiveP => y y'.
apply: le_trans ((nonexpansiveP _).1 (nemap_ne f) (x, y) (x, y')) _.
by rw tensor_edistE edist_refl add0e.
Qed.

Definition nemap_curry_fun X Y Z (f : tensor X Y -o Z) (x : X) : Y -o Z :=
  NEMap (nemap_curry_subproof f x).

Lemma nemap_curry_ne X Y Z (f : tensor X Y -o Z) :
  nonexpansive (nemap_curry_fun f).
Proof.
apply/nonexpansiveP => x x'; apply: nemap_edist_le => // y /=.
apply: le_trans ((nonexpansiveP _).1 (nemap_ne f) (x, y) (x', y)) _.
by rw tensor_edistE edist_refl adde0.
Qed.

(* Currying: CExtMet(X ⊗ Y, Z) -> CExtMet(X, Y -o Z). *)
Definition nemap_curry X Y Z (f : tensor X Y -o Z) : X -o (Y -o Z) :=
  NEMap (nemap_curry_ne f).

Lemma nemap_uncurry_ne X Y Z (g : X -o (Y -o Z)) :
  nonexpansive (fun u : tensor X Y => g u.1 u.2).
Proof.
apply/nonexpansiveP => -[x y] [x' y']; rw tensor_edistE /=.
apply: le_trans (edist_triangle _ (g x y') _) _.
rw [X in _ <= X]addeC; apply: leeD.
  exact: (nonexpansiveP _).1 (nemap_ne (g x)) y y'.
apply: le_trans (nemap_edist_ub _ _ y') _.
exact: (nonexpansiveP _).1 (nemap_ne g) x x'.
Qed.

(* Uncurrying: CExtMet(X, Y -o Z) -> CExtMet(X ⊗ Y, Z). *)
Definition nemap_uncurry X Y Z (g : X -o (Y -o Z)) : tensor X Y -o Z :=
  NEMap (nemap_uncurry_ne g).

Lemma nemap_uncurryK X Y Z : cancel (@nemap_uncurry X Y Z) (@nemap_curry X Y Z).
Proof. by move=> g; apply: nemap_ext => x; exact: nemap_ext. Qed.

Lemma nemap_curryK X Y Z : cancel (@nemap_curry X Y Z) (@nemap_uncurry X Y Z).
Proof. by move=> f; apply: nemap_ext => -[]. Qed.

Lemma nemap_curryE X Y Z (f : tensor X Y -o Z) x y :
  nemap_curry f x y = f (x, y).
Proof. by []. Qed.

Lemma nemap_uncurryE X Y Z (g : X -o (Y -o Z)) x y :
  nemap_uncurry g (x, y) = g x y.
Proof. by []. Qed.

End closed_monoidal.

(** * Completeness *)

Section completeness.
Context {R : realType}.
Implicit Types X Y : pseudoMetricType R.

Let e2 (e : R) : e%:E = (e / 2)%R%:E + (e / 2)%R%:E.
Proof. by rw -EFinD -splitr. Qed.

Let half_gt0 (e : R) : (0 < e)%R -> (0 < e / 2)%R.
Proof. by move=> e0; rw divr_gt0. Qed.

(* A Cauchy filter concentrated on the image of an isometry from a complete
   space converges. *)
Lemma complete_isometry X (Z : pseudoMetricType R) (i : X -> Z)
    (F : set_system Z) :
  ProperFilter F -> isometry i -> complete_space X -> cauchy F ->
  F (range i) -> exists z : Z, F --> z.
Proof.
move=> FF iso cX /cauchy_edistP Fc Fi.
pose G : set_system X := [set B | F [set z | forall a, i a = z -> B a]].
have GF : ProperFilter G.
  split; last split.
  - by move=> G0; have [w [[a _ iaw] /(_ a iaw)]] := filter_ex (filterI Fi G0).
  - by rw /G /=; apply: filterS filterT => z _ a _.
  - move=> A B; rw /G /= => GA GB; apply: filterS2 GA GB => z hA hB a iaz.
    by split; [exact: hA | exact: hB].
  - by move=> A B AB; rw /G /=; apply: filterS => z hA a /hA /AB.
have [a Ga] : exists a : X, G --> a.
  apply: cX; apply/cauchy_edistP => e e0.
  have [z Fz] := Fc _ (half_gt0 e0).
  have [w [[a _ iaw] za]] := filter_ex (filterI Fi Fz); subst w.
  exists a; apply: filterS Fz => w zw a' iaw; subst w.
  by rw /= -iso; apply: edist_triangle_half zw; rw edist_sym.
exists (i a); apply/cvg_edistP => e e0.
have /(cvg_edistP _).1 /(_ e e0) Gae := Ga.
by apply: filterS2 Fi Gae => _ [a' _ <-] /(_ a' erefl); rw iso.
Qed.

Lemma tensor_complete X Y :
  complete_space X -> complete_space Y -> complete_space (tensor X Y).
Proof.
move=> cX cY F FF /cauchy_edistP Fc.
have Fc1 : cauchy (fst @ F).
  apply/cauchy_edistP => e e0; have [[x y] Fxy] := Fc e e0.
  exists x; rw /fmap /=; apply: filterS Fxy => -[x' y'] /=; rw tensor_edistE /=.
  by apply: le_lt_trans; exact: leeDl.
have Fc2 : cauchy (snd @ F).
  apply/cauchy_edistP => e e0; have [[x y] Fxy] := Fc e e0.
  exists y; rw /fmap /=; apply: filterS Fxy => -[x' y'] /=; rw tensor_edistE /=.
  by apply: le_lt_trans; exact: leeDr.
have [a /cvg_edistP Fa] := cX _ _ Fc1.
have [b /cvg_edistP Fb] := cY _ _ Fc2.
exists ((a, b) : tensor X Y); apply/cvg_edistP => e e0.
near=> u; rw tensor_edistE e2; apply: lteD; near: u.
  exact: (Fa _ (half_gt0 e0)).
exact: (Fb _ (half_gt0 e0)).
Unshelve. all: by end_near. Qed.

Lemma coprod_complete X Y :
  complete_space X -> complete_space Y -> complete_space (coprod X Y).
Proof.
move=> cX cY F FF Fc; have /cauchy_edistP/(_ 1%R ltr01)[u Fu] := Fc.
case: u Fu => [a|b] Fu.
- apply: (complete_isometry _ (@inl_isometry R X Y) cX Fc).
  apply: filterS Fu => -[a'|b'] /=; first by exists a'.
  by rw coprod_edistE /= ltNge leey.
- apply: (complete_isometry _ (@inr_isometry R X Y) cY Fc).
  apply: filterS Fu => -[a'|b'] /=; last by exists b'.
  by rw coprod_edistE /= ltNge leey.
Qed.

(* +oo X is discrete, hence complete. *)
Lemma scaley_complete (r : {nonneg \bar R}) X : r%:num = +oo ->
  complete_space (scale r X).
Proof.
move=> ry F FF /cauchy_edistP /(_ 1%R ltr01) [x Fx].
exists x; apply/cvg_edistP => e e0; apply: filterS Fx => y /=.
rw !scale_edistE ry; have [->|d0] := eqVneq (edist ((x : X), (y : X))) 0.
  by rw mule0 lte_fin.
have dpos : 0 < edist ((x : X), (y : X)) by rw lt_def d0 edist_ge0.
by rw gt0_mulye // ltNge leey.
Qed.

Lemma scale_complete (r : {nonneg \bar R}) X : 0 < r%:num ->
  complete_space X -> complete_space (scale r X).
Proof.
move=> r0 cX; have [ry|ry] := eqVneq r%:num +oo; first exact: scaley_complete.
have [r' r'0 rE] : exists2 r' : R, (0 < r')%R & r%:num = r'%:E.
  move: r0 ry; case: (r%:num) => [r' r'0 _||]; first by exists r'; rw -?lte_fin.
    by rw eqxx.
  by rw ltNge leNye.
move=> F FF /cauchy_edistP Fc.
have [x /(@cvg_edistP _ X F (@filter_filter _ F FF) x) Fx] :
    exists x : X, F --> x.
  apply: cX; apply/cauchy_edistP => e e0.
  have [x Fxe] := Fc _ (mulr_gt0 r'0 e0); exists x.
  by apply: filterS Fxe => y; rw /= scale_edistE rE EFinM lte_pmul2l.
exists x; apply/cvg_edistP => e e0.
apply: filterS (Fx _ (divr_gt0 e0 r'0)) => y /= dxy.
by rw scale_edistE rE -lte_pdivlMl // -EFinM mulrC.
Qed.

Lemma nemap_complete X Y : complete_space Y -> complete_space (X -o Y).
Proof.
move=> cY F FF /cauchy_edistP Fc.
have Fx x : exists y : Y, (fun f : X -o Y => f x) @ F --> y.
  apply: cY; apply/cauchy_edistP => e e0.
  have [f0 Ff0] := Fc e e0; exists (f0 x); rw /fmap /=.
  by apply: filterS Ff0 => f /=; apply: le_lt_trans; exact: nemap_edist_ub.
pose g x := projT1 (cid (Fx x)).
have gP x : (fun f : X -o Y => f x) @ F --> g x := projT2 (cid (Fx x)).
have gnear x e : (0 < e)%R -> F [set f | edist (g x, f x) < e%:E].
  by move=> e0; exact: (cvg_edistP _).1 (gP x) e e0.
have gne : nonexpansive g.
  apply/nonexpansiveP => x x'; apply/lee_addgt0Pr => e e0; rw e2.
  have [f [fx fx']] := filter_ex
    (filterI (gnear x _ (half_gt0 e0)) (gnear x' _ (half_gt0 e0))).
  apply: le_trans (edist_triangle _ (f x) _) _.
  apply: le_trans (leeD (ltW fx) (edist_triangle _ (f x') _)) _.
  rw addeCA; apply: leeD; first exact: (nonexpansiveP _).1 (nemap_ne f) x x'.
  by apply: leeD => //; rw edist_sym; exact: ltW.
have bound f0 e : (0 < e)%R -> F [set f | edist (f0, f) < e%:E] ->
    edist (NEMap gne, f0) <= e%:E.
  move=> e0 Ff0; apply: nemap_edist_le => [|x /=]; first by rw lee_fin ltW.
  apply/lee_addgt0Pr => d d0.
  have [f [f0f gf]] := filter_ex (filterI Ff0 (gnear x _ d0)).
  apply: le_trans (edist_triangle _ (f x) _) _; rw [X in _ <= X]addeC.
  apply: leeD.
    exact: ltW.
  by rw edist_sym; apply: le_trans (nemap_edist_ub _ _ x) (ltW f0f).
exists (NEMap gne); apply/cvg_edistP => e e0.
have [f0 Ff0] := Fc _ (half_gt0 e0); have gf0 := bound _ _ (half_gt0 e0) Ff0.
apply: filterS Ff0 => f /= f0f; apply: le_lt_trans (edist_triangle _ f0 _) _.
rw e2; apply: lee_ltD => //.
by rw ge0_fin_numE // (le_lt_trans gf0) ?ltey.
Qed.

End completeness.
