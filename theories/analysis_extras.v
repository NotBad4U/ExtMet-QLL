(* Additions to MathComp Analysis, meant to be upstreamed. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import functions sequences measure lebesgue_integral.
From mathcomp Require Import measurable_realfun lebesgue_stieltjes_measure exp.
From mathcomp Require Import hoelder kernel probability.

(**md**************************************************************************)
(* # Additions to MathComp Analysis                                           *)
(*                                                                            *)
(* Each addition sits in a module move_to_X, where X is the Analysis file it *)
(* is meant to be upstreamed to; the module is exported right away.  (A      *)
(* Section cannot hold HB declarations or notations.)                        *)
(*                                                                            *)
(* ```                                                                        *)
(*   {itv \bar R & i} == extended reals in the interval i (bounds in int);   *)
(*                       {nonneg \bar R} is {itv \bar R & `[0, +oo[}          *)
(*   isExtPseudoMetric R d == factory: the pseudoMetricType whose balls are *)
(*                       the strict balls of the extended distance d, so    *)
(*                       that edist = d (edistE)                             *)
(*   hausdorffType == Hausdorff topological space; the HB class is          *)
(*                       Hausdorff, the mixin Topological_isHausdorff        *)
(*   extMetricType R == pseudoMetricType R that is Hausdorff (extended      *)
(*                       metric space); the HB class is ExtMetric            *)
(*   PseudoMetric_isExtMetric == factory: points at edist 0 are equal       *)
(*   minkowski2 == Minkowski's inequality for two-term sums (cf. hoelder2)  *)
(*   eminkowski_ge0 == Minkowski for non-negative extended-real functions   *)
(*   lp_dist p a b == (a^p + b^p)^(1/p) for p real, max a b for p = +oo     *)
(*   ret, bind mu f, bindfg f g == the Giry monad for probabilities on      *)
(*                       probability kernels (from math-comp/analysis#1177) *)
(*   metricMeasurableType R d == pseudoMetricType R that is also a          *)
(*                       measurableType d, with a measurable edist           *)
(*   lp_prod p X Y == X * Y with the l^p combination of the distances,      *)
(*                       p : {itv \bar R & `[1, +oo[}; p = 1 gives the sum  *)
(*                       and p = +oo the max                                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module move_to_constructive_ereal.

(* Interval types on the extended reals: MathComp Analysis only provides the
   instances {nonneg \bar R} (= {itv \bar R & `[0, +oo[}) and
   {posnum \bar R}.  The bounds are read in ring_scope rather than int_scope
   so that they parse with classical_set_scope open. *)
Notation "{ 'itv' '\bar' R & i }" := (Itv.def (@ext_num_sem R) (Itv.Real i%R))
  : type_scope.

End move_to_constructive_ereal.
Export move_to_constructive_ereal.

Module move_to_metric_structure.
(* Upstream, metric_structure.v also needs to import constructive_ereal. *)

HB.factory Record isExtPseudoMetric (R : realType) (M : Type) & Choice M := {
  d : M -> M -> \bar R;
  d_ge0 : forall x y, 0 <= d x y;
  d_xx : self_inverse 0 d;
  dC : commutative d;
  d_triangle : forall x y z, d x z <= d x y + d y z;
}.

HB.builders Context R M & isExtPseudoMetric R M.

Let ball (x : M) (e : R) : set M := [set y | d x y < e%:E].

Let ent : set_system (M * M) := entourage_ ball.

Let nbhs (x : M) : set_system M := nbhs_ ent x.

Let nbhsE : nbhs = nbhs_ ent. Proof. by []. Qed.

HB.instance Definition _ := hasNbhs.Build M nbhs.

Let ball_center x (e : R) : (0 < e)%R -> ball x e x.
Proof. by move=> e0; rw /ball /= d_xx lte_fin. Qed.

Let ball_sym x y (e : R) : ball x e y -> ball y e x.
Proof. by rw /ball /= dC. Qed.

Let ball_triangle x y z e1 e2 : ball x e1 y -> ball y e2 z ->
  ball x (e1 + e2) z.
Proof.
rw /ball /= => xy yz.
by rw (le_lt_trans (d_triangle x y z)) // EFinD lteD.
Qed.

Let entourageE : ent = entourage_ ball. Proof. by []. Qed.

HB.instance Definition _ := @Nbhs_isPseudoMetric.Build R M
  ent nbhsE ball ball_center ball_sym ball_triangle entourageE.

HB.end.

End move_to_metric_structure.
Export move_to_metric_structure.

Module move_to_separation_axioms.

(* Hausdorff topological spaces, as a structure (Analysis only has the
   predicate [hausdorff_space]). *)
HB.mixin Record Topological_isHausdorff T & Topological T := {
  hausdorff_subproof : hausdorff_space T
}.

#[short(type="hausdorffType")]
HB.structure Definition Hausdorff :=
  { T of Topological T & Topological_isHausdorff T }.

Lemma hausdorffT (T : hausdorffType) : hausdorff_space T.
Proof. exact: hausdorff_subproof. Qed.

End move_to_separation_axioms.
Export move_to_separation_axioms.

Module move_to_urysohn.

(* When the balls are the strict balls of a non-negative extended distance
   [d], Analysis's [edist] is [d]. *)
Lemma edistE {R : realType} (M : pseudoMetricType R) (d : M -> M -> \bar R) :
  (forall x y, 0 <= d x y) ->
  (forall x y r, ball x r y <-> d x y < r%:E) ->
  forall x y, edist (x, y) = d x y.
Proof.
move=> d_ge0 ballE x y; apply/le_anti/andP; split; last first.
  by apply: le_ereal_inf_tmp => _ [r [_ /ballE /ltW dr] <-].
move: (d_ge0 x y) => /gee0P[->|[a a0 dxy]]; first exact: leey.
apply/lee_addgt0Pr => e e0; rw dxy -EFinD.
apply: edist_fin; first exact: ltr_wpDl a0 e0.
by apply/ballE; rw dxy lte_fin ltrDl.
Qed.

Lemma normed_edistE {R : realType} (V : normedModType R) (x y : V) :
  edist (x, y) = `|x - y|%:E.
Proof.
apply: (@edistE _ _ (fun a b : V => `|a - b|%:E)) => [? ?|a b e] /=.
  by rw lee_fin.
by rw -ball_normE /ball_ /= lte_fin.
Qed.

(* Extended metric spaces: separated extended pseudometric spaces. *)
#[short(type="extMetricType")]
HB.structure Definition ExtMetric (R : realType) :=
  { M of PseudoMetric R M & Topological_isHausdorff M }.

(* Separation stated with the extended distance. *)
HB.factory Record PseudoMetric_isExtMetric (R : realType) M
    & PseudoMetric R M := {
  edist_eq0 : forall x y : M, edist (x, y) = 0 -> x = y
}.

HB.builders Context R M & PseudoMetric_isExtMetric R M.

Let hausdorffM : hausdorff_space M.
Proof. by move=> x y; rw -closeEnbhs => /edist_closeP /edist_eq0. Qed.

HB.instance Definition _ := Topological_isHausdorff.Build M hausdorffM.

HB.end.

Lemma edist_eq0 {R : realType} (M : extMetricType R) (x y : M) :
  edist (x, y) = 0 -> x = y.
Proof. by move=> /edist_closeP; rw closeEnbhs; exact: hausdorffT. Qed.

End move_to_urysohn.
Export move_to_urysohn.

Module move_to_hoelder.

Section minkowski2.
Context {R : realType}.
Local Open Scope ring_scope.

Import MeasurableR.

Let f2 (a b : R) (n : nat) : R := match n with 0%N => a | 1%N => b | _ => 0 end.

Let Lnorm_f2 (a b p : R) : 0 < p ->
  'N[counting]_p%:E[EFin \o f2 a b] = ((`|a| `^ p + `|b| `^ p) `^ p^-1)%:E.
Proof.
move=> p0; rw Lnorm_counting //.
rw (nneseries_split 0 2); first by move=> k; rw lee_fin powR_ge0.
rw ereal_series_cond eseries0 ?adde0.
  by move=> [//|] [//|n _]; rw /f2 /= normr0 powR0 // gt_eqF.
by rw big_mkord 2!big_ord_recr /= big_ord0 add0e -EFinD poweR_EFin.
Qed.

(* Minkowski's inequality for two-term sums, the analogue of [hoelder2]. *)
Lemma minkowski2 (a1 a2 b1 b2 p : R) :
  0 <= a1 -> 0 <= a2 -> 0 <= b1 -> 0 <= b2 -> 1 <= p ->
  ((a1 + b1) `^ p + (a2 + b2) `^ p) `^ p^-1 <=
  (a1 `^ p + a2 `^ p) `^ p^-1 + (b1 `^ p + b2 `^ p) `^ p^-1.
Proof.
move=> a10 a20 b10 b20 p1; have p0 : 0 < p := lt_le_trans ltr01 p1.
have mf a b : measurable_fun [set: nat] (f2 a b) by [].
have := minkowski_EFin counting (mf a1 a2) (mf b1 b2) p1.
have -> : (f2 a1 a2 \+ f2 b1 b2)%R = f2 (a1 + b1) (a2 + b2).
  by apply/funext => -[|[|n]] //=; rw addr0.
rw (Lnorm_f2 (a1 + b1) (a2 + b2) p0) (Lnorm_f2 a1 a2 p0) (Lnorm_f2 b1 b2 p0).
rw -EFinD lee_fin.
rw (ger0_norm (addr_ge0 a10 b10)) (ger0_norm (addr_ge0 a20 b20)).
by rw (ger0_norm a10) (ger0_norm a20) (ger0_norm b10) (ger0_norm b20).
Qed.

End minkowski2.

Section Lnorm_extras.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Import MeasurableR.
Implicit Types (f g : T -> \bar R).

Let measurable_pow (p : R) f : measurable_fun [set: T] f ->
  measurable_fun [set: T] (fun x => `|f x| `^ p).
Proof.
move=> mf.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x => x `^ p)) => //=.
  exact: (measurableT_comp (measurable_poweR _)).
exact: measurableT_comp.
Qed.

Lemma Lnorm_ae_eq (p : R) f g :
  measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  f = g %[ae mu] -> 'N[mu]_p%:E[f] = 'N[mu]_p%:E[g].
Proof.
move=> mf mg fg; rw unlock /=; congr (_ `^ _).
apply: ge0_ae_eq_integral => //; try exact: measurable_pow.
- by move=> x _; exact: poweR_ge0.
- by move=> x _; exact: poweR_ge0.
- by apply: filterS fg => x /= fxgx _; rw fxgx.
Qed.

Lemma le_Lnorm (p : R) f g : (0 <= p)%R ->
  measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  (forall x, `|f x| <= `|g x|) -> 'N[mu]_p%:E[f] <= 'N[mu]_p%:E[g].
Proof.
move=> p0 mf mg fg; rw unlock /=.
have ge0_in (x : \bar R) : 0 <= x -> x \in `[0, +oo].
  by move=> x0; rw in_itv /= x0 ?leey.
apply: gt0_ler_poweR; first by rw invr_ge0.
- by apply: ge0_in; apply: integral_ge0 => x _; exact: poweR_ge0.
- by apply: ge0_in; apply: integral_ge0 => x _; exact: poweR_ge0.
apply: ge0_le_integral => //; try exact: measurable_pow.
  by move=> x _; exact: poweR_ge0.
by move=> x _; apply: gt0_ler_poweR => //; apply: ge0_in; exact: abse_ge0.
Qed.

(* Minkowski's inequality for non-negative extended-real functions. *)
Lemma eminkowski_ge0 (p : R) f g : (1 <= p)%R ->
  measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  (forall x, 0 <= f x) -> (forall x, 0 <= g x) ->
  'N[mu]_p%:E[f \+ g] <= 'N[mu]_p%:E[f] + 'N[mu]_p%:E[g].
Proof.
move=> p1 mf mg f0 g0; have p0 : (0 < p)%R := lt_le_trans ltr01 p1.
have neNy h : 'N[mu]_p%:E[h] != -oo.
  by rw gt_eqF // (lt_le_trans ltNy0) // Lnorm_ge0.
have [Nfy|Nfn] := eqVneq 'N[mu]_p%:E[f] +oo.
  by rw Nfy addye ?leey.
have [Ngy|Ngn] := eqVneq 'N[mu]_p%:E[g] +oo.
  by rw Ngy addey ?leey.
have fin h : measurable_fun [set: T] h -> (forall x, 0 <= h x) ->
    'N[mu]_p%:E[h] != +oo -> {ae mu, forall x, h x \is a fin_num}.
  move=> mh h0 Nh.
  have hint : mu.-integrable [set: T] (fun x => `|h x| `^ p).
    apply/integrableP; split; first exact: measurable_pow.
    rw (eq_integral (fun x => `|h x| `^ p)).
      by move=> x _; rw gee0_abs // poweR_ge0.
    apply: (@lty_poweRy _ _ p^-1); first by rw invr_eq0 gt_eqF.
    by move: Nh; rw unlock /= ltey.
  apply: filterS (integrable_ae measurableT hint) => x /(_ I) /= hx.
  have hx' : `|h x| `^ p < +oo by rw -ge0_fin_numE // poweR_ge0.
  rw ge0_fin_numE // -[h x]gee0_abs //.
  exact: lty_poweRy (negbT (gt_eqF p0)) hx'.
pose f' x := fine (f x); pose g' x := fine (g x).
have mf' : measurable_fun [set: T] f'.
  exact: measurableT_comp (fine_measurable measurableT) mf.
have mg' : measurable_fun [set: T] g'.
  exact: measurableT_comp (fine_measurable measurableT) mg.
have mEf' : measurable_fun [set: T] (EFin \o f') by exact/measurable_EFinP.
have mEg' : measurable_fun [set: T] (EFin \o g') by exact/measurable_EFinP.
have mEfg' : measurable_fun [set: T] (EFin \o (f' \+ g')%R).
  by apply/measurable_EFinP; exact: measurable_funD.
have mfg : measurable_fun [set: T] (f \+ g) by exact: emeasurable_funD.
have ef : f = EFin \o f' %[ae mu].
  by apply: filterS (fin f mf f0 Nfn) => x fx _; rw /f' /= fineK.
have eg : g = EFin \o g' %[ae mu].
  by apply: filterS (fin g mg g0 Ngn) => x gx _; rw /g' /= fineK.
have efg : f \+ g = EFin \o (f' \+ g')%R %[ae mu].
  apply: filterS2 ef eg => x /= fx gx _.
  by rw (fx I) (gx I).
have -> : 'N[mu]_p%:E[f \+ g] = 'N[mu]_p%:E[EFin \o (f' \+ g')%R].
  exact: Lnorm_ae_eq mfg mEfg' efg.
have -> : 'N[mu]_p%:E[f] = 'N[mu]_p%:E[EFin \o f'].
  exact: Lnorm_ae_eq mf mEf' ef.
have -> : 'N[mu]_p%:E[g] = 'N[mu]_p%:E[EFin \o g'].
  exact: Lnorm_ae_eq mg mEg' eg.
exact: minkowski_EFin.
Qed.

End Lnorm_extras.

End move_to_hoelder.
Export move_to_hoelder.

Module move_to_lp_product.
(* Upstream: a new file on l^p products, after hoelder.v and urysohn.v. *)

Section lp_dist.
Context {R : realType}.
Implicit Types (p a b : \bar R).

Lemma itv_ge1e (p : {itv \bar R & `[1, +oo[}) : 1 <= p%:num.
Proof. by case: p => x /= /andP[_]; rw /= in_itv /= andbT. Qed.

(* The l^p combination of two extended reals (max for p = +oo). *)
Definition lp_dist p a b : \bar R :=
  match p with
  | r%:E => (a `^ r + b `^ r) `^ r^-1
  | _ => maxe a b
  end.

Lemma lp_distE (r : R) a b : lp_dist r%:E a b = (a `^ r + b `^ r) `^ r^-1.
Proof. by []. Qed.

Let neNy_ge0 (x : \bar R) : 0 <= x -> x != -oo.
Proof. by move=> x0; rw gt_eqF // (lt_le_trans _ x0) // ltNy0. Qed.

Lemma lp_distC p : commutative (lp_dist p).
Proof. by case: p => [r||] a b /=; [rw addeC | rw maxC | rw maxC]. Qed.

Lemma lp_dist_ge0 p a b : 0 <= a -> 0 <= b -> 0 <= lp_dist p a b.
Proof. by case: p => [r||] a0 b0 /=; rw ?poweR_ge0 // le_max a0. Qed.

Lemma lp_dist00 p : 1 <= p -> lp_dist p 0 0 = 0.
Proof.
case: p => [r||] p1; try by rw /= max_l.
have r0 : (r != 0)%R by rw gt_eqF // (lt_le_trans ltr01) // -lee_fin.
by rw lp_distE poweR0r // adde0 poweR0r // invr_eq0.
Qed.

Lemma lp_dist_le p a b a' b' : 1 <= p -> 0 <= a -> 0 <= b ->
  a <= a' -> b <= b' -> lp_dist p a b <= lp_dist p a' b'.
Proof.
case: p => [r||] p1 a0 b0 aa' bb' /=; last 2 first.
- by rw ge_max !le_max aa' bb' orbT.
- by rw ge_max !le_max aa' bb' orbT.
have r0 : (0 <= r)%R by rw -lee_fin (le_trans _ p1).
have ge0_in (x : \bar R) : 0 <= x -> x \in `[0, +oo].
  by move=> x0; rw in_itv /= x0 ?leey.
apply: gt0_ler_poweR; rw ?invr_ge0 ?ge0_in ?adde_ge0 ?poweR_ge0 //.
have a'0 := le_trans a0 aa'; have b'0 := le_trans b0 bb'.
by apply: leeD; apply: gt0_ler_poweR => //; exact: ge0_in.
Qed.

Let lp_dist_ye r b : (0 < r)%R -> 0 <= b -> lp_dist r%:E +oo b = +oo.
Proof.
move=> r0 b0; rw lp_distE poweRyr ?gt_eqF // addye ?neNy_ge0 ?poweR_ge0 //.
by rw poweRyr // invr_eq0 gt_eqF.
Qed.

(* Minkowski's inequality for the l^p combination of extended reals. *)
Lemma lp_dist_triangle p a b a' b' : 1 <= p ->
  0 <= a -> 0 <= b -> 0 <= a' -> 0 <= b' ->
  lp_dist p (a + a') (b + b') <= lp_dist p a b + lp_dist p a' b'.
Proof.
case: p => [r||] p1 a0 b0 a'0 b'0; last 2 first.
- by rw /= ge_max; apply/andP; split; apply: leeD; rw le_max lexx ?orbT.
- by rw /= ge_max; apply/andP; split; apply: leeD; rw le_max lexx ?orbT.
have r1 : (1 <= r)%R by rw -lee_fin.
have r0 : (0 < r)%R by rw (lt_le_trans ltr01).
have ge0 x y : 0 <= x -> 0 <= y -> 0 <= lp_dist r%:E x y by exact: lp_dist_ge0.
have ey x : 0 <= x -> lp_dist r%:E x +oo = +oo.
  by move=> x0; rw lp_distC lp_dist_ye.
move: a0 => /gee0P[->|[x x0 ->]].
  by rw [X in _ <= X + _]lp_dist_ye // [X in _ <= X]addye ?neNy_ge0 ?ge0 ?leey.
move: b0 => /gee0P[->|[y y0 ->]].
  by rw [X in _ <= X + _]ey // [X in _ <= X]addye ?neNy_ge0 ?ge0 ?leey.
move: a'0 => /gee0P[->|[x' x'0 ->]].
  by rw [X in _ <= _ + X]lp_dist_ye // [X in _ <= X]addey ?neNy_ge0 ?ge0 ?leey.
move: b'0 => /gee0P[->|[y' y'0 ->]].
  by rw [X in _ <= _ + X]ey // [X in _ <= X]addey ?neNy_ge0 ?ge0 ?leey.
rw !lp_distE -?EFinD ?poweR_EFin -?EFinD ?poweR_EFin -?EFinD lee_fin.
exact: minkowski2.
Qed.

Lemma lp_dist_eq0 p a b : 1 <= p -> 0 <= a -> 0 <= b ->
  lp_dist p a b = 0 -> a = 0 /\ b = 0.
Proof.
case: p => [r||] p1 a0 b0 /=; last 2 first.
- by move=> m0; split; apply/le_anti; rw ?a0 ?b0 andbT -m0 le_max lexx ?orbT.
- by move=> m0; split; apply/le_anti; rw ?a0 ?b0 andbT -m0 le_max lexx ?orbT.
move=> /(poweR_eq0_eq0 (adde_ge0 (poweR_ge0 _ _) (poweR_ge0 _ _))) /eqP.
rw padde_eq0 ?poweR_ge0 // !poweR_eq0 //.
by move=> /andP[/andP[/eqP -> _] /andP[/eqP -> _]].
Qed.

End lp_dist.

(* The l^p product of two pseudometric spaces.  It is a fresh type for each
   p, since [X * Y] already carries Analysis's max-distance pseudometric. *)
Definition lp_prod {R : realType} (p : {itv \bar R & `[1, +oo[})
  (X Y : pseudoMetricType R) : Type := (X * Y)%type.

Section lp_prod.
Context {R : realType} (p : {itv \bar R & `[1, +oo[}) (X Y : pseudoMetricType R).
Local Notation P := (lp_prod p X Y).

HB.instance Definition _ := Choice.on P.

Definition lp_prod_dist (u v : P) : \bar R :=
  lp_dist p%:num (edist (u.1, v.1)) (edist (u.2, v.2)).

Let p1 := itv_ge1e p.

Let lp_prod_dist_ge0 u v : 0 <= lp_prod_dist u v.
Proof. exact: lp_dist_ge0. Qed.

Let lp_prod_dist_xx : self_inverse 0 lp_prod_dist.
Proof. by move=> u; rw /lp_prod_dist !edist_refl lp_dist00. Qed.

Let lp_prod_distC : commutative lp_prod_dist.
Proof. by move=> u v; rw /lp_prod_dist edist_sym [edist (u.2, _)]edist_sym. Qed.

Let lp_prod_dist_triangle u v w :
  lp_prod_dist u w <= lp_prod_dist u v + lp_prod_dist v w.
Proof.
rw /lp_prod_dist; apply: le_trans (lp_dist_triangle _ _ _ _ _) => //.
by apply: lp_dist_le; rw ?edist_triangle.
Qed.

HB.instance Definition _ := isExtPseudoMetric.Build R P
  lp_prod_dist_ge0 lp_prod_dist_xx lp_prod_distC lp_prod_dist_triangle.

Lemma lp_prod_edistE (u v : P) :
  edist (u, v) = lp_dist p%:num (edist (u.1, v.1)) (edist (u.2, v.2)).
Proof. exact: (@edistE _ _ lp_prod_dist). Qed.

End lp_prod.

Section lp_prod_metric.
Context {R : realType} (p : {itv \bar R & `[1, +oo[}) (X Y : extMetricType R).

Let lp_prod_edist_eq0 (u v : lp_prod p X Y) : edist (u, v) = 0 -> u = v.
Proof.
rw lp_prod_edistE => /lp_dist_eq0[]; rw ?itv_ge1e ?edist_ge0 //.
by case: u v => [x1 y1] [x2 y2] /= /edist_eq0 -> /edist_eq0 ->.
Qed.

HB.instance Definition _ := PseudoMetric_isExtMetric.Build R (lp_prod p X Y)
  lp_prod_edist_eq0.

End lp_prod_metric.

End move_to_lp_product.
Export move_to_lp_product.

Module move_to_metric_measure.
(* Upstream: a new file relating pseudometric and measurable structures. *)

(* A measurable structure compatible with an extended pseudometric: the
   distance is measurable on the product.  This is what integrating
   distances against couplings or transport plans requires; in particular it
   holds for the Borel sigma-algebra of a separable space. *)
HB.mixin Record PseudoMetricMeasurable_isMetricMeasurable (R : realType) d M
    & PseudoMetric R M & Measurable d M := {
  measurable_edist : measurable_fun [set: M * M] (fun xy : M * M => edist xy)
}.

#[short(type="metricMeasurableType")]
HB.structure Definition MetricMeasurable (R : realType) d :=
  { M of PseudoMetric R M & Measurable d M
       & PseudoMetricMeasurable_isMetricMeasurable R d M }.

End move_to_metric_measure.
Export move_to_metric_measure.

Module move_to_probability.
(* Ported from math-comp/analysis#1177 "Giry monad for probabilities"
   (head 40d1b8562a952c31eb42600c7184e73d9b6fa608), targeting
   theories/probability.v; drop this module once the PR is merged. *)

(* a pker that takes a superfluous arg *)
Section pker_curry.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}.
Variable (f : R.-pker T ~> T1).

Definition pker_curry (_ : T) : T -> {measure set T1 -> \bar R} := f.

Let pker_curry_kernel (x : T) U :
  measurable U -> measurable_fun setT (pker_curry x ^~ U).
Proof. by move=> mU/=; exact/measurable_kernel. Qed.

HB.instance Definition _ (x : T) :=
  isKernel.Build _ _ T T1 R (pker_curry x) (pker_curry_kernel x).

Let pker_curryT x : forall x', pker_curry x x' setT = 1%E.
Proof. by move=> x'; rw /pker_curry prob_kernel. Qed.

HB.instance Definition _ (x : T) :=
  Kernel_isProbability.Build _ _ _ _ R (pker_curry x) (pker_curryT x).

End pker_curry.

(* a pker that forgets its first arg *)
Section pker_snd.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}
        d2 {T2 : measurableType d2}.
Variable (g : R.-pker T1 ~> T2).

Definition pker_snd : T * T1 -> {measure set T2 -> \bar R} := g \o snd.

Let pker_snd_kernel U : measurable U -> measurable_fun setT (pker_snd ^~ U).
Proof.
move=> mU /=.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x => g x U) _ snd) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R pker_snd pker_snd_kernel.

Let pker_sndT x : pker_snd x setT = 1%E.
Proof. by rw /pker_snd /= prob_kernel. Qed.

HB.instance Definition _ (x : T) :=
  Kernel_isProbability.Build _ _ _ _ R pker_snd pker_sndT.

End pker_snd.

Section giry_def.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType} d' {T' : measurableType d'}.

Definition ret : R.-pker T ~> T := kdirac (@measurable_id _ _ setT).

Variables (mu : probability T R) (f : R.-pker T ~> T').

Definition bind :=
  kcomp (kprobability (measurable_cst (mu : pprobability T R))) (pker_snd f) tt.

Lemma bindE A : bind A = \int[mu]_x f x A. Proof. by []. Qed.

HB.instance Definition _ := Measure.on bind.

Lemma bindT : bind setT = 1%E.
Proof.
rw bindE.
under eq_integral => x _ do rw prob_kernel.
by rw integral_cst // mul1e; exact: probability_setT.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ _ bind bindT.

End giry_def.

Section giry_prop.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}
        d2 {T2 : measurableType d2}.

Lemma giryretf (f : R.-pker T ~> T1) (x : T) A :
  measurable A -> bind (ret x) f A = f x A.
Proof.
move=> ?; rw bindE /ret/= integral_dirac ?diracT ?mul1e//.
exact: measurable_kernel.
Qed.

Lemma girymret (mu : probability T R) A :
  measurable A -> bind mu (@ret _ _ _) A = mu A.
Proof.
by move=> ?; rw bindE /ret/kdirac/= integral_indic// setIT.
Qed.

Variables (mu : probability T R) (f : R.-pker T ~> T1) (g : R.-pker T1 ~> T2).

Definition bindfg : T -> {measure set T2 -> \bar R} :=
  fun x => ((pker_curry f x) \; pker_snd g) x.

Let bindfg_kernel U : measurable U -> measurable_fun setT (bindfg ^~ U).
Proof.
move=> mU.
apply: (measurable_fun_integral_sfinite_kernel (pker_snd g ^~ U)) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R bindfg bindfg_kernel.

Let bindfgT x : bindfg x setT = 1.
Proof.
rw /bindfg /= /kcomp /=.
under eq_integral do rw prob_kernel.
by rw integral_cst// mul1e prob_kernel.
Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ R bindfg bindfgT.

Lemma giryA U : measurable U ->
  bind (bind mu f) g U = bind mu bindfg U.
Proof.
move=> mU.
rw !bindE.
have -> : bind mu f = kcomp (cst mu) (pker_snd f) tt by [].
have -> // := @integral_kcomp _ _ d1  _ T T1 R
  (kprobability (measurable_cst (mu : pprobability T R)))
  (pker_snd f) tt (g ^~ U).
exact/measurable_kernel.
Qed.

End giry_prop.

End move_to_probability.
Export move_to_probability.

(* Standard Borel spaces, aligned with standard_borel_wit of mathcomp-qbs
   (https://llm4rocq.github.io/mathcomp-qbs/, measure_qbs_adjunction.v):
   a measurable retraction (sb_encode, sb_decode) onto R. By Kuratowski this
   is equivalent to Klenke's Borel spaces [Klenke 2014, Def. 8.35]. *)
Module move_to_standard_borel.
Import MeasurableR.

HB.mixin Record Measurable_isStandardBorel (R : realType) d T
    & Measurable d T := {
  sb_encode : T -> R;
  sb_decode : R -> T;
  measurable_sb_encode : measurable_fun [set: T] sb_encode;
  measurable_sb_decode : measurable_fun [set: R] sb_decode;
  sb_retractK : cancel sb_encode sb_decode }.

#[short(type="standardBorelType")]
HB.structure Definition StandardBorel (R : realType) d :=
  { T of Measurable d T & Measurable_isStandardBorel R d T }.

Arguments sb_encode {R d s}.
Arguments sb_decode {R d s}.

Section standard_borel_lemmas.
Context {R : realType} {d} {T : standardBorelType R d}.

Lemma sb_encode_inj : injective (@sb_encode R d T).
Proof. exact: can_inj sb_retractK. Qed.

Lemma measurable_sb_image (A : set T) : measurable A ->
  measurable (sb_encode @` A : set R).
Proof.
move=> mA.
have -> : sb_encode @` A =
    ((fun r => sb_encode (sb_decode r : T)) \- id)%R @^-1` [set 0%R] `&`
    sb_decode @^-1` A.
  apply/seteqP; split => [r [t At <-]|r [/= /eqP]].
    by split => /=; rw sb_retractK // subrr.
  by rw subr_eq0 => /eqP rE Adr; exists (sb_decode r).
apply: measurableI.
  rw -[X in measurable X]setTI; apply: measurable_funB measurableT _ _ => //.
  exact: measurableT_comp measurable_sb_encode measurable_sb_decode.
by rw -[X in measurable X]setTI; exact: measurable_sb_decode.
Qed.

End standard_borel_lemmas.

Arguments measurable_sb_image {R d T} A.

End move_to_standard_borel.
Export move_to_standard_borel.

