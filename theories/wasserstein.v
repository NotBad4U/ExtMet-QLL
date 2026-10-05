(* Wasserstein distances via transport plans given by probability kernels. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import constructive_ereal ereal topology_structure.
From mathcomp Require Import uniform_structure pseudometric_structure urysohn.
From mathcomp Require Import measure lebesgue_integral measurable_realfun exp.
From mathcomp Require Import numfun kernel lebesgue_stieltjes_measure hoelder.
From ExtMetQLL Require Import analysis_extras.

(**md**************************************************************************)
(* # Wasserstein distances                                                    *)
(*                                                                            *)
(* Transport plans are probability kernels rather than couplings: a plan     *)
(* from mu to nu is a probability kernel k with nu = \int[mu]_x k x.  The     *)
(* cost is an iterated integral, so no product measure and no disintegration *)
(* is needed, and plans compose by kernel composition (the triangle          *)
(* inequality).  This mirrors the use of s-finite kernels for the semantics  *)
(* of probabilistic programs.  The resulting directed distance is            *)
(* symmetrized by a max; on standard Borel spaces, where couplings           *)
(* disintegrate, it coincides with the usual coupling definition.            *)
(*                                                                            *)
(* ```                                                                        *)
(*     is_plan mu nu k == the probability kernel k transports mu onto nu      *)
(*       wcost p mu k == (\int[mu]_x \int[k x]_y edist (x, y)^p)^(1/p)        *)
(*         wdir p mu nu == infimum of the costs of the plans from mu to nu    *)
(*        wdist p mu nu == max (wdir p mu nu) (wdir p nu mu)                  *)
(*                 kid == the identity plan, kdirac of the identity           *)
(* ```                                                                        *)
(* Here p : {itv R & `[1, +oo[} is a real exponent.                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO move to analysis_extras.v (move_to_probability) once stable. *)
Section kernel_extras.
Context {R : realType}.

Lemma integral_bind {d d'} {X : measurableType d} {Y : measurableType d'}
    (mu : probability X R) (k : R.-pker X ~> Y) (h : Y -> \bar R) :
  measurable_fun [set: Y] h -> (forall y, 0 <= h y) ->
  \int[bind mu k]_y h y = \int[mu]_x \int[k x]_y h y.
Proof.
move=> mh h0.
exact: (@integral_kcomp _ _ _ _ _ _ R
  (kprobability (measurable_cst (mu : pprobability X R))) (pker_snd k) tt h).
Qed.

Lemma integral_bindfg {d1 d2 d3} {X : measurableType d1}
    {Y : measurableType d2} {Z : measurableType d3}
    (f : R.-pker X ~> Y) (g : R.-pker Y ~> Z) x (h : Z -> \bar R) :
  measurable_fun [set: Z] h -> (forall z, 0 <= h z) ->
  \int[bindfg f g x]_z h z = \int[f x]_y \int[g y]_z h z.
Proof.
move=> mh h0.
exact: (@integral_kcomp _ _ _ _ _ _ R (pker_curry f x) (pker_snd g) x h).
Qed.

(* The graph of a probability kernel: kgraph k x is the law of (x, y) for
   y distributed as k x. *)
Section kgraph.
Context {d d'} {X : measurableType d} {Y : measurableType d'}.
Variable k : R.-pker X ~> Y.

Definition kgraph : X -> {measure set (X * Y) -> \bar R} :=
  mkcomp k (kdirac (@measurable_id _ (X * Y)%type setT)).

HB.instance Definition _ := SFiniteKernel.on kgraph.

Let kgraphT x : kgraph x setT = 1.
Proof.
rw /kgraph /= /kcomp.
under eq_integral => y _ do rw /kdirac /= diracT.
by rw integral_cst // mul1e prob_kernel.
Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ R kgraph kgraphT.

Lemma integral_kgraph x (h : X * Y -> \bar R) :
  measurable_fun [set: X * Y] h -> (forall z, 0 <= h z) ->
  \int[kgraph x]_z h z = \int[k x]_y h (x, y).
Proof.
move=> mh h0; rw /kgraph integral_kcomp //.
by apply: eq_integral => y _; rw /kdirac integral_dirac //= diracT mul1e.
Qed.

End kgraph.

End kernel_extras.

Section plan.
Context {R : realType} {d d'} {X : measurableType d} {Y : measurableType d'}.

(* A transport plan from mu to nu: a probability kernel pushing mu onto nu. *)
Definition is_plan (mu : probability X R) (nu : probability Y R)
    (k : R.-pker X ~> Y) :=
  forall A, measurable A -> nu A = bind mu k A.

(* Integrating against the target of a plan. *)
Lemma plan_integral (mu : probability X R) (nu : probability Y R)
    (k : R.-pker X ~> Y) (h : Y -> \bar R) :
  is_plan mu nu k -> measurable_fun [set: Y] h -> (forall y, 0 <= h y) ->
  \int[nu]_y h y = \int[mu]_x \int[k x]_y h y.
Proof.
move=> kp mh h0; rw (eq_measure_integral (bind mu k)).
  by move=> A mA _; exact: kp.
exact: integral_bind.
Qed.

End plan.

(* Plans compose by Kleisli composition of probability kernels. *)
Lemma is_plan_comp {R : realType} {d1 d2 d3} {X : measurableType d1}
    {Y : measurableType d2} {Z : measurableType d3}
    (mu : probability X R) (nu : probability Y R) (rho : probability Z R)
    (f : R.-pker X ~> Y) (g : R.-pker Y ~> Z) :
  is_plan mu nu f -> is_plan nu rho g -> is_plan mu rho (bindfg f g).
Proof.
move=> pf pg A mA; rw pg // -(giryA mu f g mA) !bindE.
by apply: eq_measure_integral => B mB _; exact: pf.
Qed.

Section identity_plan.
Context {R : realType} {d} {X : measurableType d}.

Definition kid : R.-pker X ~> X := kdirac (@measurable_id _ X [set: X]).

Lemma is_plan_id (mu : probability X R) : is_plan mu mu kid.
Proof.
by move=> A mA; rw (girymret mu mA).
Qed.

End identity_plan.

Section wasserstein.
Context {R : realType} {d} {X : metricMeasurableType R d}.
Implicit Types (p : {itv R & `[1, +oo[}) (mu nu : probability X R).

Definition wcost p mu (k : X -> {measure set X -> \bar R}) : \bar R :=
  (\int[mu]_x \int[k x]_y edist (x, y) `^ p%:num) `^ (p%:num)^-1.

Definition wdir p mu nu : \bar R :=
  ereal_inf [set wcost p mu k | k in [set k : R.-pker X ~> X | is_plan mu nu k]].

Definition wdist p mu nu : \bar R := maxe (wdir p mu nu) (wdir p nu mu).

Lemma wcost_ge0 p mu k : 0 <= wcost p mu k.
Proof. exact: poweR_ge0. Qed.

Lemma wdir_ge0 p mu nu : 0 <= wdir p mu nu.
Proof. by apply: le_ereal_inf_tmp => _ [k _ <-]; exact: wcost_ge0. Qed.

Lemma wdist_ge0 p mu nu : 0 <= wdist p mu nu.
Proof. by rw /wdist le_max wdir_ge0. Qed.

Lemma wdistC p : commutative (wdist p).
Proof. by move=> mu nu; rw /wdist maxC. Qed.

Lemma wcost_id p mu : wcost p mu kid = 0.
Proof.
have p0 : (p%:num != 0)%R by rw gt_eqF.
rw /wcost (_ : \int[mu]_x _ = 0) ?poweR0r ?invr_eq0 //.
transitivity (\int[mu]_x cst 0 x); last exact: integral0.
apply: eq_integral => x _ /=.
have mf : measurable_fun [set: X]
    ((poweR ^~ p%:num) \o ((fun xy : X * X => edist xy) \o pair x)).
  exact: measurableT_comp (measurable_poweR _)
    (measurableT_comp measurable_edist (pair1_measurable x)).
by rw /kid /kdirac integral_dirac //= ?diracT ?mul1e /= ?edist_refl ?poweR0r.
Qed.

Lemma wdir_refl p mu : wdir p mu mu = 0.
Proof.
apply/le_anti; rw wdir_ge0 andbT -(wcost_id p mu).
by apply: ereal_inf_lbound; exists kid => //; exact: is_plan_id.
Qed.

Lemma wdist_refl p mu : wdist p mu mu = 0.
Proof. by rw /wdist wdir_refl max_l. Qed.

Lemma itv_ge1 p : (1 <= p%:num)%R.
Proof. by case: p => x /= /andP[_]; rw /= in_itv /= andbT. Qed.

Let mdist (dT : measure_display) (T : measurableType dT) (f g : T -> X) :
  measurable_fun [set: T] f -> measurable_fun [set: T] g ->
  measurable_fun [set: T] (fun t => edist (f t, g t)).
Proof.
move=> mf mg.
exact: (measurableT_comp measurable_edist (measurable_fun_pair mf mg)).
Qed.

Let mpow (dT : measure_display) (T : measurableType dT) (r : R)
    (h : T -> \bar R) :
  measurable_fun [set: T] h -> measurable_fun [set: T] (fun t => h t `^ r).
Proof. by move=> mh; exact: (measurableT_comp (measurable_poweR r) mh). Qed.

(* Costs add up along composed plans (Minkowski on the joint law of the two
   steps). *)
Lemma wcost_comp p mu nu (f g : R.-pker X ~> X) :
  is_plan mu nu f -> wcost p mu (bindfg f g) <= wcost p mu f + wcost p nu g.
Proof.
move=> pf; have p0 : (0 < p%:num)%R by [].
pose L := bind mu (kgraph (bindfg f (kgraph g))).
have m1 : measurable_fun [set: X * (X * X)] (fun u => u.1) by exact: measurable_fst.
have m21 : measurable_fun [set: X * (X * X)] (fun u => u.2.1).
  exact: (measurableT_comp measurable_fst measurable_snd).
have m22 : measurable_fun [set: X * (X * X)] (fun u => u.2.2).
  exact: (measurableT_comp measurable_snd measurable_snd).
pose F (u : X * (X * X)) := edist (u.1, u.2.1).
pose G (u : X * (X * X)) := edist (u.2.1, u.2.2).
pose H (u : X * (X * X)) := edist (u.1, u.2.2).
have mF : measurable_fun [set: X * (X * X)] F by exact: mdist.
have mG : measurable_fun [set: X * (X * X)] G by exact: mdist.
have mH : measurable_fun [set: X * (X * X)] H by exact: mdist.
have F0 u : 0 <= F u by exact: edist_ge0.
have G0 u : 0 <= G u by exact: edist_ge0.
have H0 u : 0 <= H u by exact: edist_ge0.
have intL (h : X * (X * X) -> \bar R) :
    measurable_fun [set: X * (X * X)] h -> (forall u, 0 <= h u) ->
    \int[L]_u h u = \int[mu]_x \int[f x]_y \int[g y]_z h (x, (y, z)).
  move=> mh h0; rw integral_bind //; apply: eq_integral => x _.
  have mhx : measurable_fun [set: X * X] (fun w => h (x, w)).
    exact: (measurableT_comp mh (pair1_measurable x)).
  have hx0 w : 0 <= h (x, w) by [].
  rw integral_kgraph // integral_bindfg //.
  apply: eq_integral => y _.
  have mhxy : measurable_fun [set: X * X] (fun w => h (x, w)) by [].
  by rw (@integral_kgraph _ _ _ _ _ g y (fun w => h (x, w))).
have NL (h : X * (X * X) -> \bar R) :
    measurable_fun [set: X * (X * X)] h -> (forall u, 0 <= h u) ->
    'N[L]_(p%:num)%:E[h] =
    (\int[mu]_x \int[f x]_y \int[g y]_z h (x, (y, z)) `^ p%:num)
      `^ (p%:num)^-1.
  move=> mh h0; rw unlock /=; congr (_ `^ _).
  rw (eq_integral (fun u => h u `^ p%:num)).
    by move=> u _; rw gee0_abs.
  by apply: intL; [exact: mpow | move=> u; exact: poweR_ge0].
have E1 : wcost p mu (bindfg f g) = 'N[L]_(p%:num)%:E[H].
  rw NL // /wcost; congr (_ `^ _); apply: eq_integral => x _.
  rw integral_bindfg //; first exact: mpow (mdist _ _).
  by move=> z; exact: poweR_ge0.
have E2 : wcost p mu f = 'N[L]_(p%:num)%:E[F].
  rw NL // /wcost; congr (_ `^ _); apply: eq_integral => x _.
  apply: eq_integral => y _.
  by rw /F /= integral_cst // prob_kernel mule1.
have E3 : wcost p nu g = 'N[L]_(p%:num)%:E[G].
  rw NL // /wcost; congr (_ `^ _); rw (plan_integral pf) //.
    apply: (measurable_fun_integral_sfinite_kernel
      (fun yz : X * X => edist yz `^ p%:num)) => //.
      by move=> yz; exact: poweR_ge0.
    exact: mpow measurable_edist.
  by move=> y; apply: integral_ge0 => z _; exact: poweR_ge0.
rw E1 E2 E3.
apply: (@le_trans _ _ ('N[L]_(p%:num)%:E[F \+ G])).
  apply: (@le_Lnorm _ _ _ L (p%:num) H (F \+ G) (ltW p0) mH
    (emeasurable_funD mF mG)) => u.
  rw !gee0_abs ?adde_ge0 //; exact: edist_triangle.
by apply: eminkowski_ge0 => //; exact: itv_ge1.
Qed.

(* The triangle inequality for the directed distance. *)
Lemma wdir_triangle p mu nu rho : wdir p mu rho <= wdir p mu nu + wdir p nu rho.
Proof.
apply/lee_addgt0Pr => e e0.
have [Ay|An] := eqVneq (wdir p mu nu) +oo.
  by rw Ay addye ?addye ?leey // gt_eqF // (lt_le_trans ltNy0) // wdir_ge0.
have [By|Bn] := eqVneq (wdir p nu rho) +oo.
  by rw By addey ?addye ?leey // gt_eqF // (lt_le_trans ltNy0) // wdir_ge0.
have Afin : wdir p mu nu \is a fin_num by rw ge0_fin_numE ?wdir_ge0 // ltey.
have Bfin : wdir p nu rho \is a fin_num by rw ge0_fin_numE ?wdir_ge0 // ltey.
have e20 : (0 < e / 2)%R by rw divr_gt0.
have [_ [f pf <-] fA] : exists2 y,
    [set wcost p mu k | k in [set k : R.-pker X ~> X | is_plan mu nu k]] y &
    y < wdir p mu nu + (e / 2)%:E.
  by apply: ereal_inf_lt; rw lteDl // lte_fin.
have [_ [g pg <-] gB] : exists2 y,
    [set wcost p nu k | k in [set k : R.-pker X ~> X | is_plan nu rho k]] y &
    y < wdir p nu rho + (e / 2)%:E.
  by apply: ereal_inf_lt; rw lteDl // lte_fin.
apply: (@le_trans _ _ (wcost p mu (bindfg f g))).
  by apply: ereal_inf_lbound; exists (bindfg f g) => //; exact: is_plan_comp pf pg.
apply: (le_trans (@wcost_comp p mu nu f g pf)).
rw [X in _ <= X](_ : _ = (wdir p mu nu + (e / 2)%:E) + (wdir p nu rho + (e / 2)%:E)).
  by rw addeACA -EFinD -splitr.
by apply: leeD; exact: ltW.
Qed.

(* The unit of the monad, x |-> \d_x, is non-expansive. *)
Lemma wdir_ret p (x y : X) :
  wdir p (\d_x : probability X R) (\d_y : probability X R) <= edist (x, y).
Proof.
have p0 : (p%:num != 0)%R by rw gt_eqF.
pose k : R.-pker X ~> X := kdirac (@measurable_cst _ _ X X setT y).
have kp : is_plan \d_x \d_y k.
  by move=> A mA; rw bindE integral_dirac //= ?diracT ?mul1e.
apply: (@le_trans _ _ (wcost p \d_x k)).
  by apply: ereal_inf_lbound; exists k.
have mx' (x' : X) : measurable_fun [set: X] (fun y' => edist (x', y') `^ p%:num).
  by apply: mpow; apply: mdist => //; exact: measurable_cst.
have my : measurable_fun [set: X] (fun x' => edist (x', y) `^ p%:num).
  by apply: mpow; apply: mdist => //; exact: measurable_cst.
rw /wcost (eq_integral (fun x' => edist (x', y) `^ p%:num)).
  by move=> x' _; rw /k /kdirac integral_dirac //= diracT mul1e.
by rw integral_dirac //= diracT mul1e -poweRrM mulfV // poweRe1.
Qed.

Lemma wdist_ret p (x y : X) :
  wdist p (\d_x : probability X R) (\d_y : probability X R) <= edist (x, y).
Proof. by rw /wdist ge_max wdir_ret /= edist_sym wdir_ret. Qed.

Lemma wdist_triangle p mu nu rho :
  wdist p mu rho <= wdist p mu nu + wdist p nu rho.
Proof.
rw /wdist ge_max; apply/andP; split.
- apply: le_trans (wdir_triangle p mu nu rho) _.
  by apply: leeD; rw le_max lexx.
- apply: le_trans (wdir_triangle p rho nu mu) _.
  by rw addeC; apply: leeD; rw le_max lexx ?orbT.
Qed.

End wasserstein.
