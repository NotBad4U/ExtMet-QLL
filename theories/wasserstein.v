(* Wasserstein distances via transport plans given by probability kernels. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import constructive_ereal ereal topology_structure.
From mathcomp Require Import uniform_structure pseudometric_structure urysohn.
From mathcomp Require Import measure lebesgue_integral measurable_realfun exp.
From mathcomp Require Import numfun kernel lebesgue_stieltjes_measure hoelder.
From mathcomp Require Import bernoulli_distribution convex.
From ExtMetQLL Require Import analysis_extras extmet disintegration.

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
(*    is_coupling mu nu pi == pi has marginals mu and nu                      *)
(*         wass p mu nu == infimum over couplings; = wdir on standard Borel   *)
(*                         spaces (wassE), by disintegration                  *)
(*           wspace p X == W_p X, the pseudometric space of probabilities    *)
(*   pmap mu mf, pmix q mu nu == pushforward, convex combination              *)
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
Local Open Scope convex_scope.

(* TODO move to analysis_extras.v (move_to_probability) once stable. *)
Section kernel_extras.
Context {R : realType}.

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

(* TODO move to analysis_extras.v (move_to_measure_function). *)
Lemma prob_prod_ext {R : realType} {d1 d2} {X : measurableType d1}
    {Y : measurableType d2} (m1 m2 : probability (X * Y)%type R) :
  (forall A B, measurable A -> measurable B -> m1 (A `*` B) = m2 (A `*` B)) ->
  forall E, measurable E -> m1 E = m2 E.
Proof.
move=> m12 E; rw prod_measurable_rectangle => mE.
apply: (g_sigma_algebra_finite_measure_unique
  (G := rectangle measurable measurable)) => //.
- by move=> _ [A mA [B mB] <-]; exact: measurableX.
- by apply: setI_closed_rectangle => *; exact: measurableI.
- by rw -setXTT; exact: m12.
- by move=> _ [A mA [B mB] <-]; exact: m12.
Qed.

Section pmap.
Context {R : realType} {d d'} {X : measurableType d} {Y : measurableType d'}.

(* The image of a probability measure under a measurable map, as a bind. *)
Definition pmap (mu : probability X R) {f : X -> Y}
    (mf : measurable_fun [set: X] f) := bind mu (kdirac mf).

HB.instance Definition _ mu f (mf : measurable_fun [set: X] f) :=
  Probability.on (pmap mu mf).

Lemma pmapE mu f (mf : measurable_fun [set: X] f) A : measurable A ->
  (pmap mu mf : probability Y R) A = mu (f @^-1` A).
Proof.
move=> mA; transitivity (\int[mu]_x kdirac mf x A); first by [].
under eq_integral do rw /kdirac /= diracE.
rw -[X in mu X]setIT -integral_indic //.
  by rw -[X in measurable X]setTI; exact: (mf measurableT _ mA).
Qed.

Lemma integral_pmap mu f (mf : measurable_fun [set: X] f) (h : Y -> \bar R) :
  measurable_fun [set: Y] h -> (forall y, 0 <= h y) ->
  \int[pmap mu mf]_y h y = \int[mu]_x h (f x).
Proof.
move=> mh h0; rw integral_bind //; apply: eq_integral => x _.
by rw /kdirac /= integral_dirac //= diracT mul1e.
Qed.

End pmap.

(* The coupling of a transport plan: the law of (x, y), x ~ mu, y ~ k x. *)
Notation plan_coupling mu k := (bind mu (kgraph k)).

Section coupling.
Context {R : realType} {d d'} {X : measurableType d} {Y : measurableType d'}.
Implicit Types (mu : probability X R) (nu : probability Y R)
  (k : R.-pker X ~> Y).

Definition is_coupling mu nu (pi : probability (X * Y)%type R) :=
  (forall A, measurable A -> pi (A `*` setT) = mu A) /\
  (forall B, measurable B -> pi (setT `*` B) = nu B).

Lemma kgraphE k x (E : set (X * Y)) : measurable E ->
  kgraph k x E = k x (xsection E x).
Proof.
move=> mE; rw xsectionE /kgraph /= /kcomp.
under eq_integral do rw /kdirac /= diracE.
rw -[X in k x X]setIT -integral_indic //.
  by rw -[X in measurable X]setTI; apply: (pair1_measurable x).
Qed.

Lemma plan_couplingX mu k A B : measurable A -> measurable B ->
  plan_coupling mu k (A `*` B) = \int[mu]_(x in A) k x B.
Proof.
move=> mA mB; rw bindE [RHS]integral_mkcond.
apply: eq_integral => x _; rw kgraphE ?patchE; first exact: measurableX.
by case: ifPn => xA; [rw in_xsectionX|rw notin_xsectionX // measure0].
Qed.

Lemma is_coupling_plan mu nu k : is_plan mu nu k ->
  is_coupling mu nu (plan_coupling mu k).
Proof.
move=> kp; split => [A mA|B mB].
  transitivity (\int[mu]_(x in A) k x setT); first exact: plan_couplingX.
  rw (eq_integral (cst 1)) => [x _|]; first by rw prob_kernel.
  by rw integral_cst // mul1e.
transitivity (\int[mu]_(x in setT) k x B); first exact: plan_couplingX.
by rw kp // bindE.
Qed.

Lemma integral_plan_coupling mu k (h : X * Y -> \bar R) :
  measurable_fun [set: X * Y] h -> (forall z, 0 <= h z) ->
  \int[plan_coupling mu k]_z h z = \int[mu]_x \int[k x]_y h (x, y).
Proof.
move=> mh h0; rw integral_bind //; apply: eq_integral => x _.
exact: integral_kgraph.
Qed.

End coupling.

(* On standard Borel spaces every coupling is the coupling of a plan:
   disintegrate it along the first coordinate. *)
Section coupling_plan.
Context {R : realType} {d dT} {X : measurableType d}
  {Y : standardBorelType R dT}.
Variables (mu : probability X R) (nu : probability Y R).
Variable pi : probability (X * Y)%type R.
Hypothesis cpi : is_coupling mu nu pi.

Let pmargE A : measurable A -> pmarg pi A = mu A.
Proof. by move=> mA; rw /pmarg psliceE; exact: cpi.1. Qed.

Let int_marg (A : set X) (h : X -> \bar R) : measurable A ->
  \int[pmarg pi]_(x in A) h x = \int[mu]_(x in A) h x.
Proof. by move=> mA; apply: eq_measure_integral => B mB _; exact: pmargE. Qed.

Lemma is_plan_kborel : is_plan mu nu (kborel pi).
Proof.
move=> B mB; rw -cpi.2 // disintegration_borel // int_marg //.
Qed.

Lemma plan_coupling_kborel E : measurable E ->
  plan_coupling mu (kborel pi) E = pi E.
Proof.
apply: prob_prod_ext => A B mA mB.
transitivity (\int[mu]_(x in A) kborel pi x B); first exact: plan_couplingX.
by rw disintegration_borel // int_marg.
Qed.

End coupling_plan.

(* TODO move to analysis_extras.v (move_to_metric_measure). *)
#[short(type="metricBorelType")]
HB.structure Definition MetricBorel (R : realType) d :=
  { M of MetricMeasurable R d M & StandardBorel R d M }.

Section wasserstein_coupling.
Context {R : realType} {d} {X : metricMeasurableType R d}.
Implicit Types (p : {itv R & `[1, +oo[}) (mu nu : probability X R)
  (pi : probability (X * X)%type R).

Definition ccost p pi : \bar R :=
  (\int[pi]_z edist z `^ p%:num) `^ (p%:num)^-1.

(* The Wasserstein distance: infimum of the costs of the couplings. *)
Definition wass p mu nu : \bar R :=
  ereal_inf [set ccost p pi | pi in [set pi | is_coupling mu nu pi]].

Let medist_pow p : measurable_fun [set: X * X] (fun z => edist z `^ p%:num).
Proof. exact: measurableT_comp (measurable_poweR _) measurable_edist. Qed.

Lemma ccost_ge0 p pi : 0 <= ccost p pi.
Proof. exact: poweR_ge0. Qed.

Lemma wass_ge0 p mu nu : 0 <= wass p mu nu.
Proof. by apply: le_ereal_inf_tmp => _ [pi _ <-]; exact: ccost_ge0. Qed.

Lemma ccost_plan p mu (k : R.-pker X ~> X) :
  ccost p (plan_coupling mu k) = wcost p mu k.
Proof.
rw /ccost /wcost integral_plan_coupling //;
  by [move=> z; exact: poweR_ge0|exact: medist_pow].
Qed.

Lemma wass_le_wdir p mu nu : wass p mu nu <= wdir p mu nu.
Proof.
apply: le_ereal_inf_tmp => _ [k kp <-]; rw -ccost_plan.
by apply: ereal_inf_lbound; exists (plan_coupling mu k) => //;
  exact: is_coupling_plan.
Qed.

Lemma swapX {T1 T2 : Type} (A : set T1) (B : set T2) :
  (@unstable.swap T1 T2) @^-1` (B `*` A) = A `*` B.
Proof. by apply/seteqP; split => -[a b] /= [].
Qed.

Lemma wass_leC p mu nu : wass p mu nu <= wass p nu mu.
Proof.
apply: le_ereal_inf_tmp => _ [pi cpi <-].
pose pi' := pmap pi (@measurable_swap _ _ X X).
have cpi' : is_coupling mu nu pi'.
  split => [A mA|B mB].
  - by rw /pi' pmapE ?swapX; [exact: measurableX|exact: cpi.2].
  - by rw /pi' pmapE ?swapX; [exact: measurableX|exact: cpi.1].
apply: (@le_trans _ _ (ccost p pi')); first by apply: ereal_inf_lbound; exists pi'.
rw /ccost /pi' integral_pmap //;
  try by [move=> z; exact: poweR_ge0|exact: medist_pow].
rw (eq_integral (fun z => edist z `^ p%:num)) => [[x y] _|];
  [by rw /= edist_sym|exact: lexx].
Qed.

Lemma wassC p : commutative (wass p).
Proof. by move=> mu nu; apply/le_anti; rw !wass_leC. Qed.

End wasserstein_coupling.

Section wasserstein_borel.
Context {R : realType} {d} {X : metricBorelType R d}.
Implicit Types (p : {itv R & `[1, +oo[}) (mu nu rho : probability X R).

Lemma wdir_le_wass p mu nu : wdir p mu nu <= wass p mu nu.
Proof.
apply: le_ereal_inf_tmp => _ [pi cpi <-].
have -> : ccost p pi = wcost p mu (kborel pi).
  rw -ccost_plan /ccost; congr (_ `^ _).
  apply: eq_measure_integral => E mE _.
  exact/esym/(plan_coupling_kborel cpi).
by apply: ereal_inf_lbound; exists (kborel pi) => //; exact: is_plan_kborel.
Qed.

(* On standard Borel spaces, plans and couplings give the same distance. *)
Lemma wassE p mu nu : wass p mu nu = wdir p mu nu.
Proof. by apply/le_anti; rw wass_le_wdir wdir_le_wass. Qed.

Lemma wdistE p mu nu : wdist p mu nu = wass p mu nu.
Proof. by rw /wdist -!wassE (wassC p nu) maxxx. Qed.

Lemma wass_refl p mu : wass p mu mu = 0.
Proof. by rw wassE wdir_refl. Qed.

Lemma wass_triangle p mu nu rho :
  wass p mu rho <= wass p mu nu + wass p nu rho.
Proof. by rw !wassE; exact: wdir_triangle. Qed.

Lemma wass_ret p (x y : X) :
  wass p (\d_x : probability X R) (\d_y : probability X R) <= edist (x, y).
Proof. by rw wassE; exact: wdir_ret. Qed.

End wasserstein_borel.

(* Functoriality: pushforward along a measurable non-expansive map. *)
Section wasserstein_pushforward.
Context {R : realType} {d d'} {X : metricMeasurableType R d}
  {Y : metricMeasurableType R d'}.
Variables (f : X -> Y) (mf : measurable_fun [set: X] f).
Hypothesis f1 : forall x x', edist (f x, f x') <= edist (x, x').

Let ff (z : X * X) : Y * Y := (f z.1, f z.2).

Let mff : measurable_fun [set: X * X] ff.
Proof.
by apply: measurable_fun_pair; exact: measurableT_comp mf _.
Qed.

Lemma wass_pmap p (mu nu : probability X R) :
  wass p (pmap mu mf) (pmap nu mf) <= wass p mu nu.
Proof.
have p0 : (0 <= p%:num)%R by rw ge0.
apply: le_ereal_inf_tmp => _ [pi cpi <-].
pose pi' := pmap pi mff.
have ffX A B : ff @^-1` (A `*` B) = f @^-1` A `*` f @^-1` B by [].
have mpre (C : set Y) : measurable C -> measurable (f @^-1` C).
  by move=> mC; rw -[X in measurable X]setTI; apply: mf.
have cpi' : is_coupling (pmap mu mf) (pmap nu mf) pi'.
  split => [A mA|B mB].
  - transitivity (pi (f @^-1` A `*` setT)).
      by rw /pi' pmapE //; exact: measurableX.
    by rw cpi.1; [exact: mpre|rw pmapE].
  - transitivity (pi (setT `*` f @^-1` B)).
      by rw /pi' pmapE //; exact: measurableX.
    by rw cpi.2; [exact: mpre|rw pmapE].
apply: (@le_trans _ _ (ccost p pi')); first by apply: ereal_inf_lbound; exists pi'.
apply: gt0_ler_poweR; rw ?invr_ge0 ?in_itv /= ?leey ?andbT //;
  try by apply: integral_ge0 => z _; exact: poweR_ge0.
rw /pi' integral_pmap //;
  try by [move=> z; exact: poweR_ge0
         |exact: measurableT_comp (measurable_poweR _) measurable_edist].
apply: ge0_le_integral => //;
  first [by move=> z _; exact: poweR_ge0
        |exact: measurableT_comp (measurable_poweR _)
           (measurableT_comp measurable_edist mff)
        |exact: measurableT_comp (measurable_poweR _) measurable_edist
        |by move=> [x x'] _; apply: gt0_ler_poweR;
           rw ?in_itv /= ?leey ?andbT ?edist_ge0 //; exact: f1].
Qed.

End wasserstein_pushforward.


Lemma is_coupling_conv {R : realType} {d d'} {X : measurableType d}
    {Y : measurableType d'} (q : {i01 R})
    (mu mu' : probability X R) (nu nu' : probability Y R)
    (pi pi' : probability (X * Y)%type R) :
  is_coupling mu nu pi -> is_coupling mu' nu' pi' ->
  is_coupling (mu <| q |> mu') (nu <| q |> nu') (pi <| q |> pi').
Proof.
move=> c c'; split => [A mA|B mB]; rw !probability_convE !pmixE.
- by rw c.1 // c'.1.
- by rw c.2 // c'.2.
Qed.

(* TODO move to analysis_extras.v (move_to_ereal). *)
Section ereal_inf_add.
Context {R : realType}.
Implicit Types (S T : set \bar R) (c x : \bar R).

Lemma le_ereal_inf_addl S c x : 0 <= c -> (forall s, S s -> 0 <= s) ->
  (forall s, S s -> x <= c + s) -> x <= c + ereal_inf S.
Proof.
move=> c0 S0 h; have [->|cy] := eqVneq c +oo.
  by rw addye ?leey // gt_eqF // (lt_le_trans ltNy0) // le_ereal_inf_tmp.
have cf : c \is a fin_num by rw ge0_fin_numE // ltey.
by rw -leeBlDl //; apply: le_ereal_inf_tmp => s Ss; rw leeBlDl // h.
Qed.

(* Infimum of a sum of independent non-negative terms. *)
Lemma le_ereal_inf_add S T x :
  (forall s, S s -> 0 <= s) -> (forall t, T t -> 0 <= t) ->
  (forall s t, S s -> T t -> x <= s + t) -> x <= ereal_inf S + ereal_inf T.
Proof.
move=> S0 T0 h; apply: le_ereal_inf_addl => [|//|t Tt].
  exact: le_ereal_inf_tmp.
rw addeC; apply: le_ereal_inf_addl => [|//|s Ss]; first exact: T0.
by rw addeC; exact: h.
Qed.

End ereal_inf_add.

Section wasserstein_mix.
Context {R : realType} {d} {X : metricMeasurableType R d}.

Definition w1 : {itv R & `[1, +oo[} := widen_itv (1%R)%:itv.

Lemma ccost1 (pi : probability (X * X)%type R) :
  ccost w1 pi = \int[pi]_z edist z.
Proof.
rw /ccost /= invr1 poweRe1; first by apply: integral_ge0 => z _; exact: poweR_ge0.
by apply: eq_integral => z _; rw poweRe1 // edist_ge0.
Qed.

(* The convex combination is non-expansive p W1 (x) (1 - p) W1 -> W1. *)
Lemma wass_conv (q : {i01 R}) (mu mu' nu nu' : probability X R) :
  wass w1 (mu <| q |> mu') (nu <| q |> nu') <=
  q%:num%:E * wass w1 mu nu + (1 - q%:num)%R%:E * wass w1 mu' nu'.
Proof.
have [->|q0] := eqVneq q 0%R%:i01; first by rw !conv0 /= mul0e subr0 mul1e add0e.
have [->|q1] := eqVneq q 1%R%:i01; first by rw !conv1 /= mul1e subrr mul0e adde0.
have q0' : (0 < q%:num)%R by rw lt_neqAle eq_sym q0 ge0.
have q1' : (0 < 1 - q%:num)%R by rw subr_gt0 lt_neqAle q1 le1.
rw -!ereal_inf_pZl //; apply: le_ereal_inf_add.
- by move=> _ [_ [pi _ <-] <-]; apply: mule_ge0; [rw lee_fin ltW|exact: ccost_ge0].
- by move=> _ [_ [pi _ <-] <-]; apply: mule_ge0; [rw lee_fin ltW|exact: ccost_ge0].
move=> _ _ [_ [pi c <-] <-] [_ [pi' c' <-] <-].
apply: (@le_trans _ _ (ccost w1 (pi <| q |> pi'))).
  by apply: ereal_inf_lbound; exists (pi <| q |> pi') => //; exact: is_coupling_conv.
rw !ccost1 probability_convE integral_pmix //;
  by [exact: measurable_edist|move=> z; exact: edist_ge0].
Qed.

End wasserstein_mix.

(* Couplings only see measurable sets, so measures agreeing on them are at
   distance 0. *)
Section wass_congr.
Context {R : realType} {d} {X : metricMeasurableType R d}.
Implicit Types (p : {itv R & `[1, +oo[}) (mu nu : probability X R).

Lemma wass_congrl p mu mu' nu : (forall A, measurable A -> mu A = mu' A) ->
  wass p mu nu = wass p mu' nu.
Proof.
move=> e; rw /wass; congr ereal_inf; apply/seteqP; split => _ [pi c <-];
  exists pi => //; split => [A mA|]; rw ?c.1 ?e //; exact: c.2.
Qed.

End wass_congr.

(* W_p X: the probability measures on X with the Wasserstein distance. *)
Definition wspace {R : realType} (p : {itv R & `[1, +oo[}) {d}
  (X : metricBorelType R d) : Type := probability X R.

Section wspace_instances.
Context {R : realType} (p : {itv R & `[1, +oo[}) {d} {X : metricBorelType R d}.

HB.instance Definition _ := ConvexSpace.copy (wspace p X) (probability X R).
HB.instance Definition _ := isExtPseudoMetric.Build R (wspace p X)
  (@wass_ge0 _ _ X p) (@wass_refl _ _ X p) (@wassC _ _ X p)
  (@wass_triangle _ _ X p).

Lemma wspace_edistE (mu nu : wspace p X) : edist (mu, nu) = wass p mu nu.
Proof.
rw (@edistE _ (wspace p X) (wass p)) //; first exact: wass_ge0.
Qed.

End wspace_instances.

Section wasserstein_space.
Context {R : realType} (p : {itv R & `[1, +oo[}) {d} {X : metricBorelType R d}.

(* The unit of the monad. *)
Definition wret (x : X) : wspace p X := \d_x.

Lemma nonexpansive_wret : nonexpansive wret.
Proof. by apply/nonexpansiveP => x y; rw wspace_edistE; exact: wass_ret. Qed.

(* The action on maps. *)
Definition wmap {d'} {Y : metricBorelType R d'} (f : X -> Y)
    (mf : measurable_fun [set: X] f) (mu : wspace p X) : wspace p Y := pmap mu mf.

Lemma nonexpansive_wmap {d'} {Y : metricBorelType R d'} (f : X -> Y)
    (mf : measurable_fun [set: X] f) :
  nonexpansive f -> nonexpansive (wmap mf).
Proof.
move=> /nonexpansiveP f1; apply/nonexpansiveP => mu nu.
by rw !wspace_edistE; exact: wass_pmap.
Qed.

(* Points at distance 0: measures agreeing on measurable sets. *)
Lemma wspace_edist0 (mu nu : wspace p X) :
  (forall A, measurable A -> mu A = nu A) -> edist (mu, nu) = 0.
Proof.
by move=> e; rw wspace_edistE (wass_congrl _ _ e) wass_refl.
Qed.

End wasserstein_space.

(* The monad laws hold up to distance 0 (W_p X is a pseudometric space
   until measures are identified on the measurable sets). *)
Section wasserstein_monad_laws.
Context {R : realType} (p : {itv R & `[1, +oo[}) {d1 d2 d3}
  {X : metricBorelType R d1} {Y : metricBorelType R d2}
  {Z : metricBorelType R d3}.

(* The left unit law is giryretf: bind (ret x) f and f x agree on
   measurable sets ([f x] carries no probability instance to state it in
   W_p). *)
Lemma wbind_retr (mu : probability X R) :
  edist ((bind mu (@ret _ _ R) : wspace p X), (mu : wspace p X)) = 0.
Proof. by apply: wspace_edist0 => A mA; exact: girymret. Qed.

Lemma wbindA (mu : probability X R) (f : R.-pker X ~> Y) (g : R.-pker Y ~> Z) :
  edist ((bind (bind mu f) g : wspace p Z), (bind mu (bindfg f g) : wspace p Z)) = 0.
Proof. by apply: wspace_edist0 => A mA; exact: giryA. Qed.

End wasserstein_monad_laws.

(* Interpolative barycentric algebras [Mardare, Panangaden, Plotkin, Free
   complete Wasserstein algebras, LMCS 2018]: convex spaces whose convex
   combinations are non-expansive p X (x) (1 - p) X -> X.
   Interpolative convex algebras over finite distributions, with the
   Kantorovich lifting, are also formalized in rocq-quantitative-equational-
   reasoning (src/ICA.v, src/KantorovichProperties.v).
   TODO: completeness, and generalize to a library of metric convex spaces
   (cf. infotheo's convex.v, monae's convex monads). *)
HB.mixin Record PseudoMetricConvex_isIBAlgebra (R : realType) T
    & ConvexSpace R T & PseudoMetric R T := {
  edist_conv : forall (p : {i01 R}) (a b a' b' : T),
    edist (a <| p |> b, a' <| p |> b') <=
    p%:num%:E * edist (a, a') + (1 - p%:num)%R%:E * edist (b, b') }.

#[short(type="ibAlgebraType")]
HB.structure Definition IBAlgebra (R : realType) :=
  { T of ConvexSpace R T & PseudoMetric R T
       & PseudoMetricConvex_isIBAlgebra R T }.

(* W_1 X is an interpolative barycentric algebra. *)
Section wspace_ib.
Context {R : realType} {d} {X : metricBorelType R d}.

Let wspace_edist_conv (p : {i01 R}) (a b a' b' : wspace w1 X) :
  edist (a <| p |> b, a' <| p |> b') <=
  p%:num%:E * edist (a, a') + (1 - p%:num)%R%:E * edist (b, b').
Proof. by rw !wspace_edistE; exact: wass_conv. Qed.

HB.instance Definition _ :=
  PseudoMetricConvex_isIBAlgebra.Build R (wspace w1 X) wspace_edist_conv.

End wspace_ib.

(* The values of a probability kernel, as probability measures. *)
Section kval.
Context {R : realType} {d d'} {T : measurableType d} {X : measurableType d'}.
Variables (k : R.-pker T ~> X) (t : T).

Definition kval : set X -> \bar R := k t.

HB.instance Definition _ := Measure.on kval.
Let kvalT : kval setT = 1. Proof. by rw /kval prob_kernel. Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _ kval kvalT.

End kval.

(* Binding a probability kernel into couplings. *)
Section coupling_bind.
Context {R : realType} {dT d} {T : measurableType dT} {X : measurableType d}.
Variables (f g : R.-pker T ~> X) (gam : R.-pker T ~> (X * X)%type).
Hypothesis cgam : forall t, is_coupling (kval f t) (kval g t) (kval gam t).

Lemma is_coupling_bind (mu : probability T R) :
  is_coupling (bind mu f) (bind mu g) (bind mu gam).
Proof.
split => [A mA|B mB].
- transitivity (\int[mu]_t gam t (A `*` setT)); first by [].
  by apply: eq_integral => t _; exact: (cgam t).1.
- transitivity (\int[mu]_t gam t (setT `*` B)); first by [].
  by apply: eq_integral => t _; exact: (cgam t).2.
Qed.

End coupling_bind.

(* Bind is non-expansive in the kernel for the sup distance, given a
   measurable choice of optimal couplings.  Optimal couplings exist on Polish
   spaces and can be chosen measurably [Villani, Optimal Transport, Thm 4.1
   and Cor. 5.22]; neither result is available in Analysis. *)
Section wasserstein_bind.
Context {R : realType} {dT d} {T : measurableType dT}
  {X : metricMeasurableType R d}.
Variables (f g : R.-pker T ~> X).

Definition optimal_selection := exists gam : R.-pker T ~> (X * X)%type,
  forall t, is_coupling (kval f t) (kval g t) (kval gam t) /\
    ccost w1 (kval gam t) <= wass w1 (kval f t) (kval g t).

Hypothesis sel : optimal_selection.

Lemma wass_bind (mu : probability T R) :
  wass w1 (bind mu f) (bind mu g) <=
  ereal_sup [set wass w1 (kval f t) (kval g t) | t in setT].
Proof.
have [gam hgam] := sel; set S := ereal_sup _.
have [t0 _] : [set: T] !=set0.
  apply/set0P/negP => /eqP T0; have := probability_setT mu.
  by rw T0 measure0 => /eqP; rw eq_sym onee_eq0.
have S0 : 0 <= S.
  by apply: le_trans (wass_ge0 _ _ _) (ereal_sup_ubound _); exists t0.
apply: (@le_trans _ _ (ccost w1 (bind mu gam))).
  apply: ereal_inf_lbound; exists (bind mu gam) => //.
  by apply: is_coupling_bind => t; exact: (hgam t).1.
rw ccost1 integral_bind //;
  try by [exact: measurable_edist|move=> z; exact: edist_ge0].
apply: (@le_trans _ _ (\int[mu]_t S)).
  apply: ge0_le_integral => //;
    first [by move=> t _; apply: integral_ge0 => z _; exact: edist_ge0
          |by move=> t _; have := (hgam t).2; rw ccost1 => /le_trans; apply;
             apply: ereal_sup_ubound; exists t
          |apply: (measurable_fun_integral_sfinite_kernel
             (fun tz : T * (X * X) => edist tz.2)) => //;
           by [move=> z; exact: edist_ge0
              |exact: measurableT_comp measurable_edist measurable_snd]].
by rw integral_cst // [X in _ * X](@probability_setT _ _ _ mu) mule1.
Qed.

End wasserstein_bind.

