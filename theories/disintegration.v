(* Disintegration of probability measures on X * R (towards standard Borel
   spaces).  Meant to be upstreamed to MathComp Analysis as a new file. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean rat.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import constructive_ereal ereal topology_structure.
From mathcomp Require Import measure lebesgue_integral measurable_realfun.
From mathcomp Require Import lebesgue_stieltjes_measure charge radon_nikodym.
From mathcomp Require Import topology normedtype sequences numfun kernel.
From ExtMetQLL Require Import analysis_extras.

(**md**************************************************************************)
(* # Disintegration                                                           *)
(*                                                                            *)
(* Reference: A. Klenke, Probability Theory: A Comprehensive Course, 2nd ed., *)
(* Springer 2014, Sect. 8.3.  We prove (the product-space form of) Thm 8.29  *)
(* (regular conditional distributions in R) following the structure of its   *)
(* proof, with these differences: versions are Radon-Nikodym derivatives     *)
(* w.r.t. the marginal instead of conditional expectations; the null sets    *)
(* (8.12) for right-continuity at rationals are not used, the identity being *)
(* proved at every real t by dominated convergence along rationals q > t;    *)
(* the limits (8.13) are obtained from continuity of measures; the pi-system *)
(* is ]t, +oo[ (t real) instead of (-oo, r] (r rational).  The extension to  *)
(* standard Borel spaces (standardBorelType, as in mathcomp-qbs) is Thm 8.37.*)
(*                                                                            *)
(* Let pi be a probability measure on X * R.  For every rational q, the       *)
(* measure A |-> pi (A `*` `]-oo, q]) is absolutely continuous w.r.t. the     *)
(* first marginal of pi; its Radon-Nikodym derivative is a version of the     *)
(* conditional distribution function at q.  Regularizing these versions on a  *)
(* null set and taking Lebesgue-Stieltjes measures yields a probability       *)
(* kernel kappa with pi (A `*` B) = \int[marginal]_(x in A) kappa x B.        *)
(*                                                                            *)
(* ```                                                                        *)
(*        pslice pi mB == the measure A |-> pi (A `*` B) for measurable B     *)
(*          pmarg pi == the first marginal of pi, A |-> pi (A `*` setT)       *)
(*          cdfq pi q == Radon-Nikodym derivative of A |-> pi (A `*` ]-oo,q]) *)
(*                       w.r.t. pmarg pi                                      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* [mB] is an argument so that the measure instances below, whose proofs
   need it, are keyed on [pslice pi mB]. *)
Definition pslice {d d'} {X : measurableType d} {Y : measurableType d'}
    {R : realType} (pi : probability (X * Y)%type R) {B : set Y}
    (mB : measurable B) (A : set X) := pi (A `*` B).

(* TODO move to analysis_extras.v (classical_sets): no setX_bigcap. *)
Lemma setX_bigcapr {T1 T2 : Type} (A : set T1) (F : nat -> set T2) :
  A `*` \bigcap_n F n = \bigcap_n (A `*` F n).
Proof.
apply/seteqP; split => [[a b] /= [Aa Fb] n _|[a b] /= h].
  by split => //; exact: Fb.
by split; [exact: (h 0%N I).1|move=> n _; exact: (h n I).2].
Qed.

(* TODO move to analysis_extras.v (move_to_lebesgue_integrable): the
   inequality version of the private lemma integral_measure_lt used to prove
   integral_ae_eq. *)
Section integral_le_ae.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Lemma integral_measure_le (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x <= \int[mu]_(x in E) g x) ->
  mu (D `&` [set x | g x < f x]) = 0.
Proof.
move=> itf itg fg; pose E j := D `&` [set x | f x - g x >= j.+1%:R^-1%:E].
have msf := measurable_int _ itf.
have msg := measurable_int _ itg.
have mE j : measurable (E j).
  rewrite /E; apply: measurable_lee => //.
  by apply/(emeasurable_funD msf)/measurableT_comp => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite -measure_le0.
  have fg0 : \int[mu]_(x in E j) (f \- g) x <= 0.
    rewrite integralB//.
    - by apply: integrableS itf => //; exact: subIsetl.
    - by apply: integrableS itg => //; exact: subIsetl.
    rewrite sube_le0; apply: fg => //; exact: subIsetl.
  suff : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    by move=> /le_trans; apply; rewrite mule_ge0_le0.
  apply: (@le_trans _ _ (j.+1%:R%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)).
    by rewrite integral_cst// muleA -EFinM divff// mul1e.
  rewrite lee_pmul//; first exact: integral_ge0.
  apply: ge0_le_integral => //; last by move=> x [].
  apply: emeasurable_funB.
  - by apply: measurable_funS msf => //; exact: subIsetl.
  - by apply: measurable_funS msg => //; exact: subIsetl.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x [Dx /= ifg]; split => //.
  by move: ifg; apply: le_trans; rewrite lee_fin lef_pV2// ?posrE// ler_nat.
rewrite set_lte_bigcup.
have /cvg_lim h1 : (mu \o E) x @[x --> \oo]--> 0.
  by apply: cvg_near_cst; exact: nearW.
have := @nondecreasing_cvg_measure _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
by move/cvg_lim => h2; rewrite setI_bigcupr -h2// h1.
Qed.

Lemma integral_le_ae (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x <= \int[mu]_(x in E) g x) ->
  {ae mu, forall x, D x -> f x <= g x}.
Proof.
move=> itf itg fg; exists (D `&` [set x | g x < f x]); split.
- apply: measurable_lte => //; [exact: measurable_int itg|exact: measurable_int itf].
- exact: integral_measure_le.
- by move=> x /= /not_implyP[Dx /negP]; rewrite -ltNge.
Qed.

End integral_le_ae.

Section slice.
Context {d d'} {X : measurableType d} {Y : measurableType d'} {R : realType}.
Variable pi : probability (X * Y)%type R.
Variables (B : set Y) (mB : measurable B).
Local Notation pslice := (pslice pi mB).

Let pslice0 : pslice set0 = 0.
Proof. by rw /pslice set0X measure0. Qed.

Let pslice_ge0 A : 0 <= pslice A.
Proof. exact: measure_ge0. Qed.

Let pslice_sigma_additive : semi_sigma_additive pslice.
Proof.
move=> F mF tF mUF; rw /pslice setX_bigcupl.
apply: measure_semi_sigma_additive.
- by move=> n; exact: measurableX.
- move/trivIsetP : tF => tF; apply/trivIsetP => i j _ _ ij /=.
  by rw -setXI (tF i j) // set0X.
- by rw -setX_bigcupl; exact: measurableX.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ pslice
  pslice0 pslice_ge0 pslice_sigma_additive.

Let pslice_fin : fin_num_fun pslice.
Proof.
move=> A mA; rw ge0_fin_numE ?measure_ge0 //.
apply: (le_lt_trans (probability_le1 pi _)); last by rw ltry.
exact: measurableX.
Qed.

HB.instance Definition _ := Measure_isFinite.Build _ _ _ pslice pslice_fin.

Lemma psliceE A : pslice A = pi (A `*` B). Proof. by []. Qed.

End slice.

Section marginal.
Context {d d'} {X : measurableType d} {Y : measurableType d'} {R : realType}.
Variable pi : probability (X * Y)%type R.

Definition pmarg := pslice pi (@measurableT _ Y).

HB.instance Definition _ := FiniteMeasure.on pmarg.

Let pmargT : pmarg setT = 1.
Proof. by rw /pmarg psliceE setXTT probability_setT. Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _ pmarg pmargT.

Lemma pslice_le_marg (B : set Y) (mB : measurable B) A : measurable A ->
  pslice pi mB A <= pmarg A.
Proof.
move=> mA; rw !psliceE; apply: le_measure; rw ?inE; try exact: measurableX.
by apply: setSX.
Qed.

Lemma pslice_dominates (B : set Y) (mB : measurable B) :
  charge_of_finite_measure (pslice pi mB) `<< pmarg.
Proof.
apply/null_content_dominatesP => A mA A0; apply/eqP.
by rw eq_le measure_ge0 andbT -A0; exact: pslice_le_marg.
Qed.

End marginal.

Section conditional_cdf.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.

(* A version of the conditional distribution function at q. *)
Definition cdfq (q : R) : X -> \bar R :=
  Radon_Nikodym
    (charge_of_finite_measure (pslice pi (measurable_itv `]-oo, q])))
    (pmarg pi).

Lemma cdfq_integral q A : measurable A ->
  pi (A `*` `]-oo, q]) = \int[pmarg pi]_(x in A) cdfq q x.
Proof.
move=> mA; rw -(psliceE pi (measurable_itv `]-oo, q])).
have := Radon_Nikodym_integral (pslice_dominates (pi := pi) (measurable_itv `]-oo, q])) mA.
exact.
Qed.

Lemma cdfq_integrable q : (pmarg pi).-integrable [set: X] (cdfq q).
Proof. exact/Radon_Nikodym_integrable/pslice_dominates. Qed.

(* q |-> cdfq q x is a.e. non-decreasing ... *)
Lemma cdfq_le_ae q q' : (q <= q')%R ->
  {ae pmarg pi, forall x, [set: X] x -> cdfq q x <= cdfq q' x}.
Proof.
move=> qq'; apply: integral_le_ae => //; try exact: cdfq_integrable.
move=> E _ mE; rw -!cdfq_integral //.
apply: le_measure; rw ?inE; try exact: measurableX.
apply: setSX => // r /=; rw !in_itv /= => /le_trans; exact.
Qed.

(* ... non-negative ... *)
Lemma cdfq_ge0_ae q : {ae pmarg pi, forall x, [set: X] x -> 0 <= cdfq q x}.
Proof.
apply: (@integral_le_ae _ _ _ _ _ measurableT _ (cst 0)).
- exact: integrable0.
- exact: cdfq_integrable.
- by move=> E _ mE; rw integral0 -cdfq_integral // measure_ge0.
Qed.

(* ... and bounded by 1. *)
Lemma cdfq_le1_ae q : {ae pmarg pi, forall x, [set: X] x -> cdfq q x <= 1}.
Proof.
apply: (@integral_le_ae _ _ _ _ _ measurableT (cst 1)).
- exact: cdfq_integrable.
- exact: (finite_measure_integrable_cst _ 1%R measurableT).
- move=> E _ mE; rw -cdfq_integral // integral_cst // mul1e.
  rw [leRHS](_ : _ = pi (E `*` setT)) //.
  apply: le_measure; rw ?inE; try exact: measurableX.
  exact: setSX.
Qed.

Let bigcup_itvNyn : \bigcup_n `]-oo, n%:R]%classic = [set: R].
Proof.
rw -subTset => x _ /=; exists (Num.bound `|x|) => //=.
rw in_itv /=; apply: (le_trans (ler_norm x)); apply/ltW.
exact: archi_boundP (normr_ge0 x).
Qed.

Lemma cdfq_measurable q : measurable_fun [set: X] (cdfq q).
Proof. exact: measurable_int (cdfq_integrable q). Qed.

Let esups0_ge (u : (\bar R)^nat) m : u m <= esups u 0%N.
Proof. by apply: ereal_sup_ubound; exists m. Qed.

(* sup_n cdfq n x = 1 a.e. (given cdfq_le1_ae) *)
Lemma cdfq_sup_ge1_ae :
  {ae pmarg pi, forall x, 1 <= esups (fun n => cdfq n%:R x) 0%N}.
Proof.
pose S x := esups (fun n => cdfq n%:R x) 0%N.
have mS : measurable_fun [set: X] S.
  exact: (measurable_fun_esups (fun n => cdfq_measurable n%:R)).
pose c k : R := (1 - k.+1%:R^-1)%R.
pose E k := [set x | S x <= (c k)%:E].
have mE k : measurable (E k).
  by rw -[E k]setTI; apply: measurable_lee => //; exact: measurable_cst.
have muE k : pmarg pi (E k) = 0.
  have bnd m : pi (E k `*` `]-oo, m%:R]) <= (c k)%:E * pmarg pi (E k).
    rw cdfq_integral // -integral_cst //.
    apply: le_integral.
    - exact: mE.
    - exact: (integrableS measurableT (mE k) (@subsetT _ _) (cdfq_integrable _)).
    - exact: finite_measure_integrable_cst.
    - by move=> x; rw inE => Ex; apply: le_trans (esups0_ge _ m) Ex.
  have lim : (fun m => pi (E k `*` `]-oo, m%:R])) @ \oo -->
      pmarg pi (E k).
    rw /pmarg psliceE -bigcup_itvNyn setX_bigcupr.
    apply: (@nondecreasing_cvg_measure _ _ _ pi
      (fun m : nat => E k `*` `]-oo, m%:R]%classic)).
    - by move=> m; apply: measurableX => //; exact: measurable_itv.
    - by rw -setX_bigcupr bigcup_itvNyn; exact: measurableX.
    - move=> m n mn; apply/subsetPset; apply: setSX => // r /=.
      by rw !in_itv /= => /le_trans; apply; rw ler_nat.
  have le : pmarg pi (E k) <= (c k)%:E * pmarg pi (E k).
    rw -[X in X <= _](cvg_lim _ lim) //; apply: lime_le; first exact: cvgP lim.
    by apply: nearW => m; exact: bnd.
  have c1 : (c k < 1)%R by rw /c ltrBlDr ltrDl invr_gt0.
  apply/eqP; rw eq_le measure_ge0 andbT; move: le.
  have [->|E0] := eqVneq (pmarg pi (E k)) 0; first by [].
  have Efin : pmarg pi (E k) \is a fin_num by exact: fin_num_measure.
  rw -{1}(mul1e (pmarg pi (E k))) lee_pmul2r //.
    by rw lt0e E0 measure_ge0.
  by rw lee_fin leNgt c1.
apply: filterS (ae_foralln (fun k => _ : {ae pmarg pi, forall x, ~ E k x}))
  => [x xE|k].
  apply/lee_subgt0Pr => e e0.
  have [k ke] : exists k, (k.+1%:R^-1 < e)%R.
    exists (truncn e^-1); rw -ltf_pV2 ?posrE ?invr_gt0 // invrK.
    exact: truncnS_gt.
  have /negP := xE k; rw /E /= -ltNge => /ltW; apply: le_trans.
  by rw -EFinB lee_fin /c lerB // ltW.
by exists (E k); split => // x /= /contrapT.
Qed.

Let bigcap_itvNyNn : \bigcap_n `]-oo, (- n%:R)%R]%classic = set0 :> set R.
Proof.
rw -subset0 => x /(_ (Num.bound `|x|) I) /=.
rw in_itv /= lerNr => xb.
have := archi_boundP (normr_ge0 x); rw ltNge => /negP; apply.
apply: (le_trans xb); rw -[X in (_ <= X)%R]normrN; exact: ler_norm.
Qed.

Let einfs0_le (u : (\bar R)^nat) m : einfs u 0%N <= u m.
Proof. by apply: ereal_inf_lbound; exists m. Qed.

(* inf_n cdfq (-n) x = 0 a.e. (given cdfq_ge0_ae) *)
Lemma cdfq_inf_le0_ae :
  {ae pmarg pi, forall x, einfs (fun n => cdfq (- n%:R)%R x) 0%N <= 0}.
Proof.
pose I x := einfs (fun n => cdfq (- n%:R)%R x) 0%N.
have mI : measurable_fun [set: X] I.
  exact: (measurable_fun_einfs (fun n => cdfq_measurable (- n%:R))).
pose c k : R := (k.+1%:R^-1)%R.
pose E k := [set x | (c k)%:E <= I x].
have mE k : measurable (E k).
  by rw -[E k]setTI; apply: measurable_lee => //; exact: measurable_cst.
have muE k : pmarg pi (E k) = 0.
  have bnd m : (c k)%:E * pmarg pi (E k) <= pi (E k `*` `]-oo, (- m%:R)%R]).
    rw cdfq_integral // -integral_cst //.
    apply: le_integral.
    - exact: mE.
    - exact: finite_measure_integrable_cst.
    - exact: (integrableS measurableT (mE k) (@subsetT _ _) (cdfq_integrable _)).
    - by move=> x; rw inE => Ex; apply: le_trans Ex (einfs0_le _ m).
  have lim : (fun m => pi (E k `*` `]-oo, (- m%:R)%R])) @ \oo --> 0.
    have -> : 0 = pi (\bigcap_m (E k `*` `]-oo, (- m%:R)%R]%classic)).
      by rw -setX_bigcapr bigcap_itvNyNn setX0 measure0.
    apply: (@nonincreasing_cvg_measure _ _ _ pi
      (fun m : nat => E k `*` `]-oo, (- m%:R)%R]%classic)).
    - by rw (le_lt_trans (probability_le1 pi _)) ?ltry //; exact: measurableX.
    - by move=> m; apply: measurableX => //; exact: measurable_itv.
    - by rw -setX_bigcapr bigcap_itvNyNn setX0.
    - move=> m n mn; apply/subsetPset; apply: setSX => // r /=.
      by rw !in_itv /= => /le_trans; apply; rw lerN2 ler_nat.
  have le : (c k)%:E * pmarg pi (E k) <= 0.
    rw -[X in _ <= X](cvg_lim _ lim) //; apply: lime_ge; first exact: cvgP lim.
    by apply: nearW => m; exact: bnd.
  apply/eqP; rw eq_le measure_ge0 andbT; move: le.
  by rw pmule_rle0 // lte_fin invr_gt0.
apply: filterS (ae_foralln (fun k => _ : {ae pmarg pi, forall x, ~ E k x}))
  => [x xE|k].
  apply/lee_addgt0Pr => e e0; rw add0e.
  have [k ke] : exists k, (k.+1%:R^-1 < e)%R.
    exists (truncn e^-1); rw -ltf_pV2 ?posrE ?invr_gt0 // invrK.
    exact: truncnS_gt.
  have /negP := xE k; rw /E /= -ltNge => /ltW /le_trans; apply.
  by rw lee_fin ltW.
by exists (E k); split => // x /= /contrapT.
Qed.

End conditional_cdf.

(* TODO move to analysis_extras.v (measure_negligible): ae_foralln for any
   countable index type. *)
Lemma ae_forall_count {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) {I : countType} (P : I -> T -> Prop) :
  (forall i, {ae mu, forall x, P i x}) -> {ae mu, forall x, forall i, P i x}.
Proof.
move=> h.
have : {ae mu, forall x, forall n,
    if unpickle n is Some i then P i x else True}.
  apply: ae_foralln => n; case: (unpickle n) => [i|]; first exact: h.
  exact: aeW.
by apply: filterS => x Hx i; move: (Hx (pickle i)); rw pickleK.
Qed.

Section good_set.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Local Notation mu := (pmarg pi).
Local Notation F := (cdfq pi).

(* The points where all the a.e. properties of the cdfq hold at once on the
   rationals. *)
Definition good x : Prop :=
  [/\ forall q q' : rat, (q <= q')%R -> F (ratr q) x <= F (ratr q') x,
      forall q : rat, 0 <= F (ratr q) x /\ F (ratr q) x <= 1,
      1 <= esups (fun n => F n%:R x) 0%N &
      einfs (fun n => F (- n%:R)%R x) 0%N <= 0].

Lemma good_ae : {ae mu, forall x, good x}.
Proof.
have h1 : {ae mu, forall x, forall qq : rat * rat, (qq.1 <= qq.2)%R ->
    F (ratr qq.1) x <= F (ratr qq.2) x}.
  apply: ae_forall_count => -[q q'] /=.
  have [qq'|_] := leP q q'.
    have rq : (ratr q <= ratr q' :> R)%R by rw ler_rat.
    by apply: filterS (cdfq_le_ae pi rq) => x /(_ I) h _.
  by apply: aeW => x; rw leNgt; move/negP.
have h2 : {ae mu, forall x, forall q : rat,
    0 <= F (ratr q) x /\ F (ratr q) x <= 1}.
  apply: ae_forall_count => q.
  apply: filterS (filterI (cdfq_ge0_ae pi (ratr q)) (cdfq_le1_ae pi (ratr q))).
  by move=> x [/(_ I) a0 /(_ I) a1].
apply: filterS (filterI (filterI h1 h2)
  (filterI (cdfq_sup_ge1_ae pi) (cdfq_inf_le0_ae pi))).
move=> x [[a b] [c e]]; split => //.
by move=> q q' qq'; exact: (a (q, q')).
Qed.

Lemma exists_good : exists x, good x.
Proof.
apply/not_existsP => /= ng; have [N [mN N0 sN]] := good_ae.
have : mu N = 1.
  apply/eqP; rw eq_le probability_le1 //=.
  rw -(probability_setT mu); apply: le_measure; rw ?inE //.
  by move=> x _; apply: sN => /=; exact: ng.
by rw N0 => /eqP; rw lt_eqF // lte01.
Qed.

End good_set.

Section regular_cdf.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Local Notation F := (cdfq pi).

(* the infimum of the cdfq over the rationals above t *)
Definition rcdf (x : X) (t : R) : \bar R :=
  ereal_inf [set F (ratr q) x | q in [set q : rat | (t < ratr q)%R]].

Lemma exists_rat_gt (t : R) : exists q : rat, (t < ratr q)%R.
Proof.
exists (Num.bound `|t|)%:R; rw ratr_nat.
apply: (le_lt_trans (ler_norm t)); exact: archi_boundP (normr_ge0 t).
Qed.

Section good_point.
Variables (x : X) (gx : good pi x).

Lemma rcdf_ge0 t : 0 <= rcdf x t.
Proof.
apply: le_ereal_inf_tmp => _ [q _ <-].
by case: gx => _ /(_ q)[].
Qed.

Lemma rcdf_le_cdfq t (q : rat) : (t < ratr q)%R -> rcdf x t <= F (ratr q) x.
Proof. by move=> tq; apply: ereal_inf_lbound; exists q. Qed.

Lemma rcdf_le1 t : rcdf x t <= 1.
Proof.
have [q tq] := exists_rat_gt t.
apply: le_trans (rcdf_le_cdfq tq) _.
by case: gx => _ /(_ q)[].
Qed.

Lemma cdfq_le_rcdf (q : rat) t : (ratr q <= t)%R -> F (ratr q) x <= rcdf x t.
Proof.
move=> qt; apply: le_ereal_inf_tmp => _ [q' tq' <-].
case: gx => mono _ _ _; apply: mono.
by rw -(ler_rat R); apply: (le_trans qt); exact: ltW.
Qed.

Lemma rcdf_nd : {homo rcdf x : s t / (s <= t)%R >-> s <= t}.
Proof.
move=> s t st; apply: le_ereal_inf_tmp => _ [q tq <-].
by apply: ereal_inf_lbound; exists q => //; exact: (le_lt_trans st).
Qed.

Lemma rcdf_fin_num t : rcdf x t \is a fin_num.
Proof.
by rw ge0_fin_numE ?rcdf_ge0 // (le_lt_trans (rcdf_le1 t)) // ltry.
Qed.

End good_point.

(* A fixed good point, used outside the good set. *)
Definition good0 : X := projT1 (cid (exists_good pi)).

Lemma good_good0 : good pi good0.
Proof. exact: projT2 (cid (exists_good pi)). Qed.

Definition gpick (x : X) : X :=
  if pselect (good pi x) is left _ then x else good0.

Lemma good_gpick x : good pi (gpick x).
Proof. by rw /gpick; case: pselect => // _; exact: good_good0. Qed.

Lemma gpick_good x : good pi x -> gpick x = x.
Proof. by rw /gpick; case: pselect. Qed.

(* The regular conditional distribution function. *)
Definition regcdf (x : X) (t : R) : R := fine (rcdf (gpick x) t).

Lemma regcdfE x t : (regcdf x t)%:E = rcdf (gpick x) t.
Proof. by rw fineK //; exact: rcdf_fin_num (good_gpick x) t. Qed.

Lemma regcdf_ge0 x t : (0 <= regcdf x t)%R.
Proof. by rw -lee_fin regcdfE; exact: rcdf_ge0 (good_gpick x) t. Qed.

Lemma regcdf_le1 x t : (regcdf x t <= 1)%R.
Proof. by rw -lee_fin regcdfE; exact: rcdf_le1 (good_gpick x) t. Qed.

Lemma regcdf_nd x : nondecreasing (regcdf x).
Proof.
by move=> s t st; rw -lee_fin !regcdfE; exact: rcdf_nd.
Qed.

Lemma regcdf_rc x : right_continuous (regcdf x).
Proof.
move=> a; apply/cvgrPdist_lt => e e0.
have gg := good_gpick x.
have [_ [q aq <-] qe] : exists2 y,
    [set F (ratr q) (gpick x) | q in [set q : rat | (a < ratr q)%R]] y &
    y < rcdf (gpick x) a + e%:E.
  by apply: ereal_inf_lt; rw lteDl ?rcdf_fin_num // lte_fin.
near=> s.
have a_s : (a < s)%R by near: s; exact: nbhs_right_gt.
have sq : (s < ratr q)%R by near: s; exact: nbhs_right_lt.
have fas : (regcdf x a <= regcdf x s)%R by exact: regcdf_nd (ltW a_s).
rw distrC ger0_norm ?subr_ge0 // ltrBlDl -lte_fin EFinD !regcdfE.
exact: le_lt_trans (rcdf_le_cdfq _ sq) qe.
Unshelve. all: by end_near.
Qed.

Lemma regcdf_y1 x : (regcdf x @ +oo --> (1:R))%R.
Proof.
apply/cvgrPdist_lt => e e0.
have gg := good_gpick x.
have [n Fn] : exists n : nat, (1 - e)%:E < F n%:R (gpick x).
  case: (gg) => _ _ sup1 _.
  have : (1 - e)%:E < esups (fun n => F n%:R (gpick x)) 0%N.
    by apply: lt_le_trans sup1; rw lte_fin ltrBlDr ltrDl.
  by move=> /ereal_sup_gt[_ [n _ <-] h]; exists n.
near=> s.
have ns : (n%:R <= s)%R by near: s; apply: nbhs_pinfty_ge; exact: num_real.
have := cdfq_le_rcdf gg (q := n%:R) (t := s); rw ratr_nat => /(_ ns) Fs.
rw ger0_norm ?subr_ge0 ?regcdf_le1 // ltrBlDl -ltrBlDr -lte_fin regcdfE.
exact: lt_le_trans Fn Fs.
Unshelve. all: by end_near.
Qed.

Lemma regcdf_Ny0 x : (regcdf x @ -oo --> (0:R))%R.
Proof.
apply/cvgrPdist_lt => e e0.
have gg := good_gpick x.
have [n Fn] : exists n : nat, F (- n%:R)%R (gpick x) < e%:E.
  case: (gg) => _ _ _ inf0.
  have : einfs (fun n => F (- n%:R)%R (gpick x)) 0%N < e%:E.
    by apply: le_lt_trans inf0 _; rw lte_fin.
  by move=> /ereal_inf_lt[_ [n _ <-] h]; exists n.
near=> s.
have sn : (s < - n%:R)%R by near: s; apply: nbhs_ninfty_lt; exact: num_real.
have := rcdf_le_cdfq (gpick x) (q := - n%:R) (t := s).
rw rmorphN /= ratr_nat => /(_ sn) Fs.
rw sub0r normrN ger0_norm ?regcdf_ge0 // -lte_fin regcdfE.
exact: le_lt_trans Fs Fn.
Unshelve. all: by end_near.
Qed.

HB.instance Definition _ x := isCumulative.Build R _ R (regcdf x)
  (@regcdf_nd x) (@regcdf_rc x).

HB.instance Definition _ (x : X) :=
  isCumulativeBounded.Build R (0:R)%R (1:R)%R (regcdf x)
    (@regcdf_Ny0 x) (@regcdf_y1 x).

End regular_cdf.

Section measurability.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Local Notation F := (cdfq pi).

Definition goodset : set X := [set x | good pi x].

Let mF q : measurable_fun [set: X] (F q).
Proof. exact: cdfq_measurable. Qed.

Lemma measurable_goodset : measurable goodset.
Proof.
pose P1 n : set X := if (unpickle n : option (rat * rat)) is Some qq then
  (if (qq.1 <= qq.2)%R then [set x | F (ratr qq.1) x <= F (ratr qq.2) x]
   else setT) else setT.
pose P2 n : set X := if (unpickle n : option rat) is Some q then
  [set x | 0 <= F (ratr q) x] `&` [set x | F (ratr q) x <= 1] else setT.
pose S x := esups (fun n => F n%:R x) 0%N.
pose Inf x := einfs (fun n => F (- n%:R)%R x) 0%N.
have -> : goodset = \bigcap_n P1 n `&` \bigcap_n P2 n `&`
    [set x | 1 <= S x] `&` [set x | Inf x <= 0].
  apply/seteqP; split => [x [h1 h2 h3 h4]|x [[[h1 h2] h3] h4]].
    split => //; split => //; split => [n _|n _]; rw /P1 /P2.
    - case: (unpickle n) => // -[q q'] /=; case: ifP => // qq'.
      exact: h1.
    - by case: (unpickle n) => // q; have [] := h2 q.
  split => //.
  - move=> q q' qq'; have := h1 (pickle (q, q')) I.
    by rw /P1 pickleK /= qq'.
  - by move=> q; have := h2 (pickle q) I; rw /P2 pickleK => -[].
apply: measurableI; last first.
  rw -[X in measurable X]setTI; apply: measurable_lee => //.
  exact: (measurable_fun_einfs (fun n => mF (- n%:R)%R) 0%N).
apply: measurableI; last first.
  rw -[X in measurable X]setTI; apply: measurable_lee => //.
  exact: (measurable_fun_esups (fun n => mF n%:R) 0%N).
apply: measurableI; apply: bigcapT_measurable => n.
- rw /P1; case: (unpickle n) => // -[q q'] /=; case: ifP => // _.
  by rw -[X in measurable X]setTI; apply: measurable_lee.
- rw /P2; case: (unpickle n) => // q.
  apply: measurableI; rw -[X in measurable X]setTI; apply: measurable_lee => //;
    exact: measurable_cst.
Qed.

(* rcdf as a countable infimum over an enumeration of the rationals *)
Lemma rcdf_einfs x t : rcdf pi x t = einfs (fun n =>
  if (unpickle n : option rat) is Some q then
    (if (t < ratr q)%R then F (ratr q) x else +oo)
  else +oo) 0%N.
Proof.
apply/le_anti/andP; split.
  apply: le_ereal_inf_tmp => _ [n _ <-] /=.
  case: (unpickle n) => [q|]; last exact: leey.
  case: ifP => tq; last exact: leey.
  by apply: ereal_inf_lbound; exists q.
apply: le_ereal_inf_tmp => _ [q tq <-].
by apply: ereal_inf_lbound; exists (pickle q) => //=; rw pickleK tq.
Qed.

Lemma measurable_rcdf t : measurable_fun [set: X] (fun x => rcdf pi x t).
Proof.
pose G n x := if (unpickle n : option rat) is Some q then
    (if (t < ratr q)%R then F (ratr q) x else +oo) else +oo.
have mG n : measurable_fun [set: X] (G n).
  unfold G; case: (unpickle n) => [q|]; last exact: measurable_cst.
  by case: (t < ratr q)%R; [exact: mF|exact: measurable_cst].
have -> : (fun x => rcdf pi x t) = (fun x => einfs (G ^~ x) 0%N).
  by apply/funext => x; exact: rcdf_einfs.
exact: (measurable_fun_einfs mG 0%N).
Qed.

Lemma measurable_regcdf t : measurable_fun [set: X] (fun x => regcdf pi x t).
Proof.
pose c := regcdf pi (good0 pi) t.
have -> : (fun x => regcdf pi x t) = (fun x =>
    \1_goodset x * fine (rcdf pi x t) + (1 - \1_goodset x) * c)%R.
  apply/funext => x; rw /regcdf /c /gpick indicE.
  case: pselect => gx; first by rw mem_set // mul1r subrr mul0r addr0.
  rw memNset // mul0r add0r subr0 mul1r.
  by rw /regcdf gpick_good //; exact: good_good0.
apply: measurable_funD; apply: measurable_funM.
- exact: measurable_indic measurable_goodset.
- exact: measurableT_comp (fine_measurable measurableT) (measurable_rcdf t).
- apply: measurable_funB; first exact: measurable_cst.
  exact: measurable_indic measurable_goodset.
- exact: measurable_cst.
Qed.

End measurability.

Section kappa.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.

(* The disintegrating kernel: Lebesgue-Stieltjes measures of the regular
   conditional distribution functions. *)
Definition kappa (x : X) := lebesgue_stieltjes_measure (regcdf pi x).

HB.instance Definition _ x := Measure.on (kappa x).

Lemma kappa_ocitv x (a b : R) : (a <= b)%R ->
  kappa x `]a, b] = (regcdf pi x b - regcdf pi x a)%:E.
Proof.
move=> ab; rw /kappa /lebesgue_stieltjes_measure /measure_extension /=.
by rw measurable_mu_extE /= ?wlength_itv_bnd //; exact: is_ocitv.
Qed.

Lemma kappa_itvNy x (t : R) : kappa x `]-oo, t] = (regcdf pi x t)%:E.
Proof.
rw itvNybndEbigcup.
have h1 : kappa x `](- n%:R)%R, t] @[n --> \oo] --> (regcdf pi x t)%:E.
  suff : ((regcdf pi x t)%:E - (regcdf pi x (- n%:R)%R)%:E) @[n --> \oo] -->
      (regcdf pi x t)%:E.
    apply: cvg_trans; apply: near_eq_cvg; near=> n.
    rw kappa_ocitv // lerNl; near: n; exact: nbhs_infty_ger.
  rw -[X in _ --> X](sube0 (regcdf pi x t)%:E); apply: cvgeB => //.
  apply: (cvg_comp _ _ (cvg_comp _ _ _ (cumulativeNy (regcdf pi x)))) => //.
  by apply: (cvg_comp _ _ cvgr_idn); rw ninfty.
have h2 : kappa x `](- n%:R)%R, t] @[n --> \oo] -->
    kappa x (\bigcup_n `](- n%:R)%R, t]%classic).
  apply: nondecreasing_cvg_measure => //; first exact: bigcup_measurable.
  by move=> *; apply/subsetPset/subset_itv; rw leBSide //= lerN2 ler_nat.
exact: cvg_unique h2 h1.
Unshelve. all: by end_near.
Qed.

Let kappaT x : kappa x setT = 1.
Proof.
have h1 : kappa x `]-oo, n%:R] @[n --> \oo] --> 1.
  under eq_fun do rw kappa_itvNy.
  apply/fine_cvgP; split; first exact: nearW.
  rw /comp /=; apply: (cvg_comp _ _ cvgr_idn) => //.
  exact: (cumulativey (regcdf pi x)).
have h2 : kappa x `]-oo, n%:R] @[n --> \oo] -->
    kappa x (\bigcup_n `]-oo, n%:R]%classic).
  apply: nondecreasing_cvg_measure => //; first exact: bigcup_measurable.
  move=> m n mn; apply/subsetPset => r /=; rw !in_itv /= => /le_trans; apply.
  by rw ler_nat.
have -> : [set: R] = \bigcup_n `]-oo, n%:R]%classic.
  rw eqEsubset; split => // r _ /=; exists (Num.bound `|r|) => //=.
  rw in_itv /=; apply: (le_trans (ler_norm r)); apply/ltW.
  exact: archi_boundP (normr_ge0 r).
exact: cvg_unique h2 h1.
Qed.

HB.instance Definition _ x :=
  @Measure_isProbability.Build _ _ _ (kappa x) (kappaT x).

Lemma kappa_itvoy x t : kappa x `]t, +oo[ = (1 - regcdf pi x t)%:E.
Proof.
have -> : `]t, +oo[%classic = ~` `]-oo, t]%classic.
  apply/seteqP; split => r /=; rw !in_itv /= ?andbT.
    by move=> tr; apply/negP; rw -ltNge.
  by move/negP; rw -ltNge.
by rw probability_setC // EFinB; congr (_ - _); exact: kappa_itvNy.
Qed.

Lemma measurable_kappa (B : set R) : measurable B ->
  measurable_fun [set: X] (fun x => kappa x B).
Proof.
move=> mB.
pose H := [set B : set R |
  measurable B /\ measurable_fun [set: X] (fun x => kappa x B)].
have GH : (@RGenOInfty.G R) `<=` H.
  move=> _ [t ->]; split; first exact: measurable_itv.
  have -> : (fun x => kappa x `]t, +oo[) = EFin \o (fun x => 1 - regcdf pi x t)%R.
    by apply/funext => x; rw kappa_itvoy.
  apply/measurable_EFinP; apply: measurable_funB; first exact: measurable_cst.
  exact: measurable_regcdf.
have setIG : setI_closed ((@RGenOInfty.G R)).
  move=> _ _ [a ->] [b ->]; exists (Num.max a b).
  by apply/seteqP; split => r /=; rw !in_itv /= !andbT gt_max => /andP.
have lH : lambda_system setT H.
  split.
  - by move=> A _ ? _.
  - split => //.
    have -> : (fun x => kappa x setT) = cst 1 by apply/funext => x; rw kappaT.
    exact: measurable_cst.
  - move=> A C CA [mA fA] [mC fC]; split; first exact: measurableD.
    have AC : A `&` C = C.
      by apply/seteqP; split => [r []//|r Cr]; split => //; exact: CA.
    have -> : (fun x => kappa x (A `\` C)) = (fun x => kappa x A - kappa x C).
      apply/funext => x.
      have finA : kappa x A < +oo.
        by rw (le_lt_trans (probability_le1 _ _)) ?ltry.
      by rw measureD // AC.
    exact: emeasurable_funB.
  - move=> F ndF HF; split.
      by apply: bigcupT_measurable => i; exact: (HF i).1.
    apply: (emeasurable_fun_cvg (fun i x => kappa x (F i))) => [i|x _].
      exact: (HF i).2.
    apply: nondecreasing_cvg_measure => //; first by move=> i; exact: (HF i).1.
    by apply: bigcupT_measurable => i; exact: (HF i).1.
have sub := lambda_system_subset setIG lH GH (fun _ _ => @subsetT _ _).
have : <<s setT, (@RGenOInfty.G R) >> B.
  have mB' : (@ocitv R).-sigma.-measurable B.
    by rw RGenOpenSets.measurableE; exact: mB.
  by move: mB'; rw RGenOInfty.measurableE.
by move=> /sub [].
Qed.

(* kappa as a family of measures on R (with the MeasurableR structure), which
   is the same sigma-algebra as the domain of lebesgue_stieltjes_measure. *)
Definition kappaR (x : X) : set R -> \bar R := kappa x.

HB.instance Definition _ x := isMeasure.Build _ R R (kappaR x)
  (measure0 (kappa x)) (measure_ge0 (kappa x))
  (@measure_semi_sigma_additive _ _ _ (kappa x)).

HB.instance Definition _ x :=
  @Measure_isProbability.Build _ _ _ (kappaR x) (kappaT x).

(* the disintegrating kernel, as a probability kernel X ~> R *)
Definition kdis (x : X) : {measure set R -> \bar R} := kappaR x.

HB.instance Definition _ := isKernel.Build _ _ X R R kdis measurable_kappa.

HB.instance Definition _ :=
  Kernel_isProbability.Build _ _ _ _ R kdis (fun x => kappaT x).

Lemma kdisE x B : kdis x B = kappa x B. Proof. by []. Qed.

End kappa.

Section disintegration_rays.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Local Notation mu := (pmarg pi).
Local Notation F := (cdfq pi).

Let tn (t : R) (n : nat) : R := (t + n.+1%:R^-1)%R.

Let ttn t n : (t < tn t n)%R.
Proof. by rw /tn ltrDl invr_gt0. Qed.

(* rationals in ]t, t + 1/(n+1)[ *)
Let qs t n : rat := projT1 (cid (rat_in_itvoo (ttn t n))).

Let qsP t n : (t < ratr (qs t n))%R /\ (ratr (qs t n) < tn t n)%R.
Proof.
have := projT2 (cid (rat_in_itvoo (ttn t n))); rw in_itv /= => /andP[a b].
by split.
Qed.

Let regcdf_rat_cvg x t :
  ((fun n => regcdf pi x (ratr (qs t n))) @ \oo --> regcdf pi x t)%R.
Proof.
apply/cvgrPdist_lt => e e0.
have := @regcdf_rc _ _ _ pi x t => /cvgrPdist_lt /(_ e e0).
rw near_withinE => /nbhs_ballP[_ /posnumP[del] hdel].
near=> n.
have [tq qt] := qsP t n.
apply: (hdel (ratr (qs t n))) => //.
rw /ball /= distrC gtr0_norm ?subr_gt0 // ltrBlDl.
apply: (lt_trans qt); rw /tn ltrD2l.
near: n; exact: near_infty_natSinv_lt.
Unshelve. all: by end_near.
Qed.

Let bigcap_itvNytn t : \bigcap_n `]-oo, tn t n]%classic = `]-oo, t]%classic.
Proof.
apply/seteqP; split => [s /= h|s /= st n _]; last first.
  by move: st; rw !in_itv /= => /le_trans; apply; exact: ltW (ttn t n).
rw in_itv /=; apply/ler_addgt0Pr => e e0.
have [n ne] : exists n : nat, (n.+1%:R^-1 < e)%R.
  exists (truncn e^-1); rw -ltf_pV2 ?posrE ?invr_gt0 // invrK.
  exact: truncnS_gt.
have := h n I; rw /= in_itv /= => /le_trans; apply.
by rw /tn lerD2l ltW.
Qed.

Lemma integral_regcdf (A : set X) t : measurable A ->
  \int[mu]_(x in A) (regcdf pi x t)%:E = pi (A `*` `]-oo, t]).
Proof.
move=> mA.
have mf_ n : measurable_fun A (F (ratr (qs t n))).
  exact: measurable_funS measurableT (@subsetT _ _) (cdfq_measurable _ _).
have mf : measurable_fun A (fun x => (regcdf pi x t)%:E).
  apply: measurable_funS measurableT (@subsetT _ _) _.
  exact/measurable_EFinP/measurable_regcdf.
have f_f : {ae mu, forall x, A x ->
    (fun n => F (ratr (qs t n)) x) @ \oo --> (regcdf pi x t)%:E}.
  apply: filterS (good_ae pi) => x gx _.
  have Ex s : (regcdf pi x s)%:E = rcdf pi x s by rw regcdfE gpick_good.
  apply: (@squeeze_cvge _ _ _ _ (fun=> rcdf pi x t) _
    (fun n => (regcdf pi x (ratr (qs t n)))%:E)).
  - apply: nearW => n; have [tq _] := qsP t n.
    rw rcdf_le_cdfq //= Ex.
    exact: (cdfq_le_rcdf gx (lexx _)).
  - by rw -Ex; exact: cvg_cst.
  - by apply: cvg_EFin; [exact: nearW|exact: regcdf_rat_cvg].
have ig : mu.-integrable A (cst 1) by exact: (finite_measure_integrable_cst _ 1%R mA).
have f_g : {ae mu, forall x n, A x -> `|F (ratr (qs t n)) x| <= cst 1 x}.
  apply: filterS (good_ae pi) => x [_ h01 _ _] n _.
  by have [h0 h1] := h01 (qs t n); rw gee0_abs.
have [_ _ dct] := @dominated_convergence _ _ _ mu A mA
  (fun n => F (ratr (qs t n))) (fun x => (regcdf pi x t)%:E) (cst 1)
  mf_ mf f_f ig f_g.
have lim2 : (fun n => \int[mu]_(x in A) F (ratr (qs t n)) x) @ \oo -->
    pi (A `*` `]-oo, t]).
  have -> : (fun n => \int[mu]_(x in A) F (ratr (qs t n)) x) =
      (fun n => pi (A `*` `]-oo, ratr (qs t n)])).
    by apply/funext => n; rw cdfq_integral.
  have up : (fun n => pi (A `*` `]-oo, tn t n])) @ \oo --> pi (A `*` `]-oo, t]).
    rw -bigcap_itvNytn setX_bigcapr.
    apply: (@nonincreasing_cvg_measure _ _ _ pi
      (fun n => A `*` `]-oo, tn t n]%classic)).
    - by rw (le_lt_trans (probability_le1 pi _)) ?ltry //; exact: measurableX.
    - by move=> n; exact: measurableX.
    - by rw -setX_bigcapr bigcap_itvNytn; exact: measurableX.
    - move=> m n mn; apply/subsetPset; apply: setSX => // r /=.
      rw !in_itv /= => /le_trans; apply; rw /tn lerD2l lef_pV2 ?posrE //.
      by rw ler_nat.
  have hnear : \forall n \near \oo,
      (fun=> pi (A `*` `]-oo, t])) n <= pi (A `*` `]-oo, ratr (qs t n)]) <=
      pi (A `*` `]-oo, tn t n]).
    apply: nearW => n; have [tq qt] := qsP t n.
    apply/andP; split; apply: le_measure; rw ?inE; try exact: measurableX.
    - by apply: setSX => // r /=; rw !in_itv /= => /le_trans; apply; exact: ltW.
    - by apply: setSX => // r /=; rw !in_itv /= => /le_trans; apply; exact: ltW.
  exact: (squeeze_cvge _ _ _ hnear _ (cvg_cst _) up).
exact: cvg_unique dct lim2.
Qed.

End disintegration_rays.

(* B |-> pi (A `*` B), for fixed measurable A *)
Definition rslice {d d'} {X : measurableType d} {Y : measurableType d'}
    {R : realType} (pi : probability (X * Y)%type R) {A : set X}
    (mA : measurable A) (B : set Y) := pi (A `*` B).

Section rslice.
Context {d d'} {X : measurableType d} {Y : measurableType d'} {R : realType}.
Variable pi : probability (X * Y)%type R.
Variables (A : set X) (mA : measurable A).
Local Notation rslice := (rslice pi mA).

Let rslice0 : rslice set0 = 0.
Proof. by rw /rslice setX0 measure0. Qed.

Let rslice_ge0 B : 0 <= rslice B.
Proof. exact: measure_ge0. Qed.

Let rslice_sigma_additive : semi_sigma_additive rslice.
Proof.
move=> F mF tF mUF; rw /rslice setX_bigcupr.
apply: measure_semi_sigma_additive.
- by move=> n; exact: measurableX.
- move/trivIsetP : tF => tF; apply/trivIsetP => i j _ _ ij /=.
  by rw -setXI (tF i j) // setX0.
- by rw -setX_bigcupr; exact: measurableX.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ rslice
  rslice0 rslice_ge0 rslice_sigma_additive.

Let rslice_fin : fin_num_fun rslice.
Proof.
move=> B mB; rw ge0_fin_numE ?measure_ge0 //.
apply: (le_lt_trans (probability_le1 pi _)); last by rw ltry.
exact: measurableX.
Qed.

HB.instance Definition _ := Measure_isFinite.Build _ _ _ rslice rslice_fin.

End rslice.

(* B |-> \int[pmarg pi]_(x in A) kdis pi x B, for fixed measurable A *)
Definition kint {d} {X : measurableType d} {R : realType}
    (pi : probability (X * R)%type R) {A : set X} (mA : measurable A)
    (B : set R) := \int[pmarg pi]_(x in A) kdis pi x B.

Section kint.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Variables (A : set X) (mA : measurable A).
Local Notation kint := (kint pi mA).

Let kint0 : kint set0 = 0.
Proof.
rw /kint (eq_integral (cst 0)) ?integral0 //.
by move=> x _; rw measure0.
Qed.

Let kint_ge0 B : 0 <= kint B.
Proof. by apply: integral_ge0 => x _; exact: measure_ge0. Qed.

Let kint_sigma_additive : semi_sigma_additive kint.
Proof.
move=> F mF tF mUF.
suff <- : \sum_(n <oo) kint (F n) = kint (\bigcup_n F n).
  by apply: is_cvg_nneseries => n _ _; exact: kint_ge0.
rw /kint (eq_integral (fun x => \sum_(n <oo) kdis pi x (F n))).
  by move=> x _; rw measure_semi_bigcup.
rw integral_nneseries // => n.
exact: measurable_funS (measurable_kappa pi (mF n)).
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ kint
  kint0 kint_ge0 kint_sigma_additive.

Let kint_fin : fin_num_fun kint.
Proof.
move=> B mB; rw ge0_fin_numE ?kint_ge0 //.
have bnd : kint B <= \int[pmarg pi]_(x in A) cst 1 x.
  have mk : measurable_fun A (fun x => kdis pi x B).
    exact: measurable_funS (measurable_kappa pi mB).
  by apply: ge0_le_integral => // x _;
    first [exact: measure_ge0|exact: probability_le1].
apply: (le_lt_trans bnd).
by rw integral_cst // mul1e (le_lt_trans (probability_le1 _ _)) ?ltry.
Qed.

HB.instance Definition _ := Measure_isFinite.Build _ _ _ kint kint_fin.

End kint.

Section disintegration_R.
Context {d} {X : measurableType d} {R : realType}.
Variable pi : probability (X * R)%type R.
Local Notation mu := (pmarg pi).

Let setIG : setI_closed (@RGenOInfty.G R).
Proof.
move=> _ _ [a ->] [b ->]; exists (Num.max a b).
by apply/seteqP; split => r /=; rw !in_itv /= !andbT gt_max => /andP.
Qed.

(* Disintegration of a probability measure on X * R w.r.t. its first
   marginal (product-space form of [Klenke 2014, Thm 8.29]). *)
Theorem disintegration (A : set X) (B : set R) :
  measurable A -> measurable B ->
  pi (A `*` B) = \int[mu]_(x in A) kdis pi x B.
Proof.
move=> mA mB.
have mreg t : measurable_fun A (fun x => (regcdf pi x t)%:E).
  apply: measurable_funS measurableT (@subsetT _ _) _.
  exact/measurable_EFinP/measurable_regcdf.
have ireg t : mu.-integrable A (fun x => (regcdf pi x t)%:E).
  apply/integrableP; split; first exact: mreg.
  rw (eq_integral (fun x => (regcdf pi x t)%:E)).
    by move=> x _; rw gee0_abs // lee_fin regcdf_ge0.
  rw integral_regcdf // (le_lt_trans (probability_le1 _ _)) ?ltry //.
  exact: measurableX.
have muA : mu A = pi (A `*` setT) by [].
have Gsub : @RGenOInfty.G R `<=` measurable by move=> _ [t ->].
have : <<s (@RGenOInfty.G R) >> B.
  have mB' : (@ocitv R).-sigma.-measurable B.
    by rw RGenOpenSets.measurableE; exact: mB.
  by move: mB'; rw RGenOInfty.measurableE.
apply: (@g_sigma_algebra_finite_measure_unique _ _ _ (@RGenOInfty.G R)
  Gsub setIG (rslice pi mA) (kint pi mA)).
- rw /= /rslice /kint (eq_integral (cst 1)).
    by move=> x _; exact: probability_setT.
  by rw integral_cst // mul1e.
- move=> _ [t ->]; rw /= /rslice /kint.
  have -> : A `*` `]t, +oo[ = (A `*` setT) `\` (A `*` `]-oo, t]).
    apply/seteqP; split => [[a r] /= [Aa]|[a r] /= [[Aa _]]].
      by rw !in_itv /= andbT => tr; split => // -[_]; rw leNgt tr.
    by move=> /not_andP[//|]; rw !in_itv /= andbT => /negP; rw -ltNge.
  have fin : pi (A `*` setT) < +oo.
    by rw (le_lt_trans (probability_le1 _ _)) ?ltry //; exact: measurableX.
  have AI : (A `*` setT) `&` (A `*` `]-oo, t]) = A `*` `]-oo, t].
    by apply/seteqP; split => [[a r] [[]]|[a r] [Aa rt]].
  rw measureD //; try exact: measurableX.
  rw AI.
  have -> : \int[mu]_(x in A) kdis pi x `]t, +oo[%classic =
      \int[mu]_(x in A) (((cst 1%R) x)%:E - (regcdf pi x t)%:E).
    by apply: eq_integral => x _; rw kdisE kappa_itvoy EFinB.
  have i1 : mu.-integrable A (EFin \o (cst 1%R)).
    exact: (finite_measure_integrable_cst _ 1%R mA).
  have i2 := ireg t.
  rw integralB_EFin //.
  have -> : \int[mu]_(x in A) ((cst 1%R) x)%:E = mu A.
    by rw (eq_integral (cst 1%E)) // integral_cst // mul1e.
  by rw integral_regcdf.
Qed.

End disintegration_R.

(* Transfer to standard Borel spaces (standardBorelType, see
   analysis_extras.v) [Klenke 2014, Thm 8.37]. *)
(* TODO: move to move_to_standard_borel (HB fails there on R). *)
Section standard_borel_R.
Context {R : realType}.

Let id_measurable : measurable_fun [set: R] (@id R).
Proof. exact: measurable_id. Qed.

HB.instance Definition _ := Measurable_isStandardBorel.Build R _ R
  id_measurable id_measurable (fun=> erefl).

End standard_borel_R.

Section borel_transfer.
Context {d dT} {X : measurableType d} {R : realType} {T : standardBorelType R dT}.

Let emb (p : X * T) : X * R := (p.1, sb_encode p.2).

Let memb : measurable_fun [set: X * T] emb.
Proof.
apply: measurable_fun_pair; first exact: measurable_fst.
exact: measurableT_comp measurable_sb_encode measurable_snd.
Qed.

Variable pi : probability (X * T)%type R.

(* the image of pi in X * R *)
Definition pemb (A : set (X * R)) := pi (emb @^-1` A).

Let pemb0 : pemb set0 = 0.
Proof. by rw /pemb preimage_set0 measure0. Qed.

Let pemb_ge0 A : 0 <= pemb A.
Proof. exact: measure_ge0. Qed.

Let mpre A : measurable A -> measurable (emb @^-1` A).
Proof. by move=> mA; rw -[X in measurable X]setTI; exact: memb. Qed.

Let pemb_sigma_additive : semi_sigma_additive pemb.
Proof.
move=> F mF tF mUF; rw /pemb preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; exact: mpre.
- move/trivIsetP : tF => tF; apply/trivIsetP => i j _ _ ij /=.
  by rw -preimage_setI (tF i j) // preimage_set0.
- by rw -preimage_bigcup; exact: mpre.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ pemb
  pemb0 pemb_ge0 pemb_sigma_additive.

Let pembT : pemb setT = 1.
Proof. by rw /pemb preimage_setT probability_setT. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ _ pemb pembT.

Lemma pembX (A : set X) (C : set T) :
  pemb (A `*` (sb_encode @` C)) = pi (A `*` C).
Proof.
congr (pi _); apply/seteqP; split => [[x t] /= [Ax [t' Ct' /sb_encode_inj <-]]|].
  by [].
by move=> [x t] /= [Ax Ct]; split => //; exists t.
Qed.

Lemma pmarg_pemb (A : set X) : pmarg pemb A = pmarg pi A.
Proof.
by rw /pmarg !psliceE /pemb; congr (pi _).
Qed.

End borel_transfer.

(* the pulled-back measures A |-> kdis (pemb pi) x (sb_encode @` A) *)
Definition kimg {d dT} {X : measurableType d} {R : realType}
    {T : standardBorelType R dT} (pi : probability (X * T)%type R) (x : X)
    (A : set T) := kdis (pemb pi) x (sb_encode @` A).

Section kimg.
Context {d dT} {X : measurableType d} {R : realType} {T : standardBorelType R dT}.
Variables (pi : probability (X * T)%type R) (x : X).
Local Notation kimg := (kimg pi x).

Let kimg0 : kimg set0 = 0.
Proof. by rw /kimg image_set0 measure0. Qed.

Let kimg_ge0 A : 0 <= kimg A.
Proof. exact: measure_ge0. Qed.

Let kimg_sigma_additive : semi_sigma_additive kimg.
Proof.
move=> F mF tF mUF; rw /kimg image_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; exact: measurable_sb_image.
- move/trivIsetP : tF => tF; apply/trivIsetP => i j _ _ ij /=.
  apply/seteqP; split => // r [[a Fia <-] [b Fjb]] /sb_encode_inj ba.
  by have := tF i j I I ij; rw -subset0 => /(_ a); apply; split => //; rw -ba.
- by rw -image_bigcup; exact: measurable_sb_image.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ kimg
  kimg0 kimg_ge0 kimg_sigma_additive.

End kimg.

Section borel_kernel.
Context {d dT} {X : measurableType d} {R : realType} {T : standardBorelType R dT}.
Variable pi : probability (X * T)%type R.

(* where the pulled-back measure has full mass *)
Definition kgood : set X := [set x | 1 <= kimg pi x setT].

Lemma measurable_kgood : measurable kgood.
Proof.
rw -[kgood]setTI; apply: measurable_lee => //.
have mk := measurable_kernel (kdis (pemb pi)) _ (measurable_sb_image _ (@measurableT _ T)).
rw /kimg; exact: mk.
Qed.

(* T is inhabited, since pi is a probability measure on X * T *)
Let exists_T : exists t : T, True.
Proof.
apply/not_existsP => /= nT; have := probability_setT pi.
rw (_ : [set: X * T] = set0) ?measure0.
  by apply/seteqP; split => // -[x t] _; exact: (nT t).
by move=> /eqP; rw lt_eqF // lte01.
Qed.

Definition tpoint : T := projT1 (cid exists_T).

(* the disintegrating kernel on a standard Borel space *)
Definition kborel (x : X) : {measure set T -> \bar R} :=
  if pselect (kgood x) is left _ then kimg pi x else \d_tpoint.

Lemma kborelE x A : kborel x A =
  kimg pi x A * (\1_kgood x)%:E + \d_tpoint A * (1 - \1_kgood x)%:E.
Proof.
rw /kborel indicE; case: pselect => gx.
  by rw mem_set // mule1 subrr mule0 adde0.
by rw memNset // mule0 add0e subr0 mule1.
Qed.

Let measurable_kborel A : measurable A ->
  measurable_fun [set: X] (fun x => kborel x A).
Proof.
move=> mA; under eq_fun do rw kborelE.
apply: emeasurable_funD; apply: emeasurable_funM.
- exact: (measurable_kernel (kdis (pemb pi)) _ (measurable_sb_image _ mA)).
- by apply/measurable_EFinP; exact: measurable_indic measurable_kgood.
- exact: measurable_cst.
- apply/measurable_EFinP; apply: measurable_funB; first exact: measurable_cst.
  exact: measurable_indic measurable_kgood.
Qed.

HB.instance Definition _ := isKernel.Build _ _ X T R kborel measurable_kborel.

Let kborelT x : kborel x setT = 1.
Proof.
rw /kborel; case: pselect => [gx|_]; last exact: diracT.
apply/le_anti; rw gx andbT.
exact: probability_le1 (measurable_sb_image _ measurableT).
Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ R kborel kborelT.

End borel_kernel.

Section disintegration_borel.
Context {d dT} {X : measurableType d} {R : realType} {T : standardBorelType R dT}.
Variable pi : probability (X * T)%type R.
Local Notation mu := (pmarg pi).

Let mimg : measurable (sb_encode @` [set: T]).
Proof. exact: measurable_sb_image _ measurableT. Qed.

Let mkimg (C : set T) : measurable C ->
  measurable_fun [set: X] (fun x => kimg pi x C).
Proof.
move=> mC; rw /kimg.
exact: (measurable_kernel (kdis (pemb pi)) _ (measurable_sb_image _ mC)).
Qed.

Let int_kimg (E : set X) (C : set T) : measurable E -> measurable C ->
  \int[mu]_(x in E) kimg pi x C = pi (E `*` C).
Proof.
move=> mE mC; rw -pembX (disintegration (pemb pi) mE (measurable_sb_image _ mC)).
apply: eq_measure_integral => B mB _ /=.
by first [exact: pmarg_pemb | exact/esym/pmarg_pemb].
Qed.

Lemma kgood_ae : {ae mu, forall x, kgood pi x}.
Proof.
have mk1 := mkimg measurableT.
have i1 : mu.-integrable [set: X] (cst 1).
  exact: (finite_measure_integrable_cst _ 1%R measurableT).
have ik : mu.-integrable [set: X] (fun x => kimg pi x setT).
  apply/integrableP; split => //.
  apply: (le_lt_trans (_ : _ <= \int[mu]_(x in [set: X]) cst 1 x)).
    apply: ge0_le_integral => //.
    - by apply: measurableT_comp => //; exact: abse_measurable.
    - by move=> x _; rw gee0_abs ?measure_ge0 //; exact: probability_le1.
  rw integral_cst // mul1e.
  by first [exact: (le_lt_trans (probability_le1 _ measurableT) (ltry _)) | rw -ge0_fin_numE //; exact: fin_num_measure].
have := @integral_le_ae _ _ _ mu _ measurableT (fun x => kimg pi x setT)
  (cst 1) i1 ik.
move=> /(_ _) h; apply: filterS (h _) => [x /(_ I) //|E _ mE].
by rw int_kimg // integral_cst // mul1e.
Qed.

(* Disintegration on standard Borel spaces [Klenke 2014, Thm 8.37,
   product form]. *)
Theorem disintegration_borel (A : set X) (C : set T) :
  measurable A -> measurable C ->
  pi (A `*` C) = \int[mu]_(x in A) kborel pi x C.
Proof.
move=> mA mC; rw -int_kimg //.
apply: ae_eq_integral => //.
- exact: measurable_funS (mkimg mC).
- exact: measurable_funS (measurable_kernel (kborel pi) _ mC).
- apply: filterS kgood_ae => x gx _.
  by rw /kborel; case: pselect.
Qed.

End disintegration_borel.

