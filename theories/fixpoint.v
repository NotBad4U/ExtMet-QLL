(* Guarded recursion in CExtMet: Banach's theorem for extended metrics and
   the FIX combinator (paper, Sect. "Fixed points of non-expansive maps"). *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import discrete_topology.
From ExtMetQLL Require Import analysis_extras extmet.

(**md**************************************************************************)
(* # Fixed points of contractions on complete extended metric spaces         *)
(*                                                                            *)
(* Correction of the paper.  Lemma "Guarded recursion in CExtMet" claims     *)
(* fix : (pY -o Y) -> (1-p)Y for every non-empty complete Y.  This is false: *)
(* in nat with the discrete {0, +oo} distance (complete), the successor is a *)
(* p-contraction for every p in ]0, 1[ and has no fixed point               *)
(* (guarded_fix_counterexample).  The remark "a p-contraction maps each      *)
(* galaxy into itself" is false as well (succ_galaxy): Banach's argument     *)
(* only applies from a seed y0 at finite displacement d(y0, f y0) < +oo,     *)
(* and then yields the unique fixed point in the galaxy of y0 (ebanach).     *)
(* The lemma holds under either additional hypothesis:                        *)
(* - Y is a single galaxy (all distances finite): fix = gfix is defined for  *)
(*   every contraction and (1 - p) d(fix f, fix g) <= sup_y d(f y, g y)      *)
(*   (gfix_le), whence fp(F) non-expansive into (1 - p)Y (gfix_param);       *)
(* - or, for fp(F) : X -> Y, a non-expansive seed s : X -> Y with            *)
(*   d(s x, F x (s x)) < +oo, taking fp(F)(x) = the fixed point in the       *)
(*   galaxy of s x (efix_param).  The typing rule (FIX) then needs such a    *)
(*   seed (or a single-galaxy codomain) in addition to p < 1.                *)
(*                                                                            *)
(* ```                                                                        *)
(*       efix y0 f == limit of the iterates of f from y0; when f is a        *)
(*                    contraction and d(y0, f y0) < +oo, it is the unique    *)
(*                    fixed point of f at finite distance from y0            *)
(*          gfix f == efix point f, FIX on a single-galaxy space             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section econtraction_scalar.
Context {R : realType}.
Implicit Types r : {itv \bar R & `[0, 1[}.

Lemma econtraction_ge0 r : 0 <= r%:num.
Proof. by case: r => x /= /andP[_]; rw /= in_itv /= => /andP[]. Qed.

Lemma econtraction_lt1 r : r%:num < 1.
Proof. by case: r => x /= /andP[_]; rw /= in_itv /= => /andP[]. Qed.

Lemma econtraction_fin r : r%:num \is a fin_num.
Proof.
by rw ge0_fin_numE ?econtraction_ge0 // (lt_trans (econtraction_lt1 r)) ?ltry.
Qed.

Lemma econtraction_fine_ge0 r : (0 <= fine r%:num)%R.
Proof. exact/fine_ge0/econtraction_ge0. Qed.

Lemma econtraction_fine_lt1 r : (fine r%:num < 1)%R.
Proof. by rw -lte_fin fineK ?econtraction_fin ?econtraction_lt1. Qed.

Lemma econtractionE (X Y : pseudoMetricType R) r (f : X -> Y) :
  econtraction r f ->
  forall x y, edist (f x, f y) <= (fine r%:num)%:E * edist (x, y).
Proof. by move=> fr x y; rw fineK ?econtraction_fin //; exact: fr. Qed.

End econtraction_scalar.

(* Banach's theorem in a complete extended metric space: the iteration from a
   seed y0 at finite displacement converges to the unique fixed point in the
   galaxy of y0. *)
Section ebanach.
Context {R : realType} {Y : completeExtMetricType R}.

Definition efix (y0 : Y) (f : Y -> Y) : Y := limn (fun n => iter n f y0).

Variables (r : {itv \bar R & `[0, 1[}) (f : Y -> Y).
Hypothesis fr : econtraction r f.

Let q0 := econtraction_fine_ge0 r.
Let q1 := econtraction_fine_lt1 r.
Let fq := econtractionE fr.

Section seed.
Variable y0 : Y.
Hypothesis y0fin : edist (y0, f y0) < +oo.

Lemma efix_cvg : iter n f y0 @[n --> \oo] --> efix y0 f.
Proof. by move: (banach_cvg q0 q1 fq y0fin). Qed.

Lemma efixP : f (efix y0 f) = efix y0 f.
Proof. by apply/esym/edist_eq0; move: (banach_fixed q0 q1 fq y0fin). Qed.

Lemma efix_dist :
  edist (y0, efix y0 f) <= edist (y0, f y0) * ((1 - fine r%:num)^-1)%:E.
Proof.
apply: le_trans (banach_dist_lim q0 q1 fq y0fin) _.
by rw EFinM fineK // ge0_fin_numE.
Qed.

Lemma efix_fin : edist (y0, efix y0 f) < +oo.
Proof. exact: le_lt_trans (banach_dist_lim q0 q1 fq y0fin) (ltry _). Qed.

Lemma efix_dist_mul : (1 - r%:num) * edist (y0, efix y0 f) <= edist (y0, f y0).
Proof.
have q1' : (0 < 1 - fine r%:num)%R by rw subr_gt0.
rw -[r%:num]fineK ?econtraction_fin // -EFinB muleC.
rw -lee_pdivlMr //; exact: efix_dist.
Qed.

Lemma efix_unique z : f z = z -> edist (y0, z) < +oo -> z = efix y0 f.
Proof.
move=> fz y0z; apply/edist_eq0/(contraction_edist0 q1 fq).
- by rw fz edist_refl.
- by rw efixP edist_refl.
- apply: le_lt_trans (edist_triangle _ y0 _) _.
  by rw edist_sym lte_add_pinfty ?efix_fin.
Qed.

Theorem ebanach : exists! z, f z = z /\ edist (y0, z) < +oo.
Proof.
exists (efix y0 f); split; first by rw efixP efix_fin.
by move=> z [fz y0z]; rw (efix_unique fz y0z).
Qed.

End seed.

(* The fixed point only depends on the galaxy of the seed. *)
Lemma efix_galaxy y0 y1 : edist (y0, f y0) < +oo -> edist (y0, y1) < +oo ->
  efix y1 f = efix y0 f.
Proof.
move=> y0fin y01; have y1fin : edist (y1, f y1) < +oo.
  apply: le_lt_trans (edist_triangle _ y0 _) _; rw edist_sym lte_add_pinfty //.
  apply: le_lt_trans (edist_triangle _ (f y0) _) _; rw lte_add_pinfty //.
  apply: le_lt_trans (fq _ _) _.
  rw -(@fineK _ (edist (y0, y1))) ?ge0_fin_numE // -EFinM; exact: ltry.
apply: efix_unique (efixP y1fin) _ => //.
apply: le_lt_trans (edist_triangle _ y1 _) _; rw lte_add_pinfty //.
exact: efix_fin.
Qed.

End ebanach.

(* The key estimate behind the non-expansiveness of FIX: if a = f a, b = g b
   lie in the same galaxy and f is an r-contraction, then
   d(a, b) <= d(f a, f b) + d(f b, g b) <= r d(a, b) + d(f b, g b). *)
Lemma fixed_point_edist_le {R : realType} {Y : pseudoMetricType R}
    (r : {itv \bar R & `[0, 1[}) (f g : Y -> Y) (a b : Y) :
  econtraction r f -> f a = a -> g b = b -> edist (a, b) < +oo ->
  (1 - r%:num) * edist (a, b) <= edist (f b, g b).
Proof.
move=> fr fa gb abfin.
have le : edist (a, b) <= r%:num * edist (a, b) + edist (f b, g b).
  rw -{1}fa -{1}gb; apply: le_trans (edist_triangle _ (f b) _) _.
  by apply: leeD => //; exact: fr.
have Dfin : edist (a, b) \is a fin_num by rw ge0_fin_numE.
have rfin := econtraction_fin r.
by rw muleBl ?fin_num_adde_defr // mul1e leeBlDr ?fin_numM // addeC.
Qed.

(* FIX on a single galaxy: when all distances in Y are finite, every
   contraction has a unique fixed point, reached from any seed (here the
   point of Y), and FIX is non-expansive from the sup distance, scaled by
   1 - r. *)
Definition gfix {R : realType} {Y : completeExtMetricType R} (f : Y -> Y) : Y :=
  efix point f.

Section single_galaxy.
Context {R : realType} {Y : completeExtMetricType R}.
Hypothesis Yfin : forall x y : Y, edist (x, y) < +oo.
Implicit Types (r : {itv \bar R & `[0, 1[}) (f g : Y -> Y).

Lemma gfixP r f : econtraction r f -> f (gfix f) = gfix f.
Proof. by move=> fr; exact: efixP fr _ (Yfin _ _). Qed.

Lemma gfix_unique r f z : econtraction r f -> f z = z -> z = gfix f.
Proof. by move=> fr fz; exact: efix_unique fr _ (Yfin _ _) _ fz (Yfin _ _). Qed.

Lemma gfix_le r s f g : econtraction r f -> econtraction s g ->
  (1 - r%:num) * edist (gfix f, gfix g) <=
  ereal_sup [set edist (f y, g y) | y in [set: Y]].
Proof.
move=> fr gs; apply: le_trans (fixed_point_edist_le fr (gfixP fr) (gfixP gs)
  (Yfin _ _)) _.
by apply: ereal_sup_ubound; exists (gfix g).
Qed.

(* The partial fixed point fp(F) of the paper, for F non-expansive in its
   first argument (uniformly in the second). *)
Lemma gfix_param (X : pseudoMetricType R) r (F : X -> Y -> Y) :
  (forall x, econtraction r (F x)) ->
  (forall x x' y, edist (F x y, F x' y) <= edist (x, x')) ->
  forall x x', (1 - r%:num) * edist (gfix (F x), gfix (F x')) <= edist (x, x').
Proof.
move=> Fr FX x x'; apply: le_trans (gfix_le (Fr x) (Fr x')) _.
by apply: ge_ereal_sup => _ [y _ <-]; exact: FX.
Qed.

End single_galaxy.

(* FIX on an arbitrary complete extended metric space, given a non-expansive
   seed at finite displacement: x |-> efix (s x) (F x) is non-expansive into
   (1 - r) Y. *)
Lemma efix_param {R : realType} {X : pseudoMetricType R}
    {Y : completeExtMetricType R} (r : {itv \bar R & `[0, 1[})
    (F : X -> Y -> Y) (s : X -> Y) :
  (forall x, econtraction r (F x)) ->
  (forall x x' y, edist (F x y, F x' y) <= edist (x, x')) ->
  nonexpansive s -> (forall x, edist (s x, F x (s x)) < +oo) ->
  forall x x', (1 - r%:num) * edist (efix (s x) (F x), efix (s x') (F x')) <=
               edist (x, x').
Proof.
move=> Fr FX /nonexpansiveP sX sfin x x'.
have [->|] := eqVneq (edist (x, x')) +oo; first exact: leey.
rw -ltey => xx'; apply: le_trans (FX _ _ (efix (s x') (F x'))).
apply: fixed_point_edist_le (Fr x) (efixP (Fr x) (sfin x))
  (efixP (Fr x') (sfin x')) _.
have h1 := efix_fin (Fr x) (sfin x); have h2 := efix_fin (Fr x') (sfin x').
have h3 : edist (s x, s x') < +oo := le_lt_trans (sX _ _) xx'.
apply: le_lt_trans (edist_triangle _ (s x) _) _.
rw [edist (efix _ _, _)]edist_sym lte_add_pinfty //.
apply: le_lt_trans (edist_triangle _ (s x') _) _.
by rw lte_add_pinfty.
Qed.

(* Counterexample to the paper's lemma as stated: nat with the discrete
   {0, +oo}-valued distance is a non-empty complete extended metric space,
   the successor is an r-contraction for every r in ]0, 1[ (it is an
   isometry and all non-zero distances are +oo), but it has no fixed point.
   Every point is its own galaxy and the successor moves each point to
   another galaxy. *)
Section counterexample.
Context {R : realType}.

Local Notation dnat := (discrete_topology nat).

Lemma dnat_edistE (x y : dnat) :
  edist (x, y) = (if x == y then 0 else +oo :> \bar R).
Proof. exact: discrete_edistE. Qed.

Lemma dnat_cauchy_cvg (F : set_system dnat) :
  ProperFilter F -> cauchy F -> cvg F.
Proof. by move=> FF; exact: cauchy_cvg. Qed.

Lemma succ_econtraction (r : {itv \bar R & `[0, 1[}) :
  0 < r%:num -> econtraction r (S : dnat -> dnat).
Proof.
move=> r0 x y /=; rw !dnat_edistE eqSS.
by case: eqP => _; rw ?mule0 // muleC gt0_mulye.
Qed.

Lemma succ_galaxy (x : dnat) : edist (x, S x) = +oo :> \bar R.
Proof. by rw dnat_edistE eqn_leq ltnn andbF. Qed.

Lemma succ_no_fixpoint (x : dnat) : S x != x.
Proof. by rw eqn_leq ltnn. Qed.

Theorem guarded_fix_counterexample : exists (Y : completeExtMetricType R)
    (f : Y -> Y), (forall r : {itv \bar R & `[0, 1[}, 0 < r%:num ->
      econtraction r f) /\ forall y, f y != y.
Proof.
exists dnat, S; split; [exact: succ_econtraction | exact: succ_no_fixpoint].
Qed.

End counterexample.
