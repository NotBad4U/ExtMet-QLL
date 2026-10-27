(* The truth values Prop = [0, +oo] with the log metric, a complete extended
   pseudometric space: the object of CExtMet that interprets the type Prop of
   the calculus (paper, Sect. "Logic"). *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure num_topology normedtype.
From mathcomp Require Import urysohn sequences exp.
From ExtMetQLL Require Import analysis_extras extmet cextmet.

(**md**************************************************************************)
(* # The truth values as an object of CExtMet                                 *)
(*                                                                            *)
(* Prop = [0, +oo] carries the log metric d(a, b) = |ln a - ln b|, under     *)
(* which the crisp values 0 and +oo are at infinite distance from every     *)
(* other value.  Prop is then isometric to the coproduct 1 + R + 1 (0, the   *)
(* soft values through ln, and +oo), whence the metric axioms and the        *)
(* completeness.                                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*            prop R == the truth values [0, +oo], {nonneg \bar R} as a      *)
(*                      separate type carrying the log metric                *)
(*   mkprop x0 == the truth value x, from a proof x0 of 0 <= x               *)
(*       estar x == the involution 1 / x on [0, +oo], with 0* = +oo         *)
(*     prop_dist a b == the log metric: 0 if a = b, |ln a - ln b| if both    *)
(*                      are in ]0, +oo[, +oo otherwise                       *)
(*   prop_code, prop_decode == the isometry Prop ~ 1 + R + 1 and its inverse *)
(* ```                                                                        *)
(* prop R is a complete pseudometric space with edist = prop_dist            *)
(* (prop_edistE), pointed at 1.                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* Prop = [0, +oo]: the carrier of the sensitivities Ω (the paper's Ω), as a
   separate type since it carries the log metric. *)
Definition prop (R : realType) : Type := {nonneg \bar R}.

Arguments prop : clear implicits.

Section prop_space.
Context {R : realType}.
Implicit Types (a b c : prop R) (x y : \bar R).

(* Truth values from non-negative extended reals. *)
Lemma mkprop_subproof x : 0 <= x ->
  Itv.spec (@ext_num_sem R) (Itv.Real `[0, +oo[%R) x.
Proof.
by move=> x0; rw /Itv.spec /= /ext_num_sem /= /Order.comparable in_itv /= x0.
Qed.

Definition mkprop x (x0 : 0 <= x) : prop R := Itv.mk (mkprop_subproof x0).

Lemma mkpropE x (x0 : 0 <= x) : (mkprop x0)%:num = x. Proof. by []. Qed.

(* The involution a* = 1 / a, with 0* = +oo and (+oo)* = 0. *)
Definition estar x : \bar R :=
  if x == 0 then +oo else if x == +oo then 0 else ((fine x)^-1)%:E.

Lemma estar_ge0 x : 0 <= x -> 0 <= estar x.
Proof.
rw /estar; case: ifP => // _; case: ifP => // _ x0.
by rw lee_fin invr_ge0 fine_ge0.
Qed.

(* The log metric d(a, b) = |ln a - ln b|, the crisp values 0 and +oo at
   infinite distance from the soft ones. *)
Definition prop_dist a b : \bar R :=
  if a == b then 0 else
  if (0 < a%:num < +oo) && (0 < b%:num < +oo) then
    `|ln (fine a%:num) - ln (fine b%:num)|%:E
  else +oo.

(* The isometry with 1 + R + 1: 0 is the left point, a soft value a is
   ln a, and +oo is the right point. *)
Local Notation Z := (coprod Datatypes.unit (coprod R Datatypes.unit)).

Definition ecode x : Z :=
  if x == 0 then inl tt else if x == +oo then inr (inr tt)
  else inr (inl (ln (fine x))).

Definition prop_code a : Z := ecode a%:num.

Let expR_ge0E (r : R) : (0 : \bar R) <= (expR r)%:E.
Proof. by rw lee_fin expR_ge0. Qed.

Definition prop_decode (u : Z) : prop R :=
  match u with
  | inl _ => mkprop (lexx (0 : \bar R))
  | inr (inl r) => mkprop (expR_ge0E r)
  | inr (inr _) => mkprop (leey (0 : \bar R))
  end.

(* A non-negative extended real is 0, +oo or a positive real. *)
Let ge0_ecase x : 0 <= x -> [\/ x = 0, x = +oo | exists2 r, (0 < r)%R & x = r%:E].
Proof.
case: x => [r||] r0; last by rw leeNy_eq in r0.
  have [->|rn0] := eqVneq r 0%R; first exact: Or31.
  by apply: Or33; exists r => //; rw lt_def rn0 -lee_fin.
exact: Or32.
Qed.

Let ecode0 : ecode 0 = inl tt.
Proof. by rw /ecode eqxx. Qed.

Let ecodey : ecode +oo = inr (inr tt).
Proof. by rw /ecode gt_eqF ?lt0y // eqxx. Qed.

Let ecode_fin (r : R) : (0 < r)%R -> ecode r%:E = inr (inl (ln r)).
Proof. by move=> r0; rw /ecode gt_eqF ?lte_fin // lt_eqF ?ltry. Qed.

Let ecodeK x : 0 <= x -> (prop_decode (ecode x))%:num = x.
Proof.
case/ge0_ecase=> [->|->|[r r0 ->]]; first by rw ecode0.
  by rw ecodey.
by rw ecode_fin //= lnK // posrE.
Qed.

Lemma prop_codeK : cancel prop_code prop_decode.
Proof. by move=> a; apply/val_inj; exact: (ecodeK (ge0e a)). Qed.

Lemma prop_decodeK : cancel prop_decode prop_code.
Proof.
case=> [[]|[r|[]]]; rw /prop_code ?mkpropE; first exact: ecode0.
  by rw ecode_fin ?expR_gt0 // expRK.
exact: ecodey.
Qed.

(* The log metric is the distance of 1 + R + 1 through the coding. *)
Let edist_inr_inl (A B : pseudoMetricType R) (b : B) (a : A) :
  edist ((inr b : coprod A B), (inl a : coprod A B)) = +oo.
Proof. by rw coprod_edistE. Qed.

Let ecode_dist x y : 0 <= x -> 0 <= y -> x != y ->
  edist (ecode x, ecode y) =
  (if (0 < x < +oo) && (0 < y < +oo) then `|ln (fine x) - ln (fine y)|%:E
   else +oo).
Proof.
move=> /ge0_ecase[->|->|[r r0 ->]] /ge0_ecase[->|->|[s s0 ->]] xy;
  rw ?eqxx // in xy;
  rw ?ecode0 ?ecodey ?ecode_fin // ?ltxx ?andbF //= ?edist_inl_inr //
     ?edist_inr_inl //.
- by rw coprod_edistE /= edist_inr_inl.
- by rw coprod_edistE /= edist_inl_inr.
- rw coprod_edistE /= coprod_edistE /= normed_edistE.
  by rw !lte_fin r0 s0 !ltry.
Qed.

Lemma prop_distE a b : prop_dist a b = edist (prop_code a, prop_code b).
Proof.
rw /prop_dist; have [<-|ab] := eqVneq a b; first by rw edist_refl.
(* a != b is a%:num != b%:num, the equality of prop R being that of its values *)
by rw /prop_code ecode_dist ?ge0e.
Qed.

Let prop_dist_ge0 a b : 0 <= prop_dist a b.
Proof. by rw prop_distE edist_ge0. Qed.

Let prop_dist_xx : self_inverse 0 prop_dist.
Proof. by move=> a; rw /prop_dist eqxx. Qed.

Let prop_distC : commutative prop_dist.
Proof. by move=> a b; rw !prop_distE edist_sym. Qed.

Let prop_dist_triangle a b c : prop_dist a c <= prop_dist a b + prop_dist b c.
Proof. by rw !prop_distE; exact: edist_triangle. Qed.

HB.instance Definition _ := Choice.on (prop R).
HB.instance Definition _ := isExtPseudoMetric.Build R (prop R)
  prop_dist_ge0 prop_dist_xx prop_distC prop_dist_triangle.

Lemma prop_edistE a b : edist (a, b) = prop_dist a b.
Proof. exact: (@edistE _ _ prop_dist). Qed.

Lemma prop_decode_isometry : isometry prop_decode.
Proof. by move=> u v; rw prop_edistE prop_distE !prop_decodeK. Qed.

(* A log distance at most e is a two-sided multiplicative bound by e^e. *)
Let expR_gt0E (r : R) : (0 : \bar R) < (expR r)%:E.
Proof. by rw lte_fin expR_gt0. Qed.

Let decode_le u v (e : R) : edist (u, v) <= e%:E ->
  (prop_decode u)%:num <= (expR e)%:E * (prop_decode v)%:num.
Proof.
have c0 := expR_gt0E e.
case: u => [[]|[r|[]]]; case: v => [[]|[r'|[]]];
  rw !coprod_edistE /= ?coprod_edistE /= => uv.
- by rw mule0 lexx.
- by apply: mule_ge0; exact: ltW (expR_gt0E _).
- by apply: mule_ge0; [exact: ltW (expR_gt0E _) | exact: leey].
- by rw leNgt ltry in uv.
- rw normed_edistE lee_fin ler_norml in uv; case/andP: uv => _ uv.
  by rw -EFinM lee_fin -expRD ler_expR -lerBlDr.
- by rw gt0_muley // leey.
- by rw leNgt ltry in uv.
- by rw leNgt ltry in uv.
- by rw gt0_muley ?lexx.
Qed.

Let decode_of_le u v (e : R) : (0 <= e)%R ->
  (prop_decode u)%:num <= (expR e)%:E * (prop_decode v)%:num ->
  (prop_decode v)%:num <= (expR e)%:E * (prop_decode u)%:num ->
  edist (u, v) <= e%:E.
Proof.
move=> e0; case: u => [[]|[r|[]]]; case: v => [[]|[r'|[]]];
  rw !coprod_edistE /= ?coprod_edistE /= => h1 h2.
- by rw unit_edistE lee_fin.
- by rw mule0 leNgt expR_gt0E in h2.
- by rw mule0 leNgt lt0y in h2.
- by rw mule0 leNgt expR_gt0E in h1.
- move: h1 h2; rw -!EFinM !lee_fin -!expRD !ler_expR => h1 h2.
  rw normed_edistE lee_fin ler_norml; apply/andP; split.
    by rw lerNl opprB lerBlDr.
  by rw lerBlDr.
- by rw -EFinM leNgt ltry in h2.
- by rw mule0 leNgt lt0y in h1.
- by rw -EFinM leNgt ltry in h1.
- by rw unit_edistE lee_fin.
Qed.

Lemma prop_dist_le_mul a b (e : R) :
  prop_dist a b <= e%:E -> a%:num <= (expR e)%:E * b%:num.
Proof. by rw prop_distE => /decode_le; rw !prop_codeK. Qed.

Lemma prop_dist_le_of_mul a b (e : R) : (0 <= e)%R ->
  a%:num <= (expR e)%:E * b%:num -> b%:num <= (expR e)%:E * a%:num ->
  prop_dist a b <= e%:E.
Proof.
by move=> e0 ab ba; rw prop_distE; apply: decode_of_le e0 _ _; rw !prop_codeK.
Qed.

(* The involution a* = 1 / a is an isometry: it swaps 0 and +oo and is
   x |-> -x on the soft values, through the coding. *)
Let flip_code (u : Z) : Z :=
  match u with
  | inl _ => inr (inr tt)
  | inr (inl r) => inr (inl (- r)%R)
  | inr (inr _) => inl tt
  end.

Let flip_isometry u v : edist (flip_code u, flip_code v) = edist (u, v).
Proof.
case: u => [[]|[r|[]]]; case: v => [[]|[r'|[]]];
  rw !coprod_edistE /= ?coprod_edistE //=.
by rw !normed_edistE opprK addrC distrC.
Qed.

Let decode_star u : estar (prop_decode u)%:num = (prop_decode (flip_code u))%:num.
Proof.
case: u => [[]|[r|[]]] /=; rw /estar.
- by rw eqxx.
- rw gt_eqF ?lte_fin ?expR_gt0 // lt_eqF ?ltry //=.
  by rw expRN.
- by rw gt_eqF ?lt0y // eqxx.
Qed.

Lemma prop_dist_estar a b (a0 : 0 <= estar a%:num) (b0 : 0 <= estar b%:num) :
  prop_dist (mkprop a0) (mkprop b0) = prop_dist a b.
Proof.
have ea : mkprop a0 = prop_decode (flip_code (prop_code a)).
  by apply/val_inj; have := decode_star (prop_code a); rw prop_codeK.
have eb : mkprop b0 = prop_decode (flip_code (prop_code b)).
  by apply/val_inj; have := decode_star (prop_code b); rw prop_codeK.
rw ea eb -prop_edistE (prop_decode_isometry (flip_code _) (flip_code _)).
by rw flip_isometry prop_distE.
Qed.

(* Prop is complete, as the image of the complete space 1 + R + 1 under an
   isometry. *)
Lemma prop_complete : complete_space (prop R).
Proof.
move=> F FF Fc.
have cZ : complete_space Z.
  apply: coprod_complete; first exact: unit_complete.
  by apply: coprod_complete; [exact: completeType_complete|exact: unit_complete].
apply: (complete_isometry _ prop_decode_isometry cZ Fc).
by apply: filterS filterT => a _; exists (prop_code a) => //; rw prop_codeK.
Qed.

HB.instance Definition _ := isPointed.Build (prop R) (1%:E%:nng : prop R).
HB.instance Definition _ := Uniform_isComplete.Build (prop R)
  (complete_space_cvg prop_complete).

End prop_space.
