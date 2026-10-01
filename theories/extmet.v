(* Extended (pseudo)metric spaces: distances in [0, +oo] (paper, Sect. 2). *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets reals constructive_ereal ereal.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure separation_axioms urysohn.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module exp.
From ExtMetQLL Require Import analysis_extras.

(**md**************************************************************************)
(* # Extended pseudometric spaces                                             *)
(*                                                                            *)
(* An extended pseudometric space is a MathComp Analysis pseudoMetricType R   *)
(* and an extended metric space an extMetricType R (analysis_extras.v).       *)
(* The extended distance is Analysis's edist (urysohn.v), the infimum of      *)
(* the radii of the balls containing both points; it is +oo between points    *)
(* of different "galaxies", which are clopen.                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*     r.-elipschitz f == edist (f x, f y) <= r * edist (x, y), for           *)
(*                          r : {nonneg \bar R}                               *)
(*     econtraction r f == r.-elipschitz f, for r : {itv \bar R & `[0, 1[}    *)
(*        nonexpansive f == 1.-elipschitz f (short map)                       *)
(*           tensor X Y == X ⊗ Y, the product with the sum distance           *)
(*                          (X * Y carries Analysis's max distance, i.e. the  *)
(*                          cartesian product of CExtMet)                     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* r-Lipschitz maps for an extended scalar r in [0, +oo] (with 0 * +oo = 0),
   covering the sensitivities of the paper; Analysis's [k.-lipschitz] only
   exists for normed modules and real k (see [lipschitzE]). *)
Section ELipschitz.
Context {R : realType} (X Y : pseudoMetricType R).

Definition elipschitz (r : {nonneg \bar R}) (f : X -> Y) :=
  forall x x', edist (f x, f x') <= r%:num * edist (x, x').

(* Contractions: the constant lives in [0, 1[; interval inference widens it
   to a scalar in [0, +oo]. *)
Definition econtraction (r : {itv \bar R & `[0, 1[}) (f : X -> Y) :=
  elipschitz (r%:num)%:nng f.

(* Morphisms of ExtMet: short maps. *)
Definition nonexpansive (f : X -> Y) := elipschitz 1%:E%:nng f.

Lemma nonexpansiveP (f : X -> Y) :
  nonexpansive f <-> forall x x', edist (f x, f x') <= edist (x, x').
Proof. by split=> h x x'; move: (h x x'); rw /= mul1e. Qed.

Lemma elipschitz_le (r s : {nonneg \bar R}) (f : X -> Y) :
  r%:num <= s%:num -> elipschitz r f -> elipschitz s f.
Proof.
by move=> rs hf x x'; apply: le_trans (hf x x') _; exact: lee_wpmul2r.
Qed.

End ELipschitz.

Notation "r .-elipschitz f" := (elipschitz r f)
  (at level 2, format "r .-elipschitz  f") : type_scope.

Lemma elipschitz_comp {R : realType} (X Y Z : pseudoMetricType R)
    (r s : {nonneg \bar R}) (f : X -> Y) (g : Y -> Z) :
  r.-elipschitz f -> s.-elipschitz g -> (s%:num * r%:num)%:nng.-elipschitz (g \o f).
Proof.
move=> hf hg x x' /=; apply: le_trans (hg _ _) _; rw -muleA.
exact: lee_wpmul2l.
Qed.

Lemma nonexpansive_id {R : realType} (X : pseudoMetricType R) :
  nonexpansive (@id X).
Proof. by apply/nonexpansiveP. Qed.

Lemma nonexpansive_comp {R : realType} (X Y Z : pseudoMetricType R)
    (f : X -> Y) (g : Y -> Z) :
  nonexpansive f -> nonexpansive g -> nonexpansive (g \o f).
Proof.
move=> /nonexpansiveP hf /nonexpansiveP hg; apply/nonexpansiveP => x x'.
exact: le_trans (hg _ _) (hf _ _).
Qed.

Section NormedLipschitz.
Context {R : realType} (V W : normedModType R).

Lemma lipschitzE (k : {nonneg R}) (f : V -> W) :
  (k%:num).-lipschitz f <-> (k%:num%:E)%:nng.-elipschitz f.
Proof.
have kE : (k%:num%:E)%:nng%:num = k%:num%:E :> \bar R by [].
split=> [h x x' | h [x x'] _] /=.
- by rw kE !normed_edistE -EFinM lee_fin; exact: (h (x, x')).
- by move: (h x x'); rw kE !normed_edistE -EFinM lee_fin.
Qed.

End NormedLipschitz.

(* The monoidal product X ⊗ Y: the l^1 product, i.e. the product set with
   the (untruncated) sum distance.  (X * Y carries Analysis's max distance,
   the cartesian product of CExtMet, i.e. the l^oo product.) *)
Definition itv1 {R : realType} : {itv \bar R & `[1, +oo[} :=
  ext_widen_itv (1%:E)%:itv.

Notation tensor := (lp_prod itv1).

Lemma tensor_edistE {R : realType} (X Y : pseudoMetricType R) (u v : tensor X Y) :
  edist (u, v) = edist (u.1, v.1) + edist (u.2, v.2).
Proof.
rw lp_prod_edistE (_ : itv1%:num = 1%:E) // lp_distE invr1.
by rw !poweRe1 ?adde_ge0 ?edist_ge0.
Qed.
