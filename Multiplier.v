(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              July 1st 1995                               *)
(*                                                                          *)
(****************************************************************************)
(****************************************************************)
(*      Proof of a multiplier circuit                           *)
(*      C. Paulin-Mohring, June 95                              *)
(****************************************************************)
(*      The Multiplier proof                                    *)
(****************************************************************)

Require Import Arith.
Require Import Peano_dec.
Require Import Bool.
Require Import Zerob.
Require Import IfProp.

Require Import Streams.
Require Import Circ.

(* Definition of each combinational part of the circuit *)

Definition Mux (b : bool) (n m : nat) : nat :=
  match b return nat with
  | true => n
  | false => m
  end.

(* Extra lemmas *)

Lemma pred_SO : forall n : nat, pred n = 0 -> n <> 0 -> n = 1.
simple destruct n; auto with v62.
intros H1 H2; elim H2; auto with v62.
Qed.

Lemma plus_mult_pred : forall n m : nat, n <> 0 -> pred n * m + m = n * m.
simple destruct n; simpl in |- *; intros;
 [ elim H; trivial with v62 | auto with v62 ].
Qed.

(* The updating function *)

Definition upd1 (i1 r1 : nat) (r3 : bool) := Mux r3 i1 (pred r1).
Definition upd2 (i1 i2 r2 : nat) (r3 : bool) :=
  Mux r3 (Mux (zerob i1) 0 i2) (Mux (zerob i1) 0 i2 + r2).
Definition upd3 (i1 i2 r1 : nat) (r3 : bool) :=
  zerob (Mux r3 (pred i1) (pred (pred r1))) || zerob i2.

Lemma upd3_true :
 forall i1 i2 r1 : nat, upd3 i1 i2 r1 true = zerob (pred i1) || zerob i2.
trivial with v62.
Qed.

Lemma upd3_false :
 forall i1 i2 r1 : nat,
 upd3 i1 i2 r1 false = zerob (pred (pred r1)) || zerob i2.
trivial with v62.
Qed.

Record TR : Set := reg {reg1 : nat; reg2 : nat; reg3 : bool}.

Record TI : Set :=  {in1 : nat; in2 : nat}.

Record TO : Set := out {res : nat; done : bool}.

Definition update (i : TI) (r : TR) : TR :=
  reg (upd1 (in1 i) (reg1 r) (reg3 r))
    (upd2 (in1 i) (in2 i) (reg2 r) (reg3 r))
    (upd3 (in1 i) (in2 i) (reg1 r) (reg3 r)).

Definition output (i : TI) (r : TR) : TO := out (reg2 r) (reg3 r).

Section Multiplier_circuit.

Variable ri1 ri2 : nat.
Definition init : TR := reg ri1 ri2 true.

Definition circ_mult : Str TI -> Str TO := CIRC _ _ _ output update init.

Variable i0 : Str TI.
Definition X := in1 (HD _ i0).
Definition Y := in2 (HD _ i0).
Definition XY := Build_TI X Y.

Lemma nth_i0_O : XY = NTH _ i0 0.
replace (NTH _ i0 0) with (HD _ i0).
unfold XY, X, Y in |- *; elim (HD _ i0); trivial with v62.
trivial with v62.
Qed.
Hint Resolve nth_i0_O.

Definition stable (n : nat) : Prop :=
  between (fun q : nat => XY = NTH _ i0 q) 0 n.
Hint Unfold stable.

Lemma stable_O : stable 0.
auto with v62.
Qed.
Hint Resolve stable_O.

Lemma stable_S : forall n : nat, stable (S n) -> stable n.
intros n H; inversion H; auto with v62.
Qed.
Hint Immediate stable_S.

Lemma stable_Sn : forall n : nat, stable (S n) -> XY = NTH _ i0 n.
intros n H; inversion H; trivial with v62.
Qed.
Hint Immediate stable_Sn.

Definition Q (n : nat) (o : TO) : Prop :=
  stable n -> n <> 0 -> done o = true -> res o = X * Y.

Definition InvM (n : nat) (r : TR) : Prop :=
  stable n ->
  IfProp (n <> 0 -> reg2 r = X * Y)
    (pred (reg1 r) <> 0 /\ X <> 0 /\ pred (reg1 r) * Y + reg2 r = X * Y)
    (reg3 r).

Lemma InvM_init : InvM 0 init.
red in |- *; intro; unfold reg3 in |- *; simpl in |- *.
left; simple destruct 1; auto with v62.
Qed.

Lemma InvM_stable :
 forall (n : nat) (r : TR),
 InvM n r ->
 Q n (output (NTH _ i0 n) r) /\ InvM (S n) (update (NTH _ i0 n) r).

split.
(* Proof of (Q n (output (Nth i0 n) r)) *)
red in |- *; simpl in |- *.
intros H0 H1 H2.
elim (Iftrue_inv _ _ _ (H H0)); auto with v62.

(* Proof of (InvM (S n) (update (Nth i0 n) r)) *)
red in |- *; simpl in |- *; intro.
replace (NTH _ i0 n) with XY; simpl in |- *.
(* Proof of (Nth i0 n)=XY *) 
2: auto with v62.
(* Cases on the value of (reg3 r) *)
elim H; simpl in |- *; intros.
(* Proof that (stable n) *)
3: auto with v62.
(* Case (reg3 r)=true *)
rewrite upd3_true.
(* Case analysis wether X=0 *)
case X.
(* X=0 *)
simpl in |- *; auto with v62.
(* X'<>0 *)
(* Case analysis wether Y=0 *)
intro X'; case Y; simpl in |- *.
(* Y = O *)
rewrite orb_b_true; auto with v62.
(* Y=(S Y')<>0 *)
(* Case analysis wether X'=0 *)
intro Y'; case X'; simpl in |- *.
(* X'=O *)
auto with v62.
(* X' = (S X'') <> 0 *)
intro X''.
right; split; [ auto with v62 | split ].
auto with v62.
apply eq_S; elim plus_n_Sm; elim plus_n_Sm; auto with v62.
(* Case (reg3 r)=false *)
rewrite upd3_false.
case H1; clear H1; intros.
case H2; clear H2; intros.
rewrite (zerob_false_intro X); trivial with v62; simpl in |- *.
(* Case analysis whether Y=0 *)
generalize H3; clear H3; case Y; simpl in |- *.
(* Y=O *)
do 3 elim mult_n_O; rewrite orb_b_true; auto with v62.
(* Y=(S Y') *)
intro Y'; elim (eq_nat_dec (pred (pred (reg1 r))) 0); intro H3.
(* (pred (pred (reg1 r))=O *)
rewrite H3; simpl in |- *.
rewrite (pred_SO (pred (reg1 r))); trivial with v62; simpl in |- *.
elim plus_n_O; auto with v62.
(* (pred (pred (reg1 r)))<>O *)
intros; rewrite zerob_false_intro; trivial with v62; simpl in |- *.
right; intros.
split; trivial with v62.
split; trivial with v62.
elim H4.
replace (S (Y' + reg2 r)) with (S Y' + reg2 r); trivial with v62.
rewrite plus_assoc.
rewrite (plus_mult_pred (pred (reg1 r)) (S Y')); auto with v62.
Qed.

Theorem circ_mult_proof :
 forall n : nat,
 stable n ->
 n <> 0 ->
 done (NTH _ (circ_mult i0) n) = true -> res (NTH _ (circ_mult i0) n) = X * Y.
exact
 (Circ_property _ _ _ output update i0 init Q InvM InvM_init InvM_stable).
Qed.


(* 
   Additional property:
   Computation is done exactly after the following [iter_nb] of steps.
   (P.Letouzey 23 nov 2001) 
*)

Definition iter_nb := if zerob X || zerob Y then 1 else X. 

Lemma iter_nb_non_O : iter_nb <> 0.
unfold iter_nb in |- *.
case X; case Y; simpl in |- *; auto.
Qed.

Lemma iter_nb_1 : 1 = iter_nb -> zerob (pred X) || zerob Y = true.
unfold iter_nb in |- *.
case X; case Y; simpl in |- *; auto.
intros; rewrite orb_comm; simpl in |- *; auto.
intros; inversion H; simpl in |- *; auto.
Qed.

Lemma iter_nb_lt_1 : 1 < iter_nb -> 1 < X /\ Y <> 0.
unfold iter_nb in |- *.
case X; case Y; simpl in |- *; split; intros; auto with arith; absurd (1 < 1);
 auto with arith.
Qed.

Lemma iter_nb_general : X <> 0 -> Y <> 0 -> iter_nb = X.
unfold iter_nb in |- *.
case X; case Y; simpl in |- *; intros; auto with arith; absurd (0 = 0);
 auto with arith.
Qed.

Definition Q' (n : nat) (o : TO) : Prop :=
  stable n -> n = iter_nb -> done o = true.

Definition InvM' (n : nat) (r : TR) : Prop :=
  stable n ->
  (n = 0 -> reg3 r = true) /\
  (n <> 0 ->
   (n = iter_nb -> reg3 r = true) /\
   (n < iter_nb ->
    reg3 r = false /\
    pred (reg1 r) <> 0 /\ 1 < X /\ Y <> 0 /\ X = n + pred (reg1 r))).
	

Lemma InvM'_init : InvM' 0 init.
red in |- *; intro; unfold reg3 in |- *; simpl in |- *.
split; auto.
intro H0; elim H0; auto.
Qed.

Require Import Compare_dec.

Lemma InvM'_stable :
 forall (n : nat) (r : TR),
 InvM' n r ->
 Q' n (output (NTH _ i0 n) r) /\ InvM' (S n) (update (NTH _ i0 n) r).
split.
(* Proof of (Q' n (output (Nth i0 n) r)) *)
red in |- *; simpl in |- *.
intro H0.
elim H; simpl in |- *; auto.
intros.
elim H2; simpl in |- *; auto.
rewrite H3; exact iter_nb_non_O.
(* Proof of (InvM (S n) (update (Nth i0 n) r)) *)
red in |- *; simpl in |- *; intro.
replace (NTH _ i0 n) with XY; simpl in |- *.
(* Proof of (Nth i0 n)=XY *) 
2: auto with v62.
(* Cases on the value of (reg3 r) *)
split; intro A; [ inversion A | clear A ].
elim H; simpl in |- *.
(* Proof that (stable n) *)
2: auto with v62.
case (eq_nat_dec n 0); intro A.
rewrite A; simpl in |- *.
intros; clear H2; split; auto; intros.
rewrite H1; auto.
rewrite upd3_true.
apply iter_nb_1; auto.
rewrite H1; auto.
rewrite upd3_true.
elim (iter_nb_lt_1 H2); intros.
rewrite (zerob_false_intro Y); simpl in |- *; auto.
cut (pred X <> 0); intros.
rewrite (zerob_false_intro (pred X)); simpl in |- *; auto.
rewrite <- S_pred with (m := 1); auto.
red in |- *; generalize H3; case X; simpl in |- *; intros; auto.
absurd (1 < 0); auto with arith.
rewrite H6 in H5; absurd (1 < 1); auto with arith.
intros.
clear H1.
elim H2; auto; intros; clear H2.
elim (le_lt_dec iter_nb n); intro a.
split; intros.
rewrite <- H2 in a; absurd (S n <= n); auto with arith.
absurd (S n <= n); auto with arith.
apply lt_le_trans with iter_nb; auto with arith. 
elim H3; clear H3; auto; intros.
inversion_clear H3.
inversion_clear H5.
inversion_clear H6.
cut (X <> 0);
 [ intros
 | red in |- *; intro B; rewrite B in H3; absurd (1 < 0); auto with arith ].
rewrite iter_nb_general in a; auto.
rewrite iter_nb_general; auto.
rewrite H2; simpl in |- *; rewrite upd3_false.
rewrite (zerob_false_intro Y); simpl in |- *; auto.
assert (B := plus_Snm_nSm n 0); rewrite plus_comm in B; simpl in B.
rewrite B.
split; intro b; rewrite H7 in b.
rewrite <- (plus_reg_l _ _ _ b); auto.
assert (C := plus_lt_reg_l _ _ _ b).
cut (forall a b : nat, S (a + b) = a + S b); intros.
rewrite H8.
rewrite <- S_pred with (m := 1); auto.
cut (pred (pred (reg1 r)) <> 0); intros.
rewrite zerob_false_intro; simpl in |- *; auto.
red in |- *; intros.
rewrite (S_pred _ _ C) in C.
rewrite H9 in C; absurd (1 < 1); auto with arith.
simpl in |- *; auto.
Qed.

Theorem circ_mult_proof' :
 stable iter_nb -> done (NTH _ (circ_mult i0) iter_nb) = true.
intros.
apply
 (Circ_property _ _ _ output update i0 init Q' InvM' InvM'_init InvM'_stable);
 auto.
Qed.

Theorem circ_mult_proof'' :
 stable iter_nb -> res (NTH _ (circ_mult i0) iter_nb) = X * Y.
intros; apply circ_mult_proof; auto.
exact iter_nb_non_O.
apply circ_mult_proof'; auto.
Qed.

End Multiplier_circuit.

Section Constant_Str.

(* We define a constant Input stream. *) 

Variable a b : nat.

Definition cst_TI := STRIT _ _ (fun _ => Build_TI a b) (fun _ => tt) tt.

Lemma tl_cst_TI_is_cst_TI : TL _ cst_TI = cst_TI.
unfold cst_TI in |- *.
rewrite Tl_StrIt; auto.
Qed.

Lemma nthtl_cst_TI_is_cst_TI : forall n : nat, NTHTL _ cst_TI n = cst_TI.
induction n; simpl in |- *; auto.
rewrite IHn; apply tl_cst_TI_is_cst_TI.
Qed.

Lemma cst_TI_is_cst : forall n : nat, NTH _ cst_TI n = Build_TI a b.
intros.
unfold NTH in |- *.
rewrite nthtl_cst_TI_is_cst_TI; simpl in |- *; auto.
Qed.

Lemma cst_TI_is_stable : forall n : nat, stable cst_TI n.
induction n; simpl in |- *; auto.
left.
right; auto.
rewrite cst_TI_is_cst; simpl in |- *; auto.
Qed.

(* So we have the following alternate definition for mult: *)

Definition mult' :=
  let i := cst_TI in res (NTH _ (circ_mult 0 0 i) (iter_nb i)).

Theorem mult'_is_mult : mult' = a * b.
unfold mult' in |- *.
intros.
rewrite circ_mult_proof''; auto.
apply cst_TI_is_stable.
Qed.

End Constant_Str.

Extraction "circmult.ml" mult'.