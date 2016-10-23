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
(*              Circ.v                                          *)
(*              Representation of Circuits                      *)
(****************************************************************)

Require Import GFP.
Require Import Streams.

Section Circuits.

Variable TI TR TO : Set.

Variable output : TI -> TR -> TO.
Variable update : TI -> TR -> TR.

Definition CIRC (ri : TR) (si : Str TI) : Str TO :=
  STRCOIT _ _
    (fun x : Str TI * TR =>
     let (s, r) return (TO * (Str TI * TR)) := x in
     (output (HD _ s) r, (TL _ s, update (HD _ s) r))) 
    (si, ri).
Let Circ := CIRC.

Theorem Hd_Circ :
 forall (r : TR) (si : Str TI), HD _ (Circ r si) = output (HD _ si) r.
trivial.
Qed.

Theorem Tl_Circ :
 forall (r : TR) (si : Str TI),
 TL _ (Circ r si) = Circ (update (HD _ si) r) (TL _ si).
trivial.
Qed.

Definition Reg : Str TI * TR -> TR.
simple destruct 1; trivial.
Defined.

Definition Input : Str TI * TR -> Str TI.
simple destruct 1; trivial.
Defined.

Section CircProof.
Variable i0 : Str TI.
Variable r0 : TR.
Variable P : nat -> TO -> Prop.

Variable inv : nat -> TR -> Prop.
Hypothesis inv_init : inv 0 r0.
Hint Resolve inv_init.

Let inv_aux (n : nat) (s : Str TO) : Prop :=
  exists r : TR, inv n r /\ s = Circ r (NTHTL _ i0 n).

Remark inv_aux_init : inv_aux 0 (Circ r0 i0).
exists r0; auto.
Qed.
Hint Resolve inv_aux_init.

Hypothesis
  inv_stable :
    forall (n : nat) (r : TR),
    inv n r ->
    P n (output (NTH _ i0 n) r) /\ inv (S n) (update (NTH _ i0 n) r).

Remark inv_aux_stable :
 forall (n : nat) (s : Str TO),
 inv_aux n s -> P n (HD _ s) /\ inv_aux (S n) (TL _ s).
simple induction 1; simple induction 1; intros.
rewrite H2; rewrite Tl_Circ; rewrite Hd_Circ.
elim (inv_stable n x); intros; trivial.
split; trivial.
exists (update (NTH _ i0 n) x); auto.
Qed.
Hint Resolve inv_aux_stable.

Theorem Circ_property : forall n : nat, P n (NTH _ (Circ r0 i0) n).
intro; apply All_Q_Nth with (Inv := inv_aux); auto.
Qed.

End CircProof.

End Circuits.

Notation Circ := (CIRC _ _ _) (only parsing).
(* <Warning> : Syntax is discontinued *)
