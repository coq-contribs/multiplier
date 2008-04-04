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
(*		        Proof of a multiplier circuit		*)
(*		        C. Paulin-Mohring, June 95		*)
(****************************************************************)
(*	                Streams.v			   	*)
(*			Representing Streams	        	*)
(****************************************************************)

Require Import GFP.

Section Streams.
Variable A : Set.

Let F (X : Set) := (A * X)%type.
Definition Fmon : forall X Y : Set, (X -> Y) -> F X -> F Y.
unfold F in |- *; intros.
split; case H0; auto with v62.
Defined.

Definition Str := nu F.

Definition STROUT : Str -> A * Str := Out F Fmon.
Let StrOut := STROUT.

Definition HD (s : Str) : A := fst (StrOut s).
Definition TL (s : Str) : Str := snd (StrOut s).

Let Hd := HD.
Let Tl := TL.

Definition STRCOIT : forall X : Set, (X -> A * X) -> X -> Str := CoIt F.
Let StrCoIt := STRCOIT.

Definition STRIT (X : Set) (h : X -> A) (t : X -> X) 
  (x : X) : Str := StrCoIt X (fun y : X => (h y, t y)) x.
Let StrIt := STRIT.

Lemma Hd_StrIt :
 forall (X : Set) (h : X -> A) (t : X -> X) (x : X), Hd (StrIt X h t x) = h x.
trivial with v62.
Qed.

Lemma Tl_StrIt :
 forall (X : Set) (h : X -> A) (t : X -> X) (x : X),
 Tl (StrIt X h t x) = StrIt X h t (t x).
trivial with v62.
Qed.

Fixpoint NTHTL (s : Str) (n : nat) {struct n} : Str :=
  match n return Str with
  | O => s
  | S p => Tl (NTHTL s p)
  end.
Let NthTl := NTHTL.

Definition NTH (s : Str) (n : nat) : A := Hd (NthTl s n).
Let Nth := NTH.

(* A generic principle to prove that the property Q n (Nthtl n s) holds for 
   any n *)

Section Invariant_Stream.

Variable s : Str.
Variable Inv : nat -> Str -> Prop.
Hypothesis Inv_init : Inv 0 s.
Hint Resolve Inv_init.

Section Generic.
Variable Q : nat -> Str -> Prop.
Hypothesis
  Inv_out : forall (n : nat) (s : Str), Inv n s -> Q n s /\ Inv (S n) (Tl s).

Theorem All_Q_Nthtl : forall n : nat, Q n (NthTl s n).
intro n.
cut (Inv n (NthTl s n)).
intro I; case Inv_out with (1 := I); trivial.
elim n; trivial with v62; intros.
simpl in |- *; case Inv_out with (1 := H); trivial.
Qed.
End Generic.

(* Principle to prove that the property Q n holds for the elements of s *)

Variable Q : nat -> A -> Prop.
Lemma All_Q_Nth :
 (forall (n : nat) (s : Str), Inv n s -> Q n (Hd s) /\ Inv (S n) (Tl s)) ->
 forall n : nat, Q n (Nth s n).
Proof All_Q_Nthtl (fun (n : nat) (s : Str) => Q n (Hd s)).

End Invariant_Stream.

(* Other lemma working on the implementation *)

Section Invariant_Implementation.
Variable X : Set.
Variable h : X -> A.
Variable t : X -> X.
Variable x : X.
Variable Inv : nat -> X -> Prop.
Hypothesis Inv_init : Inv 0 x.
Hint Resolve Inv_init.

Section Nth_Implementation.
Variable Q : nat -> A -> Prop.
Hypothesis
  Inv_out : forall (n : nat) (x : X), Inv n x -> Q n (h x) /\ Inv (S n) (t x).

Theorem All_Q_Nth_Imp : forall n : nat, Q n (Nth (StrIt X h t x) n).
intro n;
 apply
  All_Q_Nth
   with
     (Inv := fun (n : nat) (s : Str) =>
             exists2 x : X, s = StrIt X h t x & Inv n x).
exists x; auto.
simple destruct 1; simple destruct 1; intro.
rewrite H0; rewrite Hd_StrIt; rewrite Tl_StrIt.
elim (Inv_out n0 x0); trivial.
split; trivial.
exists (t x0); auto.
Qed.
End Nth_Implementation.

End Invariant_Implementation.

End Streams.

Notation StrOut := (STROUT _) (only parsing).
Notation Nth := (NTH _) (only parsing).
Notation NthTl := (NTHTL _) (only parsing).
Notation Hd := (HD _) (only parsing).
Notation Tl := (TL _) (only parsing).
Notation StrCoIt := (STRCOIT _ _) (only parsing).
Notation StrIt := (STRIT _ _) (only parsing).

(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)
(* <Warning> : Syntax is discontinued *)




