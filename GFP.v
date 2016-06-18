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
(*	  	Proof of a multiplier circuit			*)
(*	  	C. Paulin-Mohring, June 95			*)
(****************************************************************)
(*	  	GFP.v						*)
(*	  	Greatest Fixed point of monotonic operators	*)
(****************************************************************)

Section Greatest_Fixpoints.

Variable F : Set -> Set.

Variable FMON : forall X Y : Set, (X -> Y) -> F X -> F Y.
Notation Fmon := (FMON _ _) (only parsing).

Inductive nu : Set :=
    CoIt : forall X : Set, (X -> F X) -> X -> nu.

Definition Out (m : nu) : F nu :=
  let (X, f, x) return (F nu) := m in FMON _ _ (CoIt X f) (f x).

Definition In (x : F nu) : nu := CoIt (F nu) (FMON _ _ Out) x.

Definition CoRec (X : Set) (f : X -> F (nu + X)) (x : X) : nu :=
  CoIt (nu + X)
    (fun z : nu + X =>
     match z return (F (nu + X)) with
     | inl n => FMON _ _ inl (Out n)
     | inr y => f y
     end) (inr nu x).

End Greatest_Fixpoints.