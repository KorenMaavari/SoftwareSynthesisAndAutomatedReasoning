Set Implicit Arguments.
Require Import Lists.List.
Import ListNotations.
Require Import Lia.

Print list.
Print rev.


(* Q1. Define `is_sorted`.  (should return a Prop.)  *)
Inductive is_sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : is_sorted R []
| sorted_singleton : forall x, is_sorted R [x]
| sorted_cons : forall x y l, R x y -> is_sorted R (y :: l) -> is_sorted R (x :: y :: l).


(* Show that this list is sorted. *)
Lemma warm_up : is_sorted le [3;5;9].
Proof.
  apply sorted_cons. lia.
  apply sorted_cons. lia.
  apply sorted_singleton.
Qed.


(* Q2. Prove that an ascending list of nat, when reversed, 
 *     becomes a descending list. *)

(*     Don't forget to use the _hint_ when proving it. *)

Theorem rev_asc_desc : ...