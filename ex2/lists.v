Set Implicit Arguments.
Require Import Lists.List.
Import ListNotations.
Require Import List.
Require Import Arith.
Require Import Lia.
Import Nat.

Print list.
Print rev.



(* Q1. Define is_sorted.  (returns a Prop.)  *)  

Inductive is_sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : is_sorted R []
| sorted_singleton : forall x, is_sorted R [x]
| sorted_cons : forall x y l, 
  R x y -> 
  is_sorted R (y :: l) -> 
  is_sorted R (x :: y :: l).

(* Show that this list is sorted. *)
Lemma warm_up : is_sorted le [3;5;9].
Proof.
  apply sorted_cons. lia.
  apply sorted_cons. lia.
  apply sorted_singleton.
Qed.

(* Q2. Prove that an ascending list of nat, when reversed, 
 *     becomes a descending list. *)

Lemma aux_rev_lemma : forall (A : Set) (l : list A) R a b,
                        is_sorted R (l ++ [a]) -> R a b -> 
                        is_sorted R (l ++ [a;b]).
Proof.
  intros.
  (* intros A R l a b Hsorted Rab. *)
  induction l as [| x xTail IH].
  - simpl in *. (* [] ++ [a] = [a], so goal becomes is_sorted R [a; b] *)
    apply sorted_cons. 
    + assumption. 
    + apply sorted_singleton.
  - simpl in *. (* l = x :: xTail, so l ++ [a] = x :: xTail ++ [a] *)
    destruct xTail as [| y yTail].
    + inversion H; subst.
      apply sorted_cons. 
      * assumption.
      * apply sorted_cons. 
        -- assumption. 
        -- apply sorted_singleton.
    + inversion H; subst.
      apply sorted_cons. 
      * assumption.
      * apply IH. assumption.
Qed.

(*     Don't forget to use the _hint_ when proving it. *)

Theorem rev_asc_desc :  forall l, 
                        is_sorted le l -> is_sorted ge (rev l).
Proof.
  intros l H.
  induction H.
  - simpl. constructor.
  - simpl. constructor.
  - simpl in *.
    rewrite <- app_assoc.
    apply aux_rev_lemma. 
    + assumption.
    + assumption.
Qed.
