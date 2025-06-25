Set Implicit Arguments.
Require Import Coq.Program.Equality.
Require Import Lia.


Inductive var := a | b | n | x | y.

Scheme Equality for var.

Definition op := nat -> nat -> nat.
  
Inductive expr :=
  expr_var : var -> expr
| expr_num : nat -> expr
| expr_op : expr -> op -> expr -> expr.

Inductive cmd :=
  assign : var -> expr -> cmd
| seq : cmd -> cmd -> cmd
| skip : cmd
| if_then_else : expr -> cmd -> cmd -> cmd
| while : expr -> cmd -> cmd
| assume : expr -> cmd.

Definition state := var -> nat.

Fixpoint sem (e : expr) (s : state) :=
  match e with
  | expr_var v => s v
  | expr_num m => m
  | expr_op e1 op e2 => op (sem e1 s) (sem e2 s)
  end.


(* -- Defining the program euclid in IMP -- *)
Require Import Arith.
Import Nat.

(* some operators *)
Definition gt01 n m := if gt_dec n m then 1 else 0.
Definition ne01 n m := if eq_dec n m then 0 else 1.

(* This notation will shorten things a bit *)
Notation "$ v" := (expr_var v) (at level 7, format "$ v").

Definition euclid_body :=
    seq (assume (expr_op $a ne01 $b))
        (if_then_else (expr_op $a gt01 $b)
                      (assign a (expr_op $a sub $b))
                      (assign b (expr_op $b sub $a))).


(* ----------------------- *)

Inductive sos   : (state * cmd) -> (state * cmd) -> Prop :=
(* assign *)
  | sos_assign : forall s v e,
      sos (s, assign v e) ((fun x => if var_eq_dec x v then sem e s else s x), skip)
(* seq *)
  | sos_seq : forall s s' c1 c1' c2,
      sos (s, c1) (s', c1') -> sos (s, seq c1 c2) (s', seq c1' c2)
  | sos_seq_skip : forall s c2,
      sos (s, seq skip c2) (s, c2)
(* if_then_else *)
  | sos_if_true  : forall s e c1 c2,
      sem e s <> 0 -> sos (s, if_then_else e c1 c2) (s, c1)
  | sos_if_false : forall s e c1 c2,
      sem e s = 0 -> sos (s, if_then_else e c1 c2) (s, c2)
(* while *)
  | sos_while_true : forall s e c,
      sem e s <> 0 -> sos (s, while e c) (s, seq c (while e c))
  | sos_while_false : forall s e c,
      sem e s = 0 -> sos (s, while e c) (s, skip)      
(* assume *)
  | sos_assume_true : forall s e,
      sem e s <> 0 -> sos (s, assume e) (s, skip).


Inductive step : state -> state -> Prop :=
  | step_a : forall s,
      s a > s b ->
      step s (fun x => if var_eq_dec x a then s a - s b else s x)
  | step_b : forall s,
      s a < s b ->
      step s (fun x => if var_eq_dec x b then s b - s a else s x).

  (* tc definitions from lab 5, changed to match step and sos *) 
  Inductive tc' (R: state -> state -> Prop): state -> state -> Prop :=
    tc'_refl : forall s, (tc' R) s s
  | tc'_step : forall s u t, R s u -> (tc' R) u t -> (tc' R) s t.

(* our implementation of gcd (eucalid version *)  
Inductive euclid : nat -> nat -> nat -> Prop :=
  stop    : forall z, euclid z z z
| step_a' : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
| step_b' : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z. 

Lemma step_correctness : forall a0 b0 s s' , 
                             s a = a0 -> 
                             s b = b0 -> 
                             (tc' step) s s' -> 
                             s' a = s' b ->
                                 euclid a0 b0 (s' a).
Proof.
intros a0 b0 s s' Ha Hb Htc.
  generalize dependent a0.
  generalize dependent b0.
  induction Htc as [| s u t Hstep Htc' IH]; intros b0 a0 Ha Hb Heq.
  - (* base case a = b = z *)
    subst. rewrite Heq. apply stop.

  - (* inductive step *)
    destruct Hstep.

    + (* case a > b, so a := a - b *)
      apply step_a'. subst.
      assumption.
      apply IH.
      * (* a0' := s a - s b *)
        simpl. subst. reflexivity.
      * (* b0' := s b *)
        simpl. subst. reflexivity.
      * assumption.
      
    + (* case a < b, so b := b - a *)
      apply step_b'. subst. assumption.
      apply IH.
      * (* a0 := s a *)
        simpl. subst. lia.
      * (* b0 := s b - s a *)
        simpl. assumption.
      * assumption. 
Qed.
