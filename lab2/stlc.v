Definition native_bool := bool.


Inductive Var : Set := x | y | z.

Inductive TyBase : Set := int | bool.

Inductive Ty : Set :=
  | Base : TyBase -> Ty
  | Arrow : Ty -> Ty -> Ty.

Inductive Term : Set :=
  | TVar : Var -> Term
  | Abs : (Var * Ty) -> Term -> Term
  | App : Term -> Term -> Term.

(* Equality *)
Definition eq_var v1 v2 := match v1, v2 with
  | x, x => true  | y, y => true  | z, z => true
  | _, _ => false 
end.

Definition eq_tybase t1 t2 := match t1, t2 with
  | int, int => true    | bool, bool => true
  | _, _ => false
end.

Open Scope bool_scope.

Fixpoint eq_ty t1 t2 := match t1, t2 with
  | Base b1,
    Base b2         => eq_tybase b1 b2
  | Arrow t'1 s'1,
    Arrow t'2 s'2   => (eq_ty t'1 t'2) && (eq_ty s'1 s'2)
  | _, _ => false
end.


(* Syntax sugar *)
Notation "\ v : t , e" := (Abs (v, t) e)
  (at level 70, v at level 0, right associativity, only parsing).
Notation "'λ' v : t , e" := (Abs (v, t) e)
  (at level 70, v at level 0, right associativity, format "'λ' v  :  t ,  e").
Notation "e1 @ e2" := (App e1 e2) (at level 65).

Check \x : Base int , TVar y @ TVar z.
Check \x : Base int , (TVar y @ TVar z).
Check (\x : Base int , TVar y) @ TVar z.
Check TVar x @ \x : Base int, \y : Base bool, TVar y.


Definition Valuation := Var -> Ty.


Module Typecheck.

Inductive Result :=
  | Ok : Ty -> Result
  | Mismatch : Term -> Ty -> Ty -> Result
  | ExpectedArrow : Term -> Ty -> Result.

(* 
  This is a recursive function definition in Coq, a functional proof assistant.
  The function is named 'typecheck', and its job is to determine the type of a given lambda calculus term
  (based on Simply Typed Lambda Calculus - STLC), by recursively analyzing its structure.
*)
Fixpoint typecheck (e : Term) (env : Valuation) : Result :=

  (* 
    'match e with ... end' is a pattern-matching construct.
    It inspects the structure of the term 'e' and performs different actions
    based on whether the term is a variable, an abstraction (function), or an application (function call).
    
    The type 'Term' is defined with three constructors:
      - TVar v     - a variable (e.g., x)
      - Abs (v, t) body - a lambda abstraction: a function taking variable 'v' of type 't'
      - App e1 e2  - an application of function 'e1' to argument 'e2'

    The environment 'env' is a function from variables to types - this represents which type each variable has in the current context.
  *)
  match e with

  (* --- CASE 1: VARIABLE --- *)
  | TVar v =>
      (*
        If the term 'e' is a variable (TVar v),
        we look up the type of this variable in the current environment.
        The environment is a function (env : Var -> Ty), so 'env v' gives us the type of variable v.

        We return this as 'Ok (env v)', wrapped in a constructor 'Ok' from the 'Result' type,
        indicating that typechecking succeeded.
      *)
      Ok (env v)

  (* --- CASE 2: ABSTRACTION --- *)
  | Abs (v, t1) body =>
      (*
        If the term is a lambda abstraction, like \v : t1. body,
        this means it's a function with:
          - a parameter 'v' of type 't1'
          - a body expression 'body' which is evaluated in an extended environment.

        To typecheck a function, we need to:
        1. Extend the environment to map 'v' to its declared type 't1'.
        2. Typecheck the body using this new environment.
        3. If the body has type t2, then the full abstraction has type (t1 -> t2).

        The environment is extended using a 'fun u => ...' function:
        This says: for any variable 'u', if it is equal to 'v', return 't1';
        otherwise, use the original environment (env u).
      *)
      match typecheck body (fun u => if eq_var u v then t1 else env u) with
      | Ok t2 =>
          (*
            If the body typechecks successfully and has type 't2',
            then the entire abstraction is a function from t1 to t2:
            we return Ok (Arrow t1 t2).
          *)
          Ok (Arrow t1 t2)

      | Mismatch e' t_expected t_actual =>
          (*
            If there was a type mismatch while checking the body,
            we propagate that mismatch as-is.
            This includes:
              - the subexpression e' that caused the error,
              - the type we expected,
              - the type we actually got.
          *)
          Mismatch e' t_expected t_actual

      | ExpectedArrow e' t =>
          (*
            If we expected a function type in the body but got something else,
            we propagate that error as well.
          *)
          ExpectedArrow e' t
      end

  (* --- CASE 3: APPLICATION --- *)
  | App e1 e2 =>
      (*
        If the term is an application (e1 e2), meaning we apply function e1 to argument e2.

        We need to:
        1. Typecheck e1 (the function)
        2. Typecheck e2 (the argument)
        3. Check that e1 has a function type, say t_arg -> t_res
        4. Check that the argument e2 has type t_arg
        5. If they match, return Ok t_res
        6. Otherwise, return an appropriate error
      *)

      match typecheck e1 env with

      | Ok (Arrow t_arg t_res) =>
          (*
            If e1 successfully typechecks and is a function from t_arg to t_res,
            now we check e2, the argument expression.
          *)
          match typecheck e2 env with
          | Ok t2 =>
              (*
                If e2 successfully typechecks and has type t2,
                we now check whether t2 matches the expected type t_arg
                (i.e., does the argument match the input type of the function?)

                eq_ty t_arg t2 returns a boolean:
                  - true if the types are equal,
                  - false if they are not.

                If they match: we return Ok t_res - the result type of the function.
                If they don’t: we return Mismatch with the argument expression e2,
                the expected type t_arg, and the actual type t2.
              *)
              if eq_ty t_arg t2 then Ok t_res
              else Mismatch e2 t_arg t2

          | Mismatch e t_expected t_actual =>
              (* Propagate any mismatch error encountered during checking of e2 *)
              Mismatch e t_expected t_actual

          | ExpectedArrow e t =>
              (* Propagate any non-function-type usage error encountered during checking of e2 *)
              ExpectedArrow e t
          end

      | Ok t1 =>
          (*
            If e1 typechecked but its type t1 is not a function (i.e., not of the form Arrow _ _),
            then this is a misuse: trying to apply a non-function.
            So we return ExpectedArrow with the function part e1 and its non-function type t1.
          *)
          ExpectedArrow e1 t1

      | Mismatch e t_expected t_actual =>
          (* Propagate type mismatch error from typechecking the function part e1 *)
          Mismatch e t_expected t_actual

      | ExpectedArrow e t =>
          (* Propagate error indicating that e1 was expected to be a function type but wasn't *)
          ExpectedArrow e t
      end
  end.


(* Examples *)

Definition env : Valuation := fun v => Base int.

Compute typecheck (\x : Base bool, TVar y @ TVar x) env.
(* ExpectedArrow (TVar y) (Base int) *)

Compute typecheck
  (\x : Arrow (Base bool) (Base int), TVar x @ TVar y) env.
(* Mismatch (TVar y) (Base bool) (Base int) *)

Compute typecheck
  (\x : Arrow (Base int) (Base bool), TVar x @ TVar y) env.
(* Ok (Arrow (Arrow (Base int) (Base bool)) (Base bool)) *)
(* ⟹   (int -> bool) -> bool  *)


End Typecheck.
