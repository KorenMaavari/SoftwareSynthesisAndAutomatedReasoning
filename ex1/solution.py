"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from syntax.lambda_typed import (
    parse, TypedExpr, is_grounded_expr,
    Id,            # Represents a variable name in the lambda expression.
    Int,
    Bool,
    Let,
    Lambda,
    App,
    VarDecl,
    Arrow,
    Primitive,
    TypeName,      # Represents any custom (non-primitive) type by name.
    TypeVar,
    LambdaType,    # The base class for all types in the lambda calculus.
    fresh_typevar
)

# It allows us to describe variables that are dictionaries (i.e., key-value mappings).
from typing import Dict


class TypeMismatchError(TypeError):
    pass


class InsufficientAnnotationsError(TypeError):
    pass


# === Type Aliases for Readability ===

# Substitution: maps type variable IDs to actual types.
# For example: {3: Primitive.INT, 5: Arrow(Primitive.BOOL, Primitive.INT)}
Substitution = Dict[int, LambdaType]

# Type Environment: maps variable names (strings) to their corresponding types.
# For example: {'x': Primitive.INT, 'f': Arrow(Primitive.INT, Primitive.BOOL)}
TypeEnv = Dict[str, LambdaType]

# ------------------------------------------------------------------------------------
#                          UNIFICATION ENGINE (Core Type Logic)
# ------------------------------------------------------------------------------------

def occurs_in(tv: TypeVar, t: LambdaType) -> bool:
    """
    Helper function for the occurs check: prevents creating infinite (cyclic) types.
    It checks if a type variable (tv) appears *within* the given type (t).
    This is needed to avoid cases like T = T -> T, which are invalid in simple types.
    """
    match t:
        case TypeVar(id):
            return tv.id == id
        case Arrow(arg, ret):
            # Recursively check the argument and return types
            return occurs_in(tv, arg) or occurs_in(tv, ret)
        case _:
            # Base types (like int, bool) don't contain variables
            return False


def apply_subst(t: LambdaType, subst: Substitution) -> LambdaType:
    """
    Applies the current substitution to a type (recursively).
    If a type variable is in the substitution map, it replaces it with the mapped type.
    This is used to resolve types during inference and unification.
    """
    match t:
        case TypeVar(id):
            # If the variable has a substitution, recurse on that type.
            return apply_subst(subst[id], subst) if id in subst else t
        case Arrow(arg, ret):
            # Recursively apply substitutions to function argument and return types.
            return Arrow(apply_subst(arg, subst), apply_subst(ret, subst))
        case _:
            # Primitive and named types remain unchanged.
            return t


def unify(t1: LambdaType, t2: LambdaType, subst: Substitution) -> None:
    """
    Attempts to unify two types by updating the substitution map in-place.
    This is the key step in Hindley-Milner inference, where we resolve type equalities.
    """
    # Apply current substitutions before unifying.
    t1 = apply_subst(t1, subst)
    t2 = apply_subst(t2, subst)

    match (t1, t2):
        case (TypeVar(id1), TypeVar(id2)) if id1 == id2:
            # Both are the same type variable - already unified.
            return

        case (TypeVar(id), _):
            # If the left is a variable, try binding it to the right.
            if occurs_in(TypeVar(id), t2):  # It is true if it is a recursive type
                raise TypeMismatchError(f"Occurs check failed: {t1} in {t2}")
            subst[id] = t2
            return

        case (_, TypeVar(_)):
            # Swap the order and unify again (to match the previous case).
            unify(t2, t1, subst)
            return

        case (p1, p2) if isinstance(p1, Primitive) and isinstance(p2, Primitive) and p1 == p2:
            # Both are the same primitive (e.g., int vs int) - fine.
            return

        case (n1, n2) if isinstance(n1, TypeName) and isinstance(n2, TypeName) and n1.name == n2.name:
            # Both are the same named type (e.g., MyType vs MyType).
            return

        case (Arrow(a1, r1), Arrow(a2, r2)):
            # If both are function types, unify argument and return types recursively.
            unify(a1, a2, subst)
            unify(r1, r2, subst)
            return

        case _:
            # Any other case: the types cannot be made equal.
            raise TypeMismatchError(f"Cannot unify {t1} with {t2}")

# ------------------------------------------------------------------------------------
#                        TYPE INFERENCE CORE - Expression Traversal
# ------------------------------------------------------------------------------------

def infer(expr: TypedExpr, env: TypeEnv, subst: Substitution) -> TypedExpr:
    """
    Recursively infers the type of a lambda expression ('expr') under the given environment ('env').
    During traversal, it builds up the substitution map ('subst') to resolve type variables.
    """
    match expr.expr:
        case Id(name):
            # Look up variable name in environment.
            if name not in env:
                raise InsufficientAnnotationsError(f"Unbound variable: {name}")
            # Apply current substitutions to the type before returning it.
            return TypedExpr(expr.expr, apply_subst(env[name], subst))

        case Int(_):
            # An integer literal always has type 'int'
            return TypedExpr(expr.expr, Primitive.INT)

        case Bool.TRUE | Bool.FALSE:
            return TypedExpr(expr.expr, Primitive.BOOL)

        case App(func, arg):
            # Infer type of function part
            tf = infer(func, env, subst)
            # Infer type of argument part
            ta = infer(arg, env, subst)
            # Introduce a fresh type variable for the result type of application
            tr = fresh_typevar()
            # Ensure the function's type matches: tf = ta -> tr
            unify(tf.type, Arrow(ta.type, tr), subst)
            # Final result type is the resolved tr
            
            # create a new appNode with the inferred results
            # and return a new typedExpression with the new appNode and the calculated type
            appNode = App(tf, ta)
            return TypedExpr(appNode, apply_subst(tr, subst))

        case Lambda(decl, body, _):
            # A lambda must always have an annotation on its parameter (i.e., \(x : type). body).
            if decl.type is None:
                raise InsufficientAnnotationsError(f"Parameter {decl.var.name} missing type")
            # Extend environment with parameter binding.
            env2 = env.copy()
            env2[decl.var.name] = decl.type
            # Infer type of body in new environment
            typed_body = infer(body, env2, subst)
            tb = typed_body.type
            # The lambda’s type is arg -> result

            # Apply substitutions to argument and return types
            arg_type = apply_subst(decl.type, subst)
            ret_type = apply_subst(tb, subst)
            # Reconstruct Lambda AST with correct inner types
            lambda_node = Lambda(
                decl=VarDecl(decl.var, arg_type),
                body=typed_body,
                ret=ret_type
            )

            # Return TypedExpr wrapping the Lambda node
            return TypedExpr(lambda_node, Arrow(arg_type, ret_type))

        case Let(decl, defn, body):
            # Infer type of the definition part
            typed_defn = infer(defn, env, subst)
            defn_type = typed_defn.type

            # If the declaration had a type, unify it with the inferred one
            if decl.type:
                unify(defn_type, decl.type, subst)
                final_decl_type = apply_subst(decl.type, subst)
            else:
                final_decl_type = defn_type

            # Extend environment with the new variable
            env2 = env.copy()
            env2[decl.var.name] = final_decl_type

            typed_body = infer(body, env2, subst)
            body_type = typed_body.type

            # Construct final Let node with updated types
            let_node = Let(
                decl=VarDecl(decl.var, final_decl_type),
                defn=typed_defn,
                body=typed_body
            )

            return TypedExpr(let_node, body_type)

        case _:
            raise NotImplementedError(f"Unknown expression: {expr}")

# ------------------------------------------------------------------------------------
#                         FINAL PASS - Apply Substitutions to AST
# ------------------------------------------------------------------------------------

def apply_subst_expr(expr: TypedExpr, subst: Substitution) -> TypedExpr:
    """
    Traverses the full AST after type inference is complete and applies final substitutions.
    This ensures that all type variables are replaced with concrete types.
    """
    # Apply substitution to current node’s type
    t = apply_subst(expr.type, subst)

    match expr.expr:
        case Id() | Int() | Bool():
            return TypedExpr(expr.expr, t)

        case App(func, arg):
            # Recurse on both function and argument
            return TypedExpr(App(apply_subst_expr(func, subst),
                                 apply_subst_expr(arg, subst)), t)

        case Lambda(decl, body, ret):
            # I am not sure I am using the syntax here correctly.
            new_decl = VarDecl(decl.var, apply_subst(decl.type, subst))
            new_body = apply_subst_expr(body, subst)
            new_ret_type = apply_subst(ret, subst)
            return TypedExpr(
                Lambda(
                    decl=new_decl,
                    body=new_body,
                    ret=new_ret_type
                ),
                t
            )

        case Let(decl, defn, body):
            return TypedExpr(
                Let(VarDecl(decl.var, apply_subst(decl.type, subst)), 
                    apply_subst_expr(defn, subst), 
                    apply_subst_expr(body, subst)),
                t
            )

        case _:
            raise NotImplementedError(f"Unknown node: {expr.expr}")

# ------------------------------------------------------------------------------------
#                         ENTRY POINT - Public API Function
# ------------------------------------------------------------------------------------

def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded types (containing TypeVar types).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """
    assert is_grounded_expr(expr, require_fully_annotated=False)

    # Start with an empty substitution map
    subst: Substitution = {}

    # Perform recursive inference to populate the substitution map
    inferred_expr = infer(expr, env={}, subst=subst)

    # Apply all substitutions to the AST to fully resolve it
    result: TypedExpr = apply_subst_expr(inferred_expr, subst)

    # Ensure the result is fully typed (no free variables left)
    if not is_grounded_expr(result, require_fully_annotated=True):
        raise InsufficientAnnotationsError("Output contains unspecified type variables")
        # print(f"Output contains unspecified type variables")

    return result


def main() -> None:
    expr = parse(r"""\x: int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()
