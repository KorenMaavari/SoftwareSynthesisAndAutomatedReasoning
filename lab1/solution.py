from syntax.lambda_pure import LambdaExpr, Id, Int, App, Lambda, Let
import itertools


# =============================
# Alpha-Equivalence Implementation
# =============================

# Alpha equivalence means that two lambda expressions are the same
# even if they use different names for their bound variables.
# For example: (\x. x) and (\y. y) are alpha-equivalent.

def alpha_equivalent(e1: LambdaExpr, e2: LambdaExpr) -> bool:
    """Check if two lambda expressions differ only in the names of their bound variables."""
    
    # Define a recursive helper function that compares e1 and e2
    # while maintaining mapping environments (meaning dictionaries) called env1 and env2, that track renamed variables.
    def helper(e1, e2, env1, env2):
        match e1, e2:
            # Case 1: Both expressions are variable references (Id).
            # Compare their mapped names under the renaming environments.
            case Id(x1), Id(x2):
                return env1.get(x1, x1) == env2.get(x2, x2)  # dictionary.get(key, default value if the key does not exist)

            # Case 2: Both expressions are integer literals.
            # They must have the same numeric value to be equivalent.
            case Int(n1), Int(n2):
                return n1 == n2

            # Case 3: Both are function applications: (f1 a1) and (f2 a2)
            # Compare function parts and argument parts recursively.
            case App(f1, a1), App(f2, a2):
                return helper(f1, f2, env1, env2) and helper(a1, a2, env1, env2)

            # Case 4: Both are lambda abstractions: (\x1. b1) and (\x2. b2)
            # Create a fresh name to represent the bound variable in both expressions.
            case Lambda(Id(x1), b1), Lambda(Id(x2), b2):
                fresh = f"_v{len(env1)}"  # Generate unique name like _v0, _v1, _v2, etc. I use underscores in the names because otherwise it conflicts with built-in keywords in the language.
                # Extend both environments to map x1 and x2 to the fresh name
                return helper(b1, b2, env1 | {x1: fresh}, env2 | {x2: fresh})  # env1 | {x1: fresh} means: create a new dictionary that’s a copy of env1, but adds or updates the key x1 with the value fresh.

            # Case 5: Both are let-bindings: let x1 = d1 in b1 and let x2 = d2 in b2
            case Let(Id(x1), d1, b1), Let(Id(x2), d2, b2):
                fresh = f"_let{len(env1)}"  # _let0, _let1, _let2, ...
                # First check that the definitions are equivalent
                # Then check the bodies with extended environments
                return helper(d1, d2, env1, env2) and helper(b1, b2, env1 | {x1: fresh}, env2 | {x2: fresh})

            # Case 6: Expressions do not match any of the above patterns
            case _:
                return False

    # Call the helper with empty renaming environments
    return helper(e1, e2, {}, {})


# =============================
# Normal-Order Interpreter
# =============================

# Create a global iterator for generating fresh variable names
_counter = itertools.count()

# Function to generate a unique variable name that has never been used before
def fresh_var() -> str:
    """Generate a fresh variable name."""
    return f"_x{next(_counter)}"  # Returns _x0, _x1, _x2, etc.

# Function to compute the set of free variables in a lambda expression.
# A variable is free if it is used in the expression but not bound by a lambda.
def free_vars(e: LambdaExpr) -> set[str]:
    match e:
        case Id(x):  # Variable usage
            return {x}
        case Int(_):  # Integer literals have no variables
            return set()
        case App(f, a):  # In an application, collect free vars from both parts
            return free_vars(f) | free_vars(a)
        case Lambda(Id(x), b):  # In a lambda, x is bound and should not be considered free
            return free_vars(b) - {x}
        case Let(Id(x), d, b):  # x is bound in b but not in d
            return free_vars(d) | (free_vars(b) - {x})

# Substitution function: replaces all free occurrences of variable 'x' in expression 'e' with value 'val'.
# This function is "capture-avoiding", meaning it avoids accidentally changing the meaning of variables.
def subst(e: LambdaExpr, x: str, val: LambdaExpr) -> LambdaExpr:
    """Capture-avoiding substitution: e[x := val]"""
    match e:
        case Id(y):  # If this is a variable
            return val if y == x else e  # Replace it only if it matches x

        case Int(_):  # Do not substitute in literals
            return e

        case App(f, a):  # Substitute recursively in both function and argument
            return App(subst(f, x, val), subst(a, x, val))

        case Lambda(Id(y), body):  # In a lambda abstraction
            if y == x:  # If the variable being substituted is the same as the lambda parameter, do not go inside the lambda body.
                return e  # Bound variable shadows x. do not substitute
            elif y in free_vars(val):  # Risk of variable capture
                y_new = fresh_var()  # Generate fresh name
                body = subst(body, y, Id(y_new))  # Rename variable inside body
                return Lambda(Id(y_new), subst(body, x, val))  # Substitute in new body
            else:
                return Lambda(Id(y), subst(body, x, val))  # Safe to substitute

        case Let(Id(y), d, b):  # In a let binding
            d_ = subst(d, x, val)  # Substitute in the definition part
            if y == x:
                # We must not substitute inside b, because x gets shadowed.
                return Let(Id(y), d_, b)  # Bound variable shadows x
            elif y in free_vars(val):  # Risk of variable capture in the body
                y_new = fresh_var()
                b = subst(b, y, Id(y_new))
                return Let(Id(y_new), d_, subst(b, x, val))
            else:
                return Let(Id(y), d_, subst(b, x, val))

# Perform a single step of normal-order beta reduction.
# Returns a tuple (new_expression, changed), where 'changed' is True if a reduction occurred.
def step(expr: LambdaExpr) -> tuple[LambdaExpr, bool]:
    """Performs one step of normal-order β-reduction."""
    match expr:

        # Case: Apply a lambda to an argument
        case App(Lambda(Id(x), body), arg):
            # Perform beta-reduction: substitute arg for x in body
            return subst(body, x, arg), True

        # Case: Application where function or argument may still reduce
        case App(f, a):
            f2, changed = step(f)  # Try to reduce the function part first (normal-order!)
            if changed:  # If f could be reduced
                return App(f2, a), True
            a2, changed = step(a)  # Then try the argument part. If the function part was not reducible (changed == False)
            return App(f, a2), changed  # We then try to reduce the argument a.

        # Case: Let binding - convert to application: from [let x = d in b] to [(λx. b) d]
        case Let(Id(x), d, b):
            return App(Lambda(Id(x), b), d), True

        # Case: Lambda abstraction - try to reduce the body
        case Lambda(v, b):
            b2, changed = step(b)
            return Lambda(v, b2), changed

        # Case: Nothing to reduce
        case _:
            return expr, False


# Fully reduce a lambda expression to its normal form using normal-order strategy.
# The reduction is bounded by a fuel counter to prevent infinite loops.
def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    """Keep performing normal-order reduction steps until you reach normal form, detect divergence or run out of fuel."""
    for _ in range(fuel):
        new_expr, changed = step(expr)  # Try one step of reduction
        if not changed:
            return expr  # Done. We reached a normal form
        expr = new_expr  # Update expression and repeat
    raise RecursionError("Evaluation ran out of fuel (non-terminating?)")
