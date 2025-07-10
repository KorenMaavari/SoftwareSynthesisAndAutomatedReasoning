import typing
import operator

import z3

from syntax.while_lang import (
    parse,
    Id,
    Expr,
    Int,
    BinOp,
    Skip,
    Assign,
    Seq,
    If,
    While,
    Stmt,
)


type Formula = z3.Ast | bool
type PVar = str
type Env = dict[PVar, Formula]
type Invariant = typing.Callable[[Env], Formula]

TRIVIAL: typing.Final = lambda _: True


OP = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": lambda a, b: a / b,
    "!=": operator.ne,
    ">": operator.gt,
    "<": operator.lt,
    "<=": operator.le,
    ">=": operator.ge,
    "=": operator.eq,
}


def mk_env(pvars: set[PVar]) -> Env:
    return {v: z3.Int(v) for v in pvars}


def upd(d: Env, k: PVar, v: Formula) -> Env:
    d = d.copy()
    d[k] = v
    return d


def expr_eval(e: Expr, env: Env) -> Formula:
    """
    Evaluate an expression `e` in the environment `env`.
    """
    match e:
        case Int(value):
            return z3.IntVal(value)
        case Id(name):
            return env[name]
        case BinOp(op, lhs, rhs):
            return OP[op](expr_eval(lhs, env), expr_eval(rhs, env))
        case _:
            raise NotImplementedError(f"Unknown expression: {e}")

def wp(stmt: Stmt, Q: Invariant, env: Env) -> Formula:
    """
    Compute the weakest precondition of `stmt` with respect to postcondition `Q`.
    """
    match stmt:
        case Skip():
            # skip leaves postcondition unchanged
            return Q(env)

        case Assign(Id(var), expr):
            # assignment: substitute expression into postcondition
            return Q(upd(env, var, expr_eval(expr, env)))

        case Seq(first, second):
            # wp[c1; c2]Q = wp[c1](wp[c2]Q)
            mid = lambda e: wp(second, Q, e)
            return wp(first, mid, env)

        case If(cond, then_branch, else_branch):
            cond_eval = expr_eval(cond, env)
            # wp[if b then c1 else c2]Q = (b ⇒ wp[c1]Q) ∧ (¬b ⇒ wp[c2]Q)
            return z3.And(
                z3.Implies(cond_eval, wp(then_branch, Q, env)),
                z3.Implies(z3.Not(cond_eval), wp(else_branch, Q, env)),
            )

        case While(cond, body):
            # Use loop invariant from environment
            linv: Invariant = env["linv"]
            cond_eval = expr_eval(cond, env)

            # 1. Invariant preserved by body (preservation)
            preserved = z3.Implies(
                z3.And(linv(env), cond_eval),
                wp(body, linv, env),
            )

            # 2. Invariant and loop exit imply postcondition
            termination = z3.Implies(
                z3.And(linv(env), z3.Not(cond_eval)),
                Q(env),
            )

            # All two must hold
            return z3.And(preserved, termination)

        case _:
            raise NotImplementedError(f"Unknown stmt type: {stmt}")


def find_solution(
    P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = lambda _: True
) -> z3.Solver:
    """
    Try to find proof for Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns a z3.Solver object, ready to be checked.
    """
    # Collect all variable names from AST (recursive traversal)
    def collect_vars(s: Stmt) -> set[str]:
        vars = set()

        def collect_expr(e):
            match e:
                case Int():
                    return
                case Id(name):
                    vars.add(name)
                case BinOp(_, lhs, rhs):
                    collect_expr(lhs)
                    collect_expr(rhs)

        match s:
            case Skip():
                pass
            case Assign(Id(name), expr):
                vars.add(name)
                collect_expr(expr)
            case Seq(s1, s2):
                vars |= collect_vars(s1)
                vars |= collect_vars(s2)
            case If(cond, t, f):
                collect_expr(cond)
                vars |= collect_vars(t)
                vars |= collect_vars(f)
            case While(cond, body):
                collect_expr(cond)
                vars |= collect_vars(body)
            case _:
                raise NotImplementedError

        return vars

    vars = collect_vars(stmt)
    env: Env = mk_env(vars)
    env["linv"] = linv  # Add loop invariant to environment

    # Construct the VC: P ∧ ¬wp(stmt, Q)
    # But also include initiation separately:
    initiation = z3.Implies(P(env), linv(env))
    body_vc = z3.And(P(env), z3.Not(wp(stmt, Q, env)))
    vc = z3.And(initiation, body_vc)

    solver = z3.Solver()
    solver.add(vc)
    return solver


def verify(P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = TRIVIAL) -> bool:
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns True if the triple is valid.
    """
    solver = find_solution(P, stmt, Q, linv)
    result = solver.check()
    if result == z3.unsat:
        return True
    else:
        print("Counterexample:")
        print(solver.model())
        return False


def main() -> None:
    # example program
    program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    P = TRIVIAL
    Q = lambda d: d["a"] == d["b"]
    linv = lambda d: d["a"] == d["b"]

    ast = parse(program)
    # Your task is to implement "verify"
    solver = find_solution(P, ast, Q, linv=linv)
    if solver.check() == z3.sat:
        print("Counterexample found:")
        print(solver.model())
    else:
        print("No counterexample found. The Hoare triple is valid.")


if __name__ == "__main__":
    main()
