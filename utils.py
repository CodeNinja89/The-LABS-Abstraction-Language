# utils.py
# Contains utility functions, including the final, robust Z3 pretty-printer.

from z3 import *
from LABSCore import SP, fmla_enc, term_enc, __variableStore__
from labsAst import *

def collect_while_loops(prog):
    loops = []

    def visit(node):
        if isinstance(node, While):
            loops.append(node)
        elif isinstance(node, Seq):
            visit(node.alpha)
            visit(node.beta)
        elif isinstance(node, Choice):
            visit(node.alpha)
            visit(node.beta)
            
    visit(prog)
    return loops


def check_invariant_preservation_z3(loop: While) -> bool:
    """
    Checks if the loop invariant is preserved across one iteration:
        (I ∧ C) ⇒ SP(body, I ∧ C) ⊨ I
    """
    I = fmla_enc(loop.invariant)
    C = fmla_enc(loop.condition)

    # Precondition to loop body: invariant and condition must hold
    pre = And(I, C)

    # Compute SP after one loop iteration
    post = SP(loop.alpha, pre)

    # Check if the invariant is preserved
    implication = Implies(post, I)

    s = Solver()
    s.add(Not(implication))
    result = s.check()

    if result == unsat:
        # print("✅ Invariant preserved across one loop iteration.")
        return True
    else:
        # print("❌ Invariant NOT preserved. Counterexample:")
        m = s.model()
        for d in m:
            print(f"  {d} = {m[d]}")
        return False

def check_soundness(Q, epsilon):
    solver = Solver()
    solver.add(And(Q, Not(epsilon)))
    result = solver.check()
    
    if result == unsat:
        return True
    else:
        m = solver.model()
        for d in m:
            print(f"  {d} = {m[d]}")
        return False

def pretty_printer(z3_expr):
    """
    Converts a Z3Py expression to a string representing a first-order logic formula,
    printing disjunctions and conjunctions in reverse order to match control flow.
    """
    if is_bool(z3_expr):
        if is_true(z3_expr):
            return "True"
        elif is_false(z3_expr):
            return "False"
        elif is_not(z3_expr):
            return f"¬({pretty_printer(z3_expr.children()[0])})"
        elif is_and(z3_expr):
            children = [pretty_printer(child) for child in reversed(z3_expr.children())]
            return f"({' ∧ '.join(children)})"
        elif is_or(z3_expr):
            children = [pretty_printer(child) for child in reversed(z3_expr.children())]
            return f"({' ∨ '.join(children)})"
        elif is_eq(z3_expr):
            left = pretty_printer(z3_expr.children()[0])
            right = pretty_printer(z3_expr.children()[1])
            return f"({left} == {right})"
        elif is_implies(z3_expr):
            children = [pretty_printer(child) for child in z3_expr.children()]
            return f"({' => '.join(children)})"
        else:
            return str(z3_expr)

    elif is_arith(z3_expr):
        if z3_expr.num_args() > 0:
            args = [pretty_printer(arg) for arg in (z3_expr.children())]
            if is_add(z3_expr):
                return f"({' + '.join(args)})"
            elif is_mul(z3_expr):
                return f"({' * '.join(args)})"
            elif is_sub(z3_expr):
                return f"({' - '.join(args)})"
            elif is_div(z3_expr):
                return f"({' / '.join(args)})"
            elif is_mod(z3_expr):
                return f"({args[0]} % {args[1]})"
            else:
                return str(z3_expr)
        else:
            return str(z3_expr)

    elif is_bv(z3_expr):
        args = [pretty_printer(arg) for arg in reversed(z3_expr.children())]
        if z3_expr.num_args() > 0:
            op_name = z3_expr.decl().name()
            if op_name == 'bvadd':
                return f"Sum({', '.join(args)})"
            elif op_name == 'bvsmod_i':
                return f"Mod({', '.join(args)})"
            else:
                return str(z3_expr)
        else:
            if z3_expr.num_args() == 0:
                val = z3_expr.as_long()
                if val >= 2**(bit_width - 1):
                    signed_val = val - 2**bit_width
                else:
                    signed_val = val
                return str(signed_val)

    else:
        args = [pretty_printer(arg) for arg in (z3_expr.children())]
        if args:
            return f"{z3_expr.decl().name()}({', '.join(args)})"
        else:
            return str(z3_expr)