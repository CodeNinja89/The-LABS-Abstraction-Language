import z3
from core.ast import * # Import from our new ast.py
# Note: This file has NO dependencies on context, encoder, or transformer.

def __is_satisfiable__(phi: z3.BoolRef) -> bool:
    """
    Checks if a Z3 formula is satisfiable.
    (Moved from LABSCore.py)
    """
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.sat

def eval_measure_if_possible(measure_node: Term, P: z3.BoolRef, encoder) -> int | None:
    """
    Tries to evaluate a loop measure to a concrete int under given assumptions.
    (Moved from LABSCore.py)
    
    Note: We must pass in the 'encoder' to visit the measure_node.
    """
    s = z3.Solver()
    s.add(P)
    s.push()
    try:
        encoded_measure = encoder.visit(measure_node)
        measure_sort = encoded_measure.sort()
        
        # We need a fresh var to check the model value
        x = z3.BitVec("__measure__", measure_sort.size())
        
        s.add(x == encoded_measure)
        if s.check() == z3.sat:
            m = s.model()
            return m.eval(x).as_long()
    except Exception:
        # Failed to encode or evaluate
        return None
    return None

def collect_while_loops(prog: Prog) -> list[While]:
    """
    Finds all While nodes in a program AST.
    (Moved from utils.py)
    """
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

def check_soundness(Q: z3.BoolRef, epsilon: z3.BoolRef) -> bool:
    """
    Checks if the generated SP (Q) implies the expected postcondition (epsilon).
    (Q ⊨ epsilon) is true iff (Q ∧ ¬epsilon) is unsat.
    (Moved from utils.py)
    """
    solver = z3.Solver()
    solver.add(z3.And(Q, z3.Not(epsilon)))
    result = solver.check()
    
    if result == z3.unsat:
        return True
    else:
        # Not sound, print a counterexample
        print("❌ Soundness check failed. Counterexample:")
        m = solver.model()
        sorted_model = sorted([(d, m[d]) for d in m], key=lambda x: str(x[0]))
        for d, val in sorted_model:
            print(f"  {d} = {val}")
        return False


def pretty_printer(z3_expr) -> str:
    """
    Converts a Z3Py expression to a readable string.
    (Moved from utils.py)
    """
    # --- BOOLEAN LOGIC ---
    if z3.is_bool(z3_expr):
        if z3.is_true(z3_expr):
            return "True"
        elif z3.is_false(z3_expr):
            return "False"
        elif z3.is_not(z3_expr):
            return f"¬({pretty_printer(z3_expr.children()[0])})"
        elif z3.is_and(z3_expr):
            children = [pretty_printer(child) for child in z3_expr.children()]
            return f"({' ∧ '.join(children)})"
        elif z3.is_or(z3_expr):
            children = [pretty_printer(child) for child in z3_expr.children()]
            return f"({' ∨ '.join(children)})"
        
        # --- "SMART" EQUALITY CHECKER ---
        elif z3.is_eq(z3_expr):
            left = z3_expr.children()[0]
            right = z3_expr.children()[1]
            
            # Pattern 1: extract(val) == 0
            if (z3.is_app_of(left, z3.Z3_OP_EXTRACT) and z3.is_bv_value(right) and right.as_long() == 0):
                val_node = left.children()[0]
                val_size = val_node.sort().size()
                hi = left.params()[0]
                lo = left.params()[1]
                if hi == val_size - 1:
                    limit = 1 << lo
                    return f"({pretty_printer(val_node)} < {limit}u{val_size})"
            
            # Pattern 2: 0 == extract(val)
            if (z3.is_app_of(right, z3.Z3_OP_EXTRACT) and z3.is_bv_value(left) and left.as_long() == 0):
                val_node = right.children()[0]
                val_size = val_node.sort().size()
                hi = right.params()[0]
                lo = right.params()[1]
                if hi == val_size - 1:
                    limit = 1 << lo
                    return f"({pretty_printer(val_node)} < {limit}u{val_size})"
            
            left_str = pretty_printer(left)
            right_str = pretty_printer(right)
            return f"({left_str} == {right_str})"
        
        elif z3.is_implies(z3_expr):
            left = pretty_printer(z3_expr.children()[0])
            right = pretty_printer(z3_expr.children()[1])
            return f"({left} => {right})"
        elif z3.is_const(z3_expr) and z3_expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
             return str(z3_expr)
        else:
            op_name = z3_expr.decl().name()
            args = [pretty_printer(arg) for arg in z3_expr.children()]
            if op_name == 'bvugt':
                return f"({args[0]} > {args[1]})"
            elif op_name == 'bvuge':
                return f"({args[0]} >= {args[1]})"
            elif op_name == 'bvult':
                return f"({args[0]} < {args[1]})"
            elif op_name == 'bvule':
                return f"({args[0]} <= {args[1]})"
            else:
                return f"{op_name}({', '.join(args)})"

    # --- BIT-VECTOR (BV) LOGIC ---
    elif z3.is_bv(z3_expr):
        if z3.is_bv_value(z3_expr):
            val = z3_expr.as_long()
            size = z3_expr.size()
            return f"{val}u{size}"
        if z3.is_const(z3_expr):
            return str(z3_expr)
        
        args = [pretty_printer(arg) for arg in z3_expr.children()]
        if z3_expr.num_args() == 0:
             return str(z3_expr)
        op_name = z3_expr.decl().name()
        
        if op_name == 'bvadd': return f"({' + '.join(args)})"
        elif op_name == 'bvsub': return f"({' - '.join(args)})"
        elif op_name == 'bvmul': return f"({' * '.join(args)})"
        elif op_name == 'bvudiv_i' or op_name == 'bvudiv': return f"({' / '.join(args)})"
        elif op_name == 'bvurem': return f"({' % '.join(args)})"
        elif op_name == 'bvand': return f"({' & '.join(args)})"
        elif op_name == 'bvor': return f"({' | '.join(args)})"
        elif op_name == 'bvxor': return f"({' ^ '.join(args)})"
        elif op_name == 'bvshl': return f"({' << '.join(args)})"
        elif op_name == 'bvlshr': return f"({' >> '.join(args)})"
        elif op_name == 'bvnot': return f"~({args[0]})"
        elif op_name == 'extract':
            val_str = pretty_printer(z3_expr.children()[0])
            return f"{val_str}"
        else:
            return f"{op_name}({', '.join(args)})"

    # --- Other Types (Datatypes, Arrays, etc.) ---
    else:
        if z3.is_const(z3_expr):
             return str(z3_expr)
        args = [pretty_printer(arg) for arg in (z3_expr.children())]
        op_name = z3_expr.decl().name()
        if args:
            return f"{op_name}({', '.join(args)})"
        else:
            return str(z3_expr)