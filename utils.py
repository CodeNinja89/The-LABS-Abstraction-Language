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

# [File: utils.py]

# You will need to add "import z3" at the top of utils.py
# if it's not already there.
# [File: utils.py]

import z3

# ... (your other functions like collect_while_loops, etc.) ...

def pretty_printer(z3_expr):
    """
    Converts a Z3Py expression to a string representing a first-order logic formula.
    Includes logic to reverse-engineer common Z3 simplifications for readability.
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
            # Reverse children to match control flow
            children = [pretty_printer(child) for child in reversed(z3_expr.children())]
            return f"({' ∧ '.join(children)})"
        elif z3.is_or(z3_expr):
            # Reverse children to match control flow
            children = [pretty_printer(child) for child in reversed(z3_expr.children())]
            return f"({' ∨ '.join(children)})"
        
        # --- "SMART" EQUALITY CHECKER ---
        elif z3.is_eq(z3_expr):
            left = z3_expr.children()[0]
            right = z3_expr.children()[1]
            
            # --- THIS IS THE FIX ---
            # Pattern 1: extract(val) == 0
            if (z3.is_app_of(left, z3.Z3_OP_EXTRACT) and z3.is_bv_value(right) and right.as_long() == 0):
                val_node = left.children()[0]
                val_size = val_node.sort().size()
                hi = left.params()[0]
                lo = left.params()[1]

                # Check for the specific pattern: "are all upper bits zero?"
                if hi == val_size - 1:
                    limit = 1 << lo
                    return f"({pretty_printer(val_node)} < {limit}u{val_size})"
            
            # Pattern 2: 0 == extract(val)
            if (z3.is_app_of(right, z3.Z3_OP_EXTRACT) and z3.is_bv_value(left) and left.as_long() == 0):
                val_node = right.children()[0]
                val_size = val_node.sort().size()
                hi = right.params()[0]
                lo = right.params()[1]

                # Check for the specific pattern: "are all upper bits zero?"
                if hi == val_size - 1:
                    limit = 1 << lo
                    return f"({pretty_printer(val_node)} < {limit}u{val_size})"
            
            # Fallback to default behavior
            left_str = pretty_printer(left)
            right_str = pretty_printer(right)
            return f"({left_str} == {right_str})"
        
        elif z3.is_implies(z3_expr):
            left = pretty_printer(z3_expr.children()[0])
            right = pretty_printer(z3_expr.children()[1])
            return f"({left} => {right})"
        elif z3.is_const(z3_expr) and z3_expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
             # Handles boolean symbolic variables (e.g., 'failed')
             return str(z3_expr)
        else:
            # Handles other boolean operations (e.g., ULT, UGT, Function Calls)
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
                # Default for functions like isFull(msgQ)
                return f"{op_name}({', '.join(args)})"

    # --- BIT-VECTOR (BV) LOGIC ---
    elif z3.is_bv(z3_expr):
        
        # Case 1: It's a concrete value (e.g., 10u8)
        if z3.is_bv_value(z3_expr):
            val = z3_expr.as_long()
            size = z3_expr.size()
            return f"{val}u{size}" # Prints as 10u8

        # Case 2: It's a symbolic variable (e.g., x, n_0)
        if z3.is_const(z3_expr):
            return str(z3_expr)

        # Case 3: It's an operation (e.g., +, &, <<)
        args = [pretty_printer(arg) for arg in z3_expr.children()]
        if z3_expr.num_args() == 0:
             return str(z3_expr) # Failsafe

        op_name = z3_expr.decl().name()
        
        if op_name == 'bvadd':
            return f"({' + '.join(args)})"
        elif op_name == 'bvsub':
            return f"({' - '.join(args)})"
        elif op_name == 'bvmul':
            return f"({' * '.join(args)})"
        elif op_name == 'bvudiv_i' or op_name == 'bvudiv':
            return f"({' / '.join(args)})"
        elif op_name == 'bvurem':
            return f"({' % '.join(args)})"
        elif op_name == 'bvand':
            return f"({' & '.join(args)})"
        elif op_name == 'bvor':
            return f"({' | '.join(args)})"
        elif op_name == 'bvxor':
            return f"({' ^ '.join(args)})"
        elif op_name == 'bvshl':
            return f"({' << '.join(args)})"
        elif op_name == 'bvlshr':
            return f"({' >> '.join(args)})"
        elif op_name == 'bvnot':
            return f"~({args[0]})"
        
        # Format extract as val[hi:lo]
        elif op_name == 'extract':
            val_str = pretty_printer(z3_expr.children()[0])
            return f"{val_str}"
        
        else:
            # Fallback for other ops (e.g., sign_extend)
            return f"{op_name}({', '.join(args)})"

    # --- ARITH (for non-bit-vector ints, if you ever add them) ---
    elif z3.is_arith(z3_expr):
        if z3.is_int_value(z3_expr):
             return str(z3_expr.as_long())
        if z3.is_const(z3_expr):
            return str(z3_expr)
            
        args = [pretty_printer(arg) for arg in z3_expr.children()]
        op_name = z3_expr.decl().name()

        if op_name == '+':
            return f"({' + '.join(args)})"
        elif op_name == '-':
             return f"({' - '.join(args)})"
        elif op_name == '*':
             return f"({' * '.join(args)})"
        elif op_name == '/':
             return f"({' / '.join(args)})"
        else:
             return f"{op_name}({', '.join(args)})"

    # --- DATATYPES (Structs) and FUNCTIONS ---
    else:
        if z3.is_const(z3_expr):
             return str(z3_expr)
             
        args = [pretty_printer(arg) for arg in (z3_expr.children())]
        op_name = z3_expr.decl().name()
        
        if args:
            return f"{op_name}({', '.join(args)})"
        else:
            return str(z3_expr)