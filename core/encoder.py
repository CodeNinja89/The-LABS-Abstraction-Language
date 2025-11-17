import z3
from core.ast import *
from core.context import LabsContext

class Z3Encoder:
    """
    Translates labs.ast nodes into Z3 expressions.
    This class replaces the 'term_enc' and 'fmla_enc' functions.
    It uses the Visitor pattern.
    """

    def __init__(self, context: LabsContext):
        self.context = context

    def visit(self, node: Node):
        """
        Public-facing dispatch method.
        It finds the correct visitor method (e.g., 'visit_Sum')
        based on the node's class name.
        """
        method_name = f'visit_{node.__class__.__name__}'
        visitor = getattr(self, method_name, self.generic_visit)
        return visitor(node)

    def generic_visit(self, node: Node):
        """Called if no explicit visitor method is found."""
        raise NotImplementedError(f"No visitor method for {node.__class__.__name__}")

    # --- Term Visitors (from term_enc) ---

    def visit_Const(self, node: Const) -> z3.BitVecRef:
        # Logic from term_enc(Const(...))
        val, suffix = node.value
        if suffix == "u8":
            return z3.BitVecVal(val, 8)
        elif suffix == "u16":
            return z3.BitVecVal(val, 16)
        elif suffix == "u64":
            return z3.BitVecVal(val, 64)
        else:
            # Default (u32 or unknown)
            return z3.BitVecVal(val, 32)

    def visit_Var(self, node: Var) -> z3.ExprRef:
        # Logic from term_enc(Var(...))
        # Get the *current* SSA-versioned Z3 constant from the context
        try:
            return self.context.get_ssa_var_term(node.name)
        except ValueError:
            # This handles cases like fmla_enc(Var('failed'))
            # where a Var is a formula. We try to encode as a formula.
            return self.visit_FmlaVar(node)

    def visit_Sum(self, node: Sum) -> z3.BitVecRef:
        return self.visit(node.left) + self.visit(node.right)

    def visit_Difference(self, node: Difference) -> z3.BitVecRef:
        return self.visit(node.left) - self.visit(node.right)

    def visit_Product(self, node: Product) -> z3.BitVecRef:
        return self.visit(node.left) * self.visit(node.right)

    def visit_Division(self, node: Division) -> z3.BitVecRef:
        # Logic from term_enc(Division(...))
        return z3.UDiv(self.visit(node.left), self.visit(node.right))

    def visit_Mod(self, node: Mod) -> z3.BitVecRef:
        # Logic from term_enc(Mod(...))
        return z3.URem(self.visit(node.left), self.visit(node.right))

    def visit_BitOr(self, node: BitOr) -> z3.BitVecRef:
        return self.visit(node.l) | self.visit(node.r)

    def visit_BitXor(self, node: BitXor) -> z3.BitVecRef:
        return self.visit(node.l) ^ self.visit(node.r)

    def visit_BitAnd(self, node: BitAnd) -> z3.BitVecRef:
        return self.visit(node.l) & self.visit(node.r)

    def visit_Shl(self, node: Shl) -> z3.BitVecRef:
        return self.visit(node.l) << self.visit(node.r)

    def visit_LShr(self, node: LShr) -> z3.BitVecRef:
        # Logic from term_enc(LShr(...))
        return z3.LShR(self.visit(node.l), self.visit(node.r))

    def visit_BitNot(self, node: BitNot) -> z3.BitVecRef:
        return ~(self.visit(node.x))

    def visit_Fn(self, node: Fn) -> z3.ExprRef:
        # Logic from term_enc(Fn(...)) and fmla_enc(Fn(...))
        sig = self.context.function_sigs.get(node.name)
        if not sig:
            raise ValueError(f"Function '{node.name}' not declared.")
        
        dom, rng = sig[:-1], sig[-1]
        z3_func = z3.Function(node.name, *(dom + [rng]))
        z3_args = [self.visit(arg) for arg in node.args]
        return z3_func(*z3_args)

    # --- Formula Visitors (from fmla_enc) ---

    def visit_FmlaVar(self, node: Var) -> z3.BoolRef:
        # This is the "formula" case for a variable.
        # Logic from fmla_enc(Var(...))
        var_term = self.context.get_ssa_var_term(node.name)
        if not z3.is_bool(var_term):
            raise ValueError(f"Variable '{node.name}' is not a boolean; cannot be used as a formula.")
        return var_term

    def visit_TrueC(self, node: TrueC) -> z3.BoolRef:
        return z3.BoolVal(True)

    def visit_FalseC(self, node: FalseC) -> z3.BoolRef:
        return z3.BoolVal(False)

    def visit_LtF(self, node: LtF) -> z3.BoolRef:
        # Logic from fmla_enc(LtF(...))
        return z3.ULT(self.visit(node.left), self.visit(node.right))

    def visit_LeF(self, node: LeF) -> z3.BoolRef:
        return z3.ULE(self.visit(node.left), self.visit(node.right))

    def visit_GtF(self, node: GtF) -> z3.BoolRef:
        return z3.UGT(self.visit(node.left), self.visit(node.right))

    def visit_GeF(self, node: GeF) -> z3.BoolRef:
        return z3.UGE(self.visit(node.left), self.visit(node.right))

    def visit_EqF(self, node: EqF) -> z3.BoolRef:
        # Logic from fmla_enc(EqF(...))
        try:
            # First, try to encode as formulas (e.g., bool == bool)
            l_fmla = self.visit(node.left)
            r_fmla = self.visit(node.right)
            if z3.is_bool(l_fmla) and z3.is_bool(r_fmla):
                return l_fmla == r_fmla
        except ValueError:
            pass # Fallback to term encoding
        
        # Fallback: encode as terms (e.g., BitVec == BitVec)
        l_term = self.visit(node.left)
        r_term = self.visit(node.right)
        return l_term == r_term

    def visit_NotF(self, node: NotF) -> z3.BoolRef:
        return z3.Not(self.visit(node.q))

    def visit_AndF(self, node: AndF) -> z3.BoolRef:
        return z3.And(self.visit(node.p), self.visit(node.q))

    def visit_OrF(self, node: OrF) -> z3.BoolRef:
        return z3.Or(self.visit(node.p), self.visit(node.q))

    def visit_ImpliesF(self, node: ImpliesF) -> z3.BoolRef:
        return z3.Implies(self.visit(node.p), self.visit(node.q))

    def visit_ForAllF(self, node: ForAllF) -> z3.BoolRef:
        # Logic from fmla_enc(ForAllF(...))
        # We create a new Z3 var for the quantifier.
        # Note: This var is *not* SSA-managed by our context.
        x = z3.BitVec(node.var, 32) # Defaulting to 32-bit
        return z3.ForAll([x], self.visit(node.body))

    def visit_ExistsF(self, node: ExistsF) -> z3.BoolRef:
        # Logic from fmla_enc(ExistsF(...))
        x = z3.BitVec(node.var, 32)
        return z3.Exists([x], self.visit(node.body))