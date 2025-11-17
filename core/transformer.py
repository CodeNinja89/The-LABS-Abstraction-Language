import z3
from core.ast import *
from core.context import LabsContext
from core.encoder import Z3Encoder
# We'll need the sat checker from utils
from core.utils import __is_satisfiable__, eval_measure_if_possible 

class SPTransformer:
    """
    Computes the Strongest Postcondition (SP) for a program AST.
    This class replaces the 'SP' and 'post' functions from LABSCore.py.
    It uses the Visitor pattern.
    """

    def __init__(self, context: LabsContext, encoder: Z3Encoder):
        self.context = context
        self.encoder = encoder

    def transform(self, node: Prog, P: z3.BoolRef, max_depth=5) -> z3.BoolRef:
        """
        Public-facing dispatch method.
        It finds the correct transform method (e.g., 'transform_Asgn')
        based on the node's class name.
        """
        method_name = f'transform_{node.__class__.__name__}'
        visitor = getattr(self, method_name, self.generic_transform)
        
        # FIX: We *always* pass max_depth to all visitors.
        # They can choose to ignore it if they don't recurse.
        return visitor(node, P, max_depth)


    def generic_transform(self, node: Prog, P: z3.BoolRef, max_depth: int):
        """Called if no explicit transform method is found."""
        raise NotImplementedError(f"No SP transform for {node.__class__.__name__}")

    # --- Transformer Visitors (from SP in LABSCore.py) ---

    def transform_Skip(self, node: Skip, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # Logic from SP(Skip(), ...)
        return P

    def transform_Assert(self, node: Assert, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # Logic from SP(Assert(), ...)
        # An assert just adds its condition to the predicate
        assert_cond = self.encoder.visit(node.q)
        return z3.And(assert_cond, P)

    def transform_Seq(self, node: Seq, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # Logic from SP(Seq(), ...)
        # SP(alpha; beta, P) = SP(beta, SP(alpha, P))
        P_alpha = self.transform(node.alpha, P, max_depth)
        P_beta = self.transform(node.beta, P_alpha, max_depth)
        return P_beta

    def transform_Asgn(self, node: Asgn, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # Logic from SP(Asgn(), ...) using the "NEW FIX"
        
        # 1. Encode the RHS using the *current* SSA state (via encoder)
        encoded_right = self.encoder.visit(node.right)
        
        # 2. Get the *new* SSA variable term from the context
        new_var_term = self.context.next_ssa_var_term(node.left.name)
        
        # 3. Check for type mismatch
        if encoded_right.sort() != new_var_term.sort():
            raise TypeError(
                f"Type mismatch in assignment to '{node.left.name}': "
                f"Cannot assign {encoded_right.sort()} to {new_var_term.sort()}."
            )
            
        # 4. Return the new SP: (new_var == encoded_right) AND P
        return z3.And(new_var_term == encoded_right, P)
        
    def transform_NewAssignment(self, node: NewAssignment, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # This node (e.g., 'msg := new message') is handled by the parser,
        # which registers 'msg' and 'msg.field' in the context.
        # In the SP logic, this assignment doesn't add a Z3 constraint,
        # it just ensures the variable is available. We treat it as a Skip.
        return P

    def transform_Choice(self, node: Choice, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        """
        Transforms a Choice (if/else) node.
        This logic is from SP(Choice(), ...)
        and includes the fixes to correctly propagate the final state.
        """
        
        # 1. Encode the condition
        cond_z3 = self.encoder.visit(node.condition)
        
        # 2. Create "then" and "else" preconditions
        P_then = z3.simplify(z3.And(P, cond_z3))
        P_else = z3.simplify(z3.And(P, z3.Not(cond_z3)))

        sat_then = __is_satisfiable__(P_then)
        sat_else = __is_satisfiable__(P_else)

        # 3. Fork contexts
        context_then = self.context.fork()
        context_else = self.context.fork()
        
        # 4. Create child transformers for each branch
        #    Each child gets its own context AND its own new encoder
        child_transformer_then = SPTransformer(context_then, Z3Encoder(context_then))
        child_transformer_else = SPTransformer(context_else, Z3Encoder(context_else))
        
        # 5. Run the recursive transform on the children
        sp_then_formula = child_transformer_then.transform(node.alpha, P_then, max_depth)
        sp_else_formula = child_transformer_else.transform(node.beta, P_else, max_depth)

        # 6. Handle pruning (the simple cases)
        if not sat_then and not sat_else:
            return z3.BoolVal(False) # Neither path is possible
        
        if sat_then and not sat_else:
            # "Then" path is the only one. Commit its final state back to self.
            self.context = child_transformer_then.context
            self.encoder = child_transformer_then.encoder
            return sp_then_formula
        
        if not sat_then and sat_else:
            # "Else" path is the only one. Commit its final state back to self.
            self.context = child_transformer_else.context
            self.encoder = child_transformer_else.encoder
            return sp_else_formula

        # 7. Merge (The "Phi Function" step)
        # Both paths are feasible. Merge the two child contexts into self.context.
        phi_nodes = self.context.merge(cond_z3, 
                                     child_transformer_then.context, 
                                     child_transformer_else.context)
        
        # After merging, self.context is updated. We MUST create a new
        # encoder that is bound to this new merged context.
        self.encoder = Z3Encoder(self.context)
        
        # 8. Return the final merged SP
        return z3.And(z3.Or(sp_then_formula, sp_else_formula), *phi_nodes)

    def transform_While(self, node: While, P: z3.BoolRef, max_depth: int) -> z3.BoolRef:
        # Logic from SP(While(), ...)
        
        cond = self.encoder.visit(node.condition)
        I = self.encoder.visit(node.invariant)
    
        # Try to get a concrete depth from the measure
        depth = eval_measure_if_possible(node.measure, P, self.encoder) or max_depth
        
        if depth == 0:
            P_notC = z3.simplify(z3.And(P, z3.Not(cond)))
            return P_notC if __is_satisfiable__(P_notC) else z3.BoolVal(False)
    
        P_C = z3.simplify(z3.And(P, cond))
        P_notC = z3.simplify(z3.And(P, z3.Not(cond)))
        feas_C = __is_satisfiable__(P_C)
        feas_notC = __is_satisfiable__(P_notC)
    
        if not feas_C and not feas_notC:
            return z3.BoolVal(False)
    
        # 'stop_now' branch: immediate exit
        stop_now = z3.And(P, I, z3.Not(cond))
    
        if depth == 1:
            # 'body_once' branch: one iteration
            # We must use a forked context for the body
            ctx_body = self.context.fork()
            child_transformer_body = SPTransformer(ctx_body, Z3Encoder(ctx_body))
            # Run the transform
            body_once_formula = child_transformer_body.transform(node.alpha, P_C, max_depth)
    
            # ...
            if feas_C and not feas_notC:
                # FIX: Commit the child's *final* state
                self.context = child_transformer_body.context
                self.encoder = child_transformer_body.encoder
                return body_once_formula
            return z3.Or(stop_now, body_once_formula)
    
        # depth > 1: Unfold
        # SP(while, P, d) = (P & I & ~C) | SP(body; while, P & C, d-1)
        
        # We need a new 'while' node for the recursive call
        recursive_while = While(node.condition, node.alpha, node.invariant, node.measure)
        unfold_prog = Seq(node.alpha, recursive_while)
        
        # Unfolding happens in a forked context
        ctx_unfold = self.context.fork()
        encoder_unfold = Z3Encoder(ctx_unfold) 
        child_transformer = SPTransformer(ctx_unfold, Z3Encoder(ctx_unfold))
        # Run the recursion
        unfolded_formula = child_transformer.transform(
            unfold_prog, 
            P_C, 
            max_depth=depth - 1
        )
    
        if feas_notC and not feas_C: return stop_now
        if feas_C and not feas_notC: 
            self.context = child_transformer.context
            self.encoder = child_transformer.encoder
            return unfolded_formula
        return z3.Or(stop_now, unfolded)