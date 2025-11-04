"""LABSCore.py — Core semantics & strongest postcondition (SP) engine for LABS.

This module provides:
  • Z3 encoders for LABS terms and formulas
  • An SSA-style strongest postcondition transformer SP(α, P)
  • Helpers for satisfiability checks and (optional) loop-unrolling control

Key ideas:
  • SSA versioning: each assignment introduces a fresh version of the LHS.
  • SP composition: SP(Seq(α, β), P) = SP(β, SP(α, P)).
  • Choice pruning: infeasible branches w.r.t. current pre P are dropped.
  • While (bounded unrolling): builds a disjunction of “stop-now” and
    “one-more-iteration then recurse”. Depth can be derived from a measure.

Notes on While:
  • depth == 0:       returns P ∧ ¬C (immediate exit).
  • depth == 1:       returns (I ∧ ¬C) ∨ SP(body, P ∧ C).
  • depth  > 1:       returns (P ∧ I ∧ ¬C) ∨ SP(Seq(body, while...), P ∧ C, depth−1)
  • The depth==1 ‘stop-now’ branch currently omits P (it’s I ∧ ¬C),
    whereas depth>1 uses P ∧ I ∧ ¬C. This mirrors the existing code.
"""

from __future__ import annotations
# from z3 import *
import z3
from dataclasses import dataclass, field
from contextlib import *
from labsAst import *
# from parser import __symbol_table__, __function_sigs__, __z3_structs__, __constants__, dump_symTab, resolve_sort
import parser

bit_width = 64
__variableStore__ = {}

def dump_varStore():
    global __variableStore__
    print(__variableStore__)

def term_enc(e):
    match e:
        case Const(value_tuple):
            # --- NEW CODE ---
            val, suffix = value_tuple
            if suffix == "u8":
                return z3.BitVecVal(val, 8)
            elif suffix == "u16":
                return z3.BitVecVal(val, 16)
            elif suffix == "u64":
                return z3.BitVecVal(val, 64)
            else:
                # Default (u32 or unknown)
                return z3.BitVecVal(val, 32)
        case Var(name):
            base_name = name.split('_')[0]
            sort = parser.__symbol_table__.get(base_name)

            if sort is None:
                # This handles undeclared vars (like in quantifiers)
                # We assume they are 32-bit
                return z3.BitVec(name, 32) 

            # Check if this variable has a current SSA version
            ssa_name = base_name
            if base_name in __variableStore__:
                version = __variableStore__[base_name]
                ssa_name = f"{base_name}_{version}"
            
            return z3.Const(ssa_name, sort)
        case Sum(l, r):
            return term_enc(l) + term_enc(r)
        case Difference(l, r):
            return term_enc(l) - term_enc(r)
        case Product(l, r):
            return term_enc(l) * term_enc(r)
        case Division(l, r):
            return z3.UDiv(term_enc(l), term_enc(r))
        case Mod(l, r):
            return z3.URem(term_enc(l), term_enc(r))
        case BitOr(l, r):
            return term_enc(l) | term_enc(r)
        case BitXor(l, r):
            return term_enc(l) ^ term_enc(r)
        case BitAnd(l, r):
            return term_enc(l) & term_enc(r)
        case Shl(l, r):
            return term_enc(l) << term_enc(r)
        case LShr(l, r):
            return z3.LShR(term_enc(l), term_enc(r))
        case BitNot(l):
            return ~(term_enc(l))
        case Fn(name, args):
            # Use declared sorts: domain = arg sorts, range = last
            sig = parser.__function_sigs__.get(name)
            if not sig:
                # fallback to uint32^n -> uint32
                rng = z3.BitVecSort(32)
                dom = [z3.BitVecSort(32)] * len(args)
            else:
                dom, rng = sig[:-1], sig[-1]
            z3_func = z3.Function(name, *(dom + [rng]))
            z3_args = [term_enc(arg) for arg in args]
            return z3_func(*z3_args)
        case TrueC():  return z3.BoolVal(True)
        case FalseC(): return z3.BoolVal(False)
        case _:
            raise ValueError(f"Unknown term: {e}")

# Boolean expressions.
# We have specified all the boolean opertors
# A boolean formula is a union of all these operators.

def fmla_enc(p: Formula):
    match p:
        case Var(name):
            # A variable can be a formula if its type is bool
            base_name = name.split('_')[0]
            sort = parser.__symbol_table__.get(base_name)
            
            if sort == z3.BoolSort():
                return z3.Const(name, sort)
            else:
                # This variable is a number (Term), not a Formula.
                raise ValueError(f"Variable '{name}' is not a boolean; cannot be used as a formula.")
        case TrueC():  return z3.BoolVal(True)
        case FalseC(): return z3.BoolVal(False)
        case LtF(l, r): return z3.ULT(term_enc(l), term_enc(r))
        case LeF(l, r): return z3.ULE(term_enc(l), term_enc(r))
        case GtF(l, r): return z3.UGT(term_enc(l), term_enc(r))
        case GeF(l, r): return z3.UGE(term_enc(l), term_enc(r))
        case EqF(l, r):
            try:
                l_fmla = fmla_enc(l)
                r_fmla = fmla_enc(r)
                return l_fmla == r_fmla # Z3 boolean equivalence
            except ValueError:
                # If that fails, *then* encode as terms (numbers, structs, etc.)
                #try:
                return term_enc(l) == term_enc(r)
                #except Exception as e:
                    #raise ValueError(f"Cannot encode EqF({l}, {r}) as either Formula or Term") from e
        case NotF(q):   return z3.Not(fmla_enc(q))
        case AndF(p,q): return z3.And(fmla_enc(p), fmla_enc(q))
        case OrF(p,q):  return z3.Or(fmla_enc(p), fmla_enc(q))
        case ImpliesF(p,q): return z3.Implies(fmla_enc(p), fmla_enc(q))
        case ForAllF(var, body):
            x = z3.BitVec(var, 32)
            return z3.ForAll([x], fmla_enc(body))
        case ExistsF(var, body):
            x = z3.BitVec(var, 32)
            return z3.Exists([x], fmla_enc(body))
            
        case Fn(name, args):
            sig = parser.__function_sigs__.get(name) # <--- FIX 1
            if not sig:
                # fallback to uint32^n -> uint32
                rng = z3.BitVecSort(32)
                dom = [z3.BitVecSort(32)] * len(args)
            else:
                dom, rng = sig[:-1], sig[-1]
                
            z3_func = z3.Function(name, *(dom + [rng])) # <--- FIX 2
            z3_args = [term_enc(arg) for arg in args]
            return z3_func(*z3_args)
        case _:
            raise ValueError(f"Unknown formula: {p}")

def nextVar(x: Var):
    if len(x.name.split('_')) == 1:
        if x.name not in __variableStore__:
            __variableStore__[x.name] = 0
        else:
            __variableStore__[x.name] = __variableStore__[x.name] + 1
    return Var('{}_{}'.format(x.name, __variableStore__[x.name]))

def __is_satisfiable__(phi):
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.sat

def eval_measure_if_possible(measure, assumptions):
    """Try to evaluate a loop measure to a concrete int under given assumptions.

    Mechanism:
      • Constrain fresh int x == enc(measure)
      • If SAT and model provides an integer value, return it; otherwise None.

    Args:
        measure: LABS Term for the measure.
        assumptions: z3.BoolRef (typically current precondition P).

    Returns:
        Optional[int]
    """
    s = z3.Solver()
    s.add(assumptions)
    s.push()
    # 1. Encode the measure *first* to find its real sort
    encoded_measure = term_enc(measure)
    measure_sort = encoded_measure.sort()
    
    x = z3.BitVec("__measure__", measure_sort.size())
    
    # 4. Now the comparison is between two identical sorts
    s.add(x == encoded_measure)
    if s.check() == z3.sat:
        m = s.model()
        try:
            return m.eval(x).as_long()
        except:
            return None
    return None

def post(alpha: Prog, P: BoolRef, max_depth=1):
    global __variableStore__
    
    # reset all the stores
    __variableStore__ = {}
    return SP(alpha, P, max_depth)
    
def SP(alpha: Prog, P: BoolRef, max_depth=1):
    """Top-level entry point: reset global state and compute SP(alpha, P).

    Resets:
      • SSA version store
      • parser symbol table, function signatures, struct sorts, constants

    Args:nd
        alpha: LABS program AST
        P:     z3 precondition
        max_depth: bound for while-unrolling (used if measure not concrete)

    Returns:
        z3.BoolRef — the strongest postcondition
    """
    if max_depth == 0:
        return BoolVal(False)
    
    match alpha:
        case Skip():
            # The postcondition of the previous expression is propagated
            return P
        case Asgn(left, right):
            # 1. Get info about the variable
            base_name = left.name.split('_')[0]
            target_sort = parser.__symbol_table__.get(base_name)
            if target_sort is None:
                raise TypeError(f"Undeclared variable in assignment: {left.name}")

            # 2. Check BOOLEAN or TERM assignment
            if target_sort == z3.BoolSort():
                # --- This is a Boolean Assignment ---
                try:
                    # Encodes RHS using *current* SSA vars (e.g., failed_0)
                    encoded_right = fmla_enc(right) 
                except ValueError as e:
                    raise TypeError(f"Type mismatch: Cannot assign non-boolean {right} to boolean var {left.name}") from e

                # Get *new* var term (e.g., failed_1)
                next_var_ast = nextVar(left) # This updates __variableStore__
                new_var_term = z3.Const(next_var_ast.name, target_sort)

                # --- OLD BUGGY CODE ---
                # old_var_term = term_enc(left) 
                # P_sub = z3.substitute(P, [(old_var_term, new_var_term)])
                # return z3.And(new_var_term == encoded_right, P_sub)

                # --- NEW FIX ---
                # The new SP is just the new constraint AND'd with the old predicate.
                return z3.And(new_var_term == encoded_right, P)

            else:
                # --- This is a Term (BitVec/Struct) Assignment ---
                try:
                    # Encodes RHS using *current* SSA vars (e.g., sum_0 + num_0)
                    encoded_right = term_enc(right)
                except ValueError as e:
                    raise TypeError(f"Type mismatch: Cannot assign formula {right} to non-boolean var {left.name}") from e
                
                if encoded_right.sort() != target_sort:
                    raise TypeError(f"Type mismatch in assignment to '{left.name}': Cannot assign {encoded_right.sort()} to {target_sort}.")
                
                # Get *new* var term (e.g., sum_1)
                next_var_ast = nextVar(left) # This updates __variableStore__
                new_var_term = z3.Const(next_var_ast.name, target_sort)

                # --- OLD BUGGY CODE ---
                # old_var_term = term_enc(left) 
                # P_sub = z3.substitute(P, [(old_var_term, new_var_term)])
                # return z3.And(new_var_term == encoded_right, P_sub)
                
                # --- NEW FIX ---
                return z3.And(new_var_term == encoded_right, P)
        
        case Seq(alpha, beta):
            return SP(beta, SP(alpha, P, max_depth), max_depth)
        
        case Assert(Q):            
            return z3.And(fmla_enc(Q), P)
        
        case Choice(condition, alpha, beta):
            cond = fmla_enc(condition)
            P1 = z3.simplify(z3.And(P, cond))
            P2 = z3.simplify(z3.And(P, z3.Not(cond)))
        
            post_alpha = SP(alpha, P1, max_depth)
            post_beta = SP(beta, P2, max_depth)
        
            if __is_satisfiable__(P1) and __is_satisfiable__(P2):
                return z3.Or(post_alpha, post_beta) # both feasible
            elif __is_satisfiable__(P1):
                return post_alpha
            elif __is_satisfiable__(P2):
                return post_beta
            else:
                return z3.BoolVal(False)  # Both infeasible, dead code

        case While(condition, body, invariant, measure):
            cond = fmla_enc(condition)
            I    = fmla_enc(invariant)
        
            # pick depth as you already do
            depth = eval_measure_if_possible(measure, P) or max_depth
            try:
                concrete = z3.simplify(term_enc(measure))
                if is_int_value(concrete):
                    depth = int(str(concrete))
            except:
                pass
        
            # quick base: no budget ⇒ only exit if ¬C is feasible
            if depth == 0:
                P_notC = z3.simplify(z3.And(P, z3.Not(cond)))
                return P_notC if __is_satisfiable__(P_notC) else BoolVal(False)
        
            # feasibility checks for pruning
            P_C    = z3.simplify(z3.And(P, cond))
            P_notC = z3.simplify(z3.And(P, z3.Not(cond)))
            feas_C    = __is_satisfiable__(P_C)
            feas_notC = __is_satisfiable__(P_notC)
        
            # if both infeasible, dead code
            if not feas_C and not feas_notC:
                return z3.BoolVal(False)
        
            # left branch: immediate exit (ensure P is included for consistency)
            stop_now = z3.And(P, I, z3.Not(cond))
        
            if depth == 1:
                # right branch: one iteration
                body_once = SP(body, P_C)
        
                # prune based on feasibility
                if feas_notC and not feas_C:
                    return stop_now
                if feas_C and not feas_notC:
                    return body_once
                # both feasible: keep the disjunction
                return z3.Or(stop_now, body_once)
        
            # depth > 1: unfold
            unfolded = SP(
                Seq(body, While(condition, body, invariant, measure)),
                P_C,
                max_depth=depth - 1
            )
        
            # prune based on feasibility
            if feas_notC and not feas_C:
                return stop_now
            if feas_C and not feas_notC:
                return unfolded
            return z3.Or(stop_now, unfolded)