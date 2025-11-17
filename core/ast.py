# labsAst.py
# Defines all data classes for the Abstract Syntax Tree (AST).

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Union

@dataclass
class Node:
    pass

@dataclass
class Prog(Node):
    pass

# --- Term Nodes ---
@dataclass
class Const(Node): value: any
@dataclass
class Var(Node): name: str
@dataclass
class Sum(Node): left: 'Term'; right: 'Term'
@dataclass
class Difference(Node): left: 'Term'; right: 'Term'
@dataclass
class Product(Node): left: 'Term'; right: 'Term'
@dataclass
class Division(Node): left: 'Term'; right: 'Term'
@dataclass
class Mod(Node): left: 'Term'; right: 'Term'
@dataclass
class Fn(Node): name: str; args: List['Term']
    
# --- bitwise unary ---
@dataclass
class BitNot(Node):
    x: 'Term'

# --- bitwise binary ---
@dataclass
class BitAnd(Node):
    l: 'Term'
    r: 'Term'

@dataclass
class BitXor(Node):
    l: 'Term'
    r: 'Term'

@dataclass
class BitOr(Node):
    l: 'Term'
    r: 'Term'

# --- shifts (logical right shift; left shift) ---
@dataclass
class Shl(Node):
    l: 'Term'
    r: 'Term'

@dataclass
class LShr(Node):  # logical right shift (maps to Z3 LShR)
    l: 'Term'
    r: 'Term'


Term = Union[Const, Var, Fn, Sum, Difference, Product, Division, Mod, BitNot, BitAnd, BitXor, BitOr, Shl, LShr]

# --- Formula Nodes ---
@dataclass
class TrueC(Node): _: None = None
@dataclass
class FalseC(Node): _: None = None
@dataclass
class LtF(Node): left: Term; right: Term
@dataclass
class LeF(Node): left: Term; right: Term
@dataclass
class GtF(Node): left: Term; right: Term
@dataclass
class GeF(Node): left: Term; right: Term
@dataclass
class EqF(Node): left: Term; right: Term
@dataclass
class NotF(Node): q: 'Formula'
@dataclass
class AndF(Node): p: 'Formula'; q: 'Formula'
@dataclass
class OrF(Node): p: 'Formula'; q: 'Formula'
@dataclass
class ImpliesF(Node): p: 'Formula'; q: 'Formula'

@dataclass
class ForAllF(Node):
    var: str
    body: Formula

@dataclass
class ExistsF(Node):
    var: str
    body: Formula

Formula = Union[TrueC, FalseC, LtF, GtF, LeF, GeF, EqF, NotF, AndF, OrF, ImpliesF, ForAllF, ExistsF]

# --- Program & Declaration Nodes ---
@dataclass
class Asgn(Prog): left: Var; right: Term
@dataclass
class Seq(Prog): alpha: Prog; beta: Prog
@dataclass
class Assert(Prog): q: Formula
@dataclass
class Choice(Prog): condition: Formula; alpha: Prog; beta: Prog
@dataclass
class While(Prog): condition: Formula; alpha: Prog; invariant: Formula; measure: Term
@dataclass
class Skip(Prog): _: None = None
# These are treated as program nodes so they can be parsed in sequence
@dataclass
class StructDef(Prog): name: str; fields: list
@dataclass
class NewAssignment(Prog): left: Var; type_name: str

Program = Union[Asgn, Seq, Assert, Choice, While, Skip, StructDef, NewAssignment]

@dataclass
class StructuredProgram(Node):
    precondition: Formula
    postcondition: Formula
    program: Prog

@dataclass
class ArrayDecl(Prog):
    name: str
    index_sort: str
    value_sort: str

@dataclass
class VarDecl(Prog):
    name: str

@dataclass
class StructField:
    name: str
    type: str

@dataclass
class ConstDecl(Prog):
    name: str