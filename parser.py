from lark import Transformer, v_args, Token
from labsAst import *
from z3 import IntSort, BoolSort, ArraySort, SortRef, ArraySortRef, Datatype, BitVecSort

__function_sigs__ = {}
__symbol_table__ = {}
__constants__ = []
__z3_structs__ = {}  # struct name → Z3 DatatypeRef

def reset_parser_globals():
    """Resets all global state tables used by the parser."""
    global __function_sigs__, __symbol_table__, __constants__, __z3_structs__
    __function_sigs__ = {}
    __symbol_table__ = {}
    __constants__ = []
    __z3_structs__ = {}

def dump_symTab():
    global __symbol_table__
    print(__symbol_table__)

def dump_z3_structs():
    global __z3_structs__
    print(__z3_structs__)

def resolve_sort(t):
    if isinstance(t, SortRef):
        return t
        # return BitVecSort(32)
    if t == "uint8":
        return BitVecSort(8)
    if t == "uint16":
        return BitVecSort(16)
    if t == "uint32":
        return BitVecSort(32)
    if t == "uint64":
        return BitVecSort(64)
    if t == "bool":
        return BoolSort()
    if t.startswith("array[") and t.endswith("]"):
        val_type = t[6:-1].strip()
        return ArraySort(BitVecSort(32), resolve_sort(val_type))
    if t in __z3_structs__:
        return __z3_structs__[t]
    raise TypeError(f"Unknown type '{t}'. Allowed: 'uint8 | uint16 | uint32 | uint64', 'bool', 'array[T]', or a declared struct name.")

def create_z3_sort(struct: StructDef):
    sort = Datatype(struct.name)
    fields = [(f.name, resolve_sort(f.type)) for f in struct.fields]
    sort.declare(f"{struct.name}_ctor", *fields)
    return sort.create()

@v_args(inline=True)
class AstTransformer(Transformer):
    def _create_sequence(self, stmts):
        # Flatten into Seq nodes
        if not stmts:
            return Skip()
        if len(stmts) == 1:
            return stmts[0]
        prog = Seq(stmts[0], stmts[1])
        for s in stmts[2:]:
            prog = Seq(prog, s)
        return prog

    def structured_program(self, decls, inits, preconds, postconds, body):
        # Flatten program (init + body) and preconditions (default TrueC)
        all_statements = inits + body
        program = self._create_sequence(all_statements)

        if not preconds:
            pre = TrueC()
        elif len(preconds) == 1:
            pre = preconds[0]
        else:
            pre = AndF(preconds[0], preconds[1])
            for f in preconds[2:]:
                pre = AndF(pre, f)

        post = TrueC() if not postconds else postconds[0]
        for f in postconds[1:]:
            post = AndF(post, f)

        return StructuredProgram(precondition=pre, postcondition=post, program=program)

    def declarations_section(self, *items):
        return [x for x in items if x is not None]

    def function_sig(self, *args):
        return list(args)

    def initialisation_section(self, *items):
        return list(items)

    def preconditions_section(self, *items):
        return [f for f in items if isinstance(f, Formula)]
        
    def postconditions_section(self, *items):
        return [f for f in items if isinstance(f, Formula)]

    def program_section(self, *items):
        return list(items)

    def new_assignment(self, lvalue, typename):
        struct_name = typename.value
        var_name = lvalue.name
        if struct_name not in __z3_structs__:
            raise TypeError(f"Cannot create new instance of undeclared struct: {struct_name}")
        z3_sort = __z3_structs__[struct_name]
        __symbol_table__[var_name] = z3_sort
        if struct_name in __z3_structs__:
            for i in range(z3_sort.constructor(0).arity()):
                accessor = z3_sort.accessor(0, i)
                field_name = accessor.name()
                qualified_name = f"{var_name}.{field_name}"
                __symbol_table__[qualified_name] = resolve_sort(accessor.range())
    
        return NewAssignment(lvalue, struct_name)
    
    def field(self, name_tok, type_tok):
        # print("[DEBUG FIELD]: ", name_tok.value, resolve_sort(type_tok))
        return StructField(name_tok.value, resolve_sort(type_tok))

    def var_decl(self, name, type_sort):
        __symbol_table__[name.value] = resolve_sort(type_sort)
        return VarDecl(name.value)

    def const_decl(self, name_tok, type_sort):
        name = name_tok.value
        __symbol_table__[name] = resolve_sort(type_sort)
        __constants__.append(name)
        return ConstDecl(name)

    def assignment(self, lvalue, expr):
        if lvalue.name in __constants__:
            raise ValueError(f"Cannot assign to constant: {lvalue.name}")
        return Asgn(lvalue, expr)

    def assert_statement(self, f):
        return Assert(f)

    def skip(self): return Skip()

    def lvalue(self, *parts):
        try:
            name = ".".join(p.value for p in parts)
        except Exception as e:
            print("lvalue parts =", parts)
            raise
        return Var(name)

    def var(self, x):
        if isinstance(x, Token):
            return Var(x.value)
        return x  # Already a Var or something else
        
    # def number(self, x): return Const(int(x.value))
    def number(self, *args):
        # This will receive either (value,) or (value, suffix)
        
        # 1. Unpack the arguments
        value_token = args[0]
        suffix_token = args[1] if len(args) > 1 else None

        # 2. Get the integer value
        val = int(value_token.value)

        # 3. Determine the suffix string
        suffix_str = "u32"  # Default to u32
        if suffix_token:
            suffix_str = suffix_token.value  # e.g., "u8"
            
        # 4. Return the tuple that LABSCore.py expects
        return Const((val, suffix_str))

    def sum(self, a, b): return Sum(a, b)
    def difference(self, a, b): return Difference(a, b)
    def product(self, a, b): return Product(a, b)
    def division(self, a, b): return Division(a, b)
    def mod(self, a, b): return Mod(a, b)
    def neg_op(self, x): return Difference(Const(0), x)

    def true_const(self): return TrueC()
    def false_const(self): return FalseC()

    def andf(self, a, b): return AndF(a, b)
    def orf(self, a, b): return OrF(a, b)
    def impliesf(self, a, b): return ImpliesF(a, b)
    def notf(self, x): return NotF(x)
    def eqf(self, a, b): return EqF(a, b)
    def neqf(self, a, b): return NotF(EqF(a, b))
    def gtf(self, a, b): return GtF(a, b)
    def ltf(self, a, b): return LtF(a, b)
    def gef(self, a, b): return GeF(a, b)
    def lef(self, a, b): return LeF(a, b)

    def function_call(self, name, *args):
        fname = name.value
        expected_types = __function_sigs__.get(fname)
        if not expected_types:
            raise ValueError(f"Function '{fname}' not declared.")
    
        arg_types = []
        for arg in args:
            if isinstance(arg, Var):
                if arg.name in __symbol_table__:
                    arg_type = __symbol_table__[arg.name]
                #elif "." in arg.name:
                    #arg_type = BitVecSort(32)  # fallback for flattened field access
                else:
                    raise TypeError(f"Undeclared variable '{arg.name}' used in call to '{fname}'")
                arg_types.append(arg_type)
            elif isinstance(arg, Const):
                arg_types.append(BitVecSort(32))
            else:
                arg_types.append(BitVecSort(32))  # default fallback
    
        if len(arg_types) != len(expected_types) - 1:
            raise TypeError(f"Function '{fname}' expects {len(expected_types)-1} arguments, got {len(arg_types)}")
    
        for i, (actual, expected) in enumerate(zip(arg_types, expected_types[:-1])):
            # print("[DEBUG FUNCTIONCALL]: ", expected)
            if resolve_sort(actual) != resolve_sort(expected):
                raise TypeError(
                    f"Function '{fname}' arg {i+1}: expected {expected}, got {actual}"
                )
    
        return Fn(fname, list(args))

    def user_type(self, tok):
        return str(tok)

    def if_statement(self, cond, true_block, false_block=None):
        return Choice(cond, true_block, false_block or Skip())

    '''def while_loop(self, cond, invariant_formula=None, measure_expr=None, body=None):
        invariant = invariant_formula if invariant_formula else TrueC()
        measure = measure_expr or Const(1)  # fallback if no measure provided
        return While(cond, body, invariant, measure)'''
    def while_loop(self, cond, *args):
        invariant = TrueC()
        measure = Const(1)
        body = None
    
        for a in args:
            if isinstance(a, Formula):
                invariant = a
            elif isinstance(a, Term):
                measure = a
            else:
                body = a
    
        return While(cond, body, invariant, measure)


    def block(self, *stmts):
        return self._create_sequence(list(stmts))

    def statement(self, stmt):
        return stmt

    def array_decl(self, name, value_type):
        typename = f"array[{value_type}]"
        z3_sort = resolve_sort(typename)
        __symbol_table__[name.value] = z3_sort
        return ArrayDecl(name.value, "uint32", value_type)

    '''def function_decl(self, name_tok, arg_sorts, ret_sort):
        name = name_tok.value
        __function_sigs__[name] = list(arg_sorts) + [ret_sort]
        return None'''
    def function_decl(self, name_tok, arg_sorts, ret_sort):
        name = name_tok.value
        resolved = [resolve_sort(t) for t in list(arg_sorts) + [ret_sort]]
        __function_sigs__[name] = resolved
        return None
        
    def forallf(self, var_tok, f):
        return ForAllF(var_tok.value, f)
    
    def existsf(self, var_tok, f):
        return ExistsF(var_tok.value, f)

    def uint8_type(self): return BitVecSort(8)
    def uint16_type(self): return BitVecSort(16)
    def uint32_type(self): return BitVecSort(32)
    def uint64_type(self): return BitVecSort(64)
    def bool_type(self): return BoolSort()
    def array_type(self, value_type):
        return f"array[{value_type}]"

    def struct_def(self, name_tok, *field_tuples):
        fields = list(field_tuples)
        struct = StructDef(name_tok.value, fields)
        __z3_structs__[struct.name] = create_z3_sort(struct)
        return struct

    def bit_not(self, x):
        return BitNot(x)
        
    def bit_and(self, *children):
        if len(children) == 1:
            return children[0]
        left, right = children
        return BitAnd(left, right)

    def bit_xor(self, *children):
        if len(children) == 1:
            return children[0]
        left, right = children
        return BitXor(left, right)

    def bit_or(self, *children):
        if len(children) == 1:
            return children[0]
        left, right = children
        return BitOr(left, right)

    # shifts always have two children
    def shl(self, left, right):
        return Shl(left, right)

    def lshr(self, left, right):
        return LShr(left, right)
    
    def add(self, x):
        return x
    
    def shift(self, x):
        return x