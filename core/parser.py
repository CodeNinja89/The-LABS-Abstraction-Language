from lark import Transformer, v_args, Token
import z3

# Import our new AST node definitions and the context
from core.ast import *
from core.context import LabsContext

@v_args(inline=True)
class AstTransformer(Transformer):

    def __init__(self, context: LabsContext):
        """
        The transformer is initialized with a LabsContext object.
        It no longer knows about any global state.
        """
        self.context = context
        super().__init__()

    # --- Helper for creating sequences (e.g., in blocks) ---
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

    # --- Program Structure ---
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

    def initialisation_section(self, *items):
        return list(items)

    def preconditions_section(self, *items):
        return [f for f in items if isinstance(f, Formula)]
        
    def postconditions_section(self, *items):
        return [f for f in items if isinstance(f, Formula)]

    def program_section(self, *items):
        return list(items)

    def function_sig(self, *args):
        # Returns a list of Z3 sorts
        return list(args)

    # --- Type Resolution (Now uses context) ---
    def uint8_type(self): return self.context.resolve_sort("uint8")
    def uint16_type(self): return self.context.resolve_sort("uint16")
    def uint32_type(self): return self.context.resolve_sort("uint32")
    def uint64_type(self): return self.context.resolve_sort("uint64")
    def bool_type(self): return self.context.resolve_sort("bool")
    
    def user_type(self, tok):
        # We just pass the string name; context will resolve it later
        return str(tok)

    def array_type(self, value_type):
        # value_type is either a string or a Z3 sort.
        # We create the string representation for the context to resolve.
        return f"array[{value_type}]"

    # --- Declarations (Now register with context) ---

    def var_decl(self, name, type_sort_or_str):
        # Resolve the sort using the context
        resolved_sort = self.context.resolve_sort(type_sort_or_str)
        self.context.register_variable(name.value, resolved_sort)
        return VarDecl(name.value) # Return AST node

    def const_decl(self, name_tok, type_sort_or_str):
        name = name_tok.value
        resolved_sort = self.context.resolve_sort(type_sort_or_str)
        self.context.register_variable(name, resolved_sort, is_const=True)
        return ConstDecl(name) # Return AST node

    def array_decl(self, name, value_type_str):
        typename = f"array[{value_type_str}]"
        z3_sort = self.context.resolve_sort(typename)
        self.context.register_variable(name.value, z3_sort)
        return ArrayDecl(name.value, "uint32", value_type_str)

    def function_decl(self, name_tok, arg_sorts, ret_sort):
        name = name_tok.value
        all_types = list(arg_sorts) + [ret_sort]
        resolved_sig = [self.context.resolve_sort(t) for t in all_types]
        
        self.context.register_function(name, resolved_sig)
        return None # No AST node needed

    def struct_def(self, name_tok, *field_tuples):
        fields = list(field_tuples)
        struct = StructDef(name_tok.value, fields)
        # Register the struct definition with the context
        self.context.register_struct(struct)
        return struct # Return AST node

    def field(self, name_tok, type_sort_or_str):
        # Resolve the sort using the context
        resolved_sort = self.context.resolve_sort(type_sort_or_str)
        return StructField(name_tok.value, resolved_sort)

    def new_assignment(self, lvalue, typename):
        struct_name = typename.value
        var_name = lvalue.name
        
        # We just tell the context to register the new instance
        # This will also register field accesses like 'var.field'
        self.context.register_struct_instance(var_name, struct_name)
    
        return NewAssignment(lvalue, struct_name) # Return AST node

    # --- Statements ---
    
    def assignment(self, lvalue, expr):
        # Check against the context's list of constants
        if lvalue.name in self.context.constants:
            raise ValueError(f"Cannot assign to constant: {lvalue.name}")
        return Asgn(lvalue, expr)

    def assert_statement(self, f):
        return Assert(f)

    def skip(self): 
        return Skip()

    def lvalue(self, *parts):
        # Logic from parser.py
        try:
            name = ".".join(p.value for p in parts)
        except Exception as e:
            print("lvalue parts =", parts)
            raise
        return Var(name)

    def if_statement(self, cond, true_block, false_block=None):
        return Choice(cond, true_block, false_block or Skip())

    def while_loop(self, cond, *args):
        # Logic from parser.py
        invariant = TrueC()
        measure = Const(1)
        body = None
    
        for a in args:
            if isinstance(a, Formula):
                invariant = a
            elif isinstance(a, Term):
                measure = a
            else:
                body = a # This should be the block
    
        return While(cond, body, invariant, measure)

    def block(self, *stmts):
        return self._create_sequence(list(stmts))

    def statement(self, stmt):
        return stmt

    # --- Formulas (Create AST nodes) ---
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
    def forallf(self, var_tok, f): return ForAllF(var_tok.value, f)
    def existsf(self, var_tok, f): return ExistsF(var_tok.value, f)

    # --- Terms (Create AST nodes) ---
    def var(self, x):
        if isinstance(x, Token):
            return Var(x.value)
        return x  # Already a Var

    def number(self, *args):
        # Logic from parser.py
        value_token = args[0]
        suffix_token = args[1] if len(args) > 1 else None
        val = int(value_token.value)
        suffix_str = "u32"  # Default
        if suffix_token:
            suffix_str = suffix_token.value
        return Const((val, suffix_str)) # Store as tuple

    def true_const(self): return TrueC()
    def false_const(self): return FalseC()
    
    def sum(self, a, b): return Sum(a, b)
    def difference(self, a, b): return Difference(a, b)
    def product(self, a, b): return Product(a, b)
    def division(self, a, b): return Division(a, b)
    def mod(self, a, b): return Mod(a, b)
    def neg_op(self, x): return Difference(Const(0), x) # Re-using Const(0) logic

    # --- Bitwise (Create AST nodes) ---
    def bit_not(self, x): return BitNot(x)
    def bit_and(self, *children):
        if len(children) == 1: return children[0]
        return BitAnd(children[0], children[1])
    def bit_xor(self, *children):
        if len(children) == 1: return children[0]
        return BitXor(children[0], children[1])
    def bit_or(self, *children):
        if len(children) == 1: return children[0]
        return BitOr(children[0], children[1])

    def shl(self, left, right): return Shl(left, right)
    def lshr(self, left, right): return LShr(left, right)
    
    # --- Grammar pass-throughs ---
    def add(self, x): return x
    def shift(self, x): return x

    # --- Function Call (Now uses context for validation) ---
    def function_call(self, name, *args):
        fname = name.value
        
        # Check against the context's function signatures
        expected_types = self.context.function_sigs.get(fname)
        if not expected_types:
            raise ValueError(f"Function '{fname}' not declared.")
    
        arg_types = []
        for arg in args:
            if isinstance(arg, Var):
                if arg.name in self.context.symbol_table:
                    arg_type = self.context.symbol_table[arg.name]
                else:
                    raise TypeError(f"Undeclared variable '{arg.name}' used in call to '{fname}'")
                arg_types.append(arg_type)
            elif isinstance(arg, Const):
                # Infer type from const suffix
                _, suffix = arg.value
                arg_types.append(self.context.resolve_sort(suffix))
            else:
                # This is a fallback for complex terms (e.g., x + y)
                # A full type-checker would infer the result type.
                # For now, we'll default to uint32.
                arg_types.append(self.context.resolve_sort("uint32"))
    
        if len(arg_types) != len(expected_types) - 1:
            raise TypeError(f"Function '{fname}' expects {len(expected_types)-1} arguments, got {len(arg_types)}")
    
        for i, (actual, expected) in enumerate(zip(arg_types, expected_types[:-1])):
            if actual != expected:
                raise TypeError(
                    f"Function '{fname}' arg {i+1}: expected {expected}, got {actual}"
                )
    
        return Fn(fname, list(args)) # Return AST node