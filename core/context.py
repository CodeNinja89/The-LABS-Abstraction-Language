from __future__ import annotations
import z3
import copy
from core.ast import StructDef

class LabsContext:
    """
    Holds all shared state for the LABS parsing, encoding, and transformation 
    process. This replaces all the global variables.
    """
    
    def __init__(self):
        # Maps: var_name (str) -> z3_sort (SortRef)
        self.symbol_table: dict[str, z3.SortRef] = {}

        # Maps: func_name (str) -> list[z3.SortRef] (last is return type)
        self.function_sigs: dict[str, list[z3.SortRef]] = {}
        
        # Maps: struct_name (str) -> z3_datatype (DatatypeRef)
        self.struct_defs: dict[str, z3.DatatypeRef] = {}
        
        # A simple list of const variable names
        self.constants: list[str] = []
        
        # Maps: var_name (str) -> current_version (int)
        self.variable_versions: dict[str, int] = {}

    def __repr__(self):
        return (f"LabsContext(\n"
                f"  Symbols: {list(self.symbol_table.keys())}\n"
                f"  Functions: {list(self.function_sigs.keys())}\n"
                f"  Structs: {list(self.struct_defs.keys())}\n"
                f"  Versions: {self.variable_versions}\n)")

    # --- Methods for Parser (Phase 2) ---
    
    def resolve_sort(self, type_name: str | z3.SortRef) -> z3.SortRef:
        """
        Translates a type name (e.g., 'uint32', 'messageQ') into a Z3 Sort.
        This logic is moved from the top of parser.py.
        """
        # --- This logic is from parser.py ---
        if isinstance(type_name, z3.SortRef):
            return type_name
        if type_name == "uint8":
            return z3.BitVecSort(8)
        if type_name == "uint16":
            return z3.BitVecSort(16)
        if type_name == "uint32":
            return z3.BitVecSort(32)
        if type_name == "uint64":
            return z3.BitVecSort(64)
        if type_name == "bool":
            return z3.BoolSort()
        if type_name.startswith("array[") and type_name.endswith("]"):
            val_type = type_name[6:-1].strip()
            # Note: Z3 arrays require a domain (index) sort. We'll default to 
            # 32-bit BitVecs for array indices, as seen in the parser.py logic.
            return z3.ArraySort(z3.BitVecSort(32), self.resolve_sort(val_type))
        if type_name in self.struct_defs:
            return self.struct_defs[type_name]
        
        raise TypeError(f"Unknown type '{type_name}'.")
        # --- End of logic from parser.py ---

    def register_variable(self, name: str, sort: z3.SortRef, is_const=False):
        """
        Adds a variable to the symbol table and initializes its SSA version.
        """
        if name in self.symbol_table:
            raise ValueError(f"Variable '{name}' already declared.")
            
        self.symbol_table[name] = sort
        
        # All variables, even struct instances, start at version 0
        self.variable_versions[name] = 0 
        
        if is_const:
            self.constants.append(name)

    def register_function(self, name: str, signature: list[z3.SortRef]):
        """Adds a function signature."""
        if name in self.function_sigs:
            raise ValueError(f"Function '{name}' already declared.")
        self.function_sigs[name] = signature

    def _create_z3_datatype(self, struct_node: StructDef) -> z3.DatatypeRef:
        """
        Helper function to create the Z3 Datatype.
        Logic from create_z3_sort in parser.py.
       
        """
        sort = z3.Datatype(struct_node.name)
        fields = []
        for f in struct_node.fields:
            # We must resolve the field type *before* declaring it
            field_sort = self.resolve_sort(f.type)
            fields.append((f.name, field_sort))
            
        sort.declare(f"{struct_node.name}_ctor", *fields)
        return sort.create()

    def register_struct(self, struct_node: StructDef):
        """
        Creates the Z3 Datatype for a struct and registers it.
        """
        if struct_node.name in self.struct_defs:
            raise ValueError(f"Struct '{struct_node.name}' already declared.")
        
        # Create and register the Z3 datatype
        z3_datatype = self._create_z3_datatype(struct_node)
        self.struct_defs[struct_node.name] = z3_datatype

    def register_struct_instance(self, instance_name: str, struct_name: str):
        """
        Registers a *new instance* of a struct (from 'x := new message').
        This also populates the symbol table for field access (e.g., 'x.toCore').
        """
        if struct_name not in self.struct_defs:
            raise TypeError(f"Cannot create new instance of undeclared struct: {struct_name}")
            
        z3_sort = self.struct_defs[struct_name]
        
        # Register the main instance variable (e.g., 'msg')
        self.register_variable(instance_name, z3_sort)

        # --- Logic from parser.py's new_assignment ---
        # Register all its fields in the symbol table for type-checking
        # This allows the parser to know 'msg.toCore' is a uint32
        for i in range(z3_sort.constructor(0).arity()):
            accessor = z3_sort.accessor(0, i)
            field_name = accessor.name()
            qualified_name = f"{instance_name}.{field_name}"
            
            # We're just registering the *type* of the field access
            # The SSA logic will handle versioning of 'msg'
            self.symbol_table[qualified_name] = accessor.range()
        # --- End of logic from parser.py ---

    # --- Methods for SPTransformer (Phase 3) ---
    # (Stubs remain for now)
    def _get_ssa_name(self, base_name: str, version: int) -> str:
        """Helper to construct the versioned name."""
        return f"{base_name}_{version}"

    def get_ssa_var_term(self, base_name: str) -> z3.ConstRef:
        """
        Gets the Z3 Const term for the *current* SSA version (e.g., 'x_0').
        This is used by the Z3Encoder.
        """
        if base_name not in self.symbol_table:
            # This can happen for undeclared vars like in quantifiers
            # We'll assume uint32, mimicking the old term_enc logic
            #
            return z3.BitVec(base_name, 32)

        sort = self.symbol_table[base_name]
        version = self.variable_versions.get(base_name, 0)
        ssa_name = self._get_ssa_name(base_name, version)
        
        return z3.Const(ssa_name, sort)

    def next_ssa_var_term(self, base_name: str) -> z3.ConstRef:
        """
        Increments the SSA version for a var and returns the *new* Z3 Const 
        term (e.g., 'x_1'). This is used by the SPTransformer for assignments.
        """
        if base_name not in self.symbol_table:
            raise ValueError(f"Cannot assign to undeclared variable '{base_name}'")
        
        # Get current version and increment
        # This logic is from LABSCore.py's nextVar
        current_version = self.variable_versions.get(base_name, 0)
        new_version = current_version + 1
        self.variable_versions[base_name] = new_version
        
        # Get the variable's sort and create the new Z3 term
        sort = self.symbol_table[base_name]
        new_ssa_name = self._get_ssa_name(base_name, new_version)
        
        return z3.Const(new_ssa_name, sort)

    def fork(self) -> LabsContext:
        """
        Creates a deep copy of this context, used for branching (if/else).
        This copies the *entire* state, especially the variable versions.
        """
        # We use deepcopy to ensure all dictionaries are new
        new_context = LabsContext()
        new_context.symbol_table = copy.deepcopy(self.symbol_table)
        new_context.function_sigs = copy.deepcopy(self.function_sigs)
        new_context.struct_defs = copy.deepcopy(self.struct_defs)
        new_context.constants = copy.deepcopy(self.constants)
        new_context.variable_versions = copy.deepcopy(self.variable_versions)
        return new_context

    def merge(self, cond: z3.BoolRef, 
              then_ctx: LabsContext, 
              else_ctx: LabsContext) -> list[z3.BoolRef]:
        """
        Merges 'then_ctx' and 'else_ctx' into this (the 'before') context.
        Returns:
            A list of Z3 'phi' formulas (e.g., [x_2 == If(cond, x_1, x_0)]).
        """
        phi_nodes = []
        
        # Find all variables modified in *either* branch
        all_modified_vars = set(then_ctx.variable_versions.keys()) | \
                            set(else_ctx.variable_versions.keys())

        for var_name in all_modified_vars:
            # Get the version from all three states
            ver_before = self.variable_versions.get(var_name, -1)
            ver_then = then_ctx.variable_versions.get(var_name, ver_before)
            ver_else = else_ctx.variable_versions.get(var_name, ver_before)

            if ver_then == ver_else:
                # Both branches agree (or neither touched it)
                self.variable_versions[var_name] = ver_then
                continue

            # --- State Conflict: Build a Phi Node ---
            
            # 1. Get the Z3 sort for this variable
            sort = self.symbol_table[var_name]
            
            # 2. Get the terms for the 'then' and 'else' versions
            term_then = z3.Const(self._get_ssa_name(var_name, ver_then), sort)
            term_else = z3.Const(self._get_ssa_name(var_name, ver_else), sort)
            
            # 3. Create a *new* merged version
            new_ver = max(ver_then, ver_else) + 1
            new_term = z3.Const(self._get_ssa_name(var_name, new_ver), sort)
            
            # 4. Create the Phi formula: new_var = If(cond, var_then, var_else)
            phi = (new_term == z3.If(cond, term_then, term_else))
            phi_nodes.append(phi)
            
            # 5. Update this context's state for subsequent statements
            self.variable_versions[var_name] = new_ver

        return phi_nodes