import argparse
import pathlib
import sys
from copy import deepcopy
from typing import Any, Dict, List, Union
from uc.uc_ast import *
from uc.uc_parser import UCParser
from uc.uc_type import VoidType, CharType, IntType, BoolType, StringType, ArrayType, FuncType


class SymbolTable:
    """Class representing a symbol table.

    `add` and `lookup` methods are given, however you still need to find a way to 
    deal with scopes.

    ## Attributes
    - :attr data: the content of the SymbolTable
    """

    def __init__(self) -> None:
        """ Initializes the SymbolTable. """
        self.__data = dict()

    @property
    def data(self) -> Dict[str, Any]:
        """ Returns a copy of the SymbolTable.
        """
        return deepcopy(self.__data)

    def add(self, name: str, value: Any) -> None:
        """ Adds to the SymbolTable.

        ## Parameters
        - :param name: the identifier on the SymbolTable
        - :param value: the value to assign to the given `name`
        """
        self.__data[name] = value

    def lookup(self, name: str) -> Union[Any, None]:
        """ Searches `name` on the SymbolTable and returns the value
        assigned to it.

        ## Parameters
        - :param name: the identifier that will be searched on the SymbolTable

        ## Return
        - :return: the value assigned to `name` on the SymbolTable. If `name` is not found, `None` is returned.
        """
        return self.__data.get(name)

class STStack:
    def __init__(self) -> None:
        self.tables: List[SymbolTable] = []
    
    @property
    def data(self) -> List[Dict[str, Any]]:
        return [table.data for table in self.tables]
    
    def add(self, name: str, value: Any) -> None:
        self.tables[-1].add(name, value)
    
    def lookup(self, name: str) -> Union[Any, None]:
        for table in self.tables[::-1]:
            v = table.lookup(name)
            if v is not None:
                return v
        
        return None

    def new_context(self) -> None:
        self.tables.append(SymbolTable())
    
    def top_context(self) -> SymbolTable:
        return self.tables[-1]
    
    def pop_context(self) -> None:
        self.tables.pop()
    

# TABLES = STStack()

class NodeVisitor:
    """A base NodeVisitor class for visiting uc_ast nodes.
    Subclass it and define your own visit_XXX methods, where
    XXX is the class name you want to visit with these
    methods.
    """

    _method_cache = None

    def visit(self, node):
        """Visit a node."""

        if self._method_cache is None:
            self._method_cache = {}

        visitor = self._method_cache.get(node.__class__.__name__)
        if visitor is None:
            method = "visit_" + node.__class__.__name__
            visitor = getattr(self, method, self.generic_visit)
            self._method_cache[node.__class__.__name__] = visitor

        return visitor(node)

    def generic_visit(self, node):
        """Called if no explicit visitor function exists for a
        node. Implements preorder visiting of the node.
        """
        for _, child in node.children():
            self.visit(child)


class Visitor(NodeVisitor):
    """
    Program visitor class. This class uses the visitor pattern. You need to define methods
    of the form visit_NodeName() for each kind of AST node that you want to process.
    """

    def __init__(self):
        # Initialize the symbol table
        self.symtab = STStack()
        self.typemap = {
            "int": IntType,
            "char": CharType,
            "bool": BoolType,
            "string": StringType,
            "void": VoidType,
            "array": ArrayType,
            "func": FuncType
            # TODO
        }
        # TODO: Complete...

    def _assert_semantic(self, condition: bool, msg_code: int, coord, name: str = "", ltype="", rtype=""):
        """Check condition, if false print selected error message and exit"""
        error_msgs = {
            1: f"{name} is not defined",
            2: f"subscript must be of type(int), not {ltype}",
            3: "Expression must be of type(bool)",
            4: f"Cannot assign {rtype} to {ltype}",
            5: f"Binary operator {name} does not have matching LHS/RHS types",
            6: f"Binary operator {name} is not supported by {ltype}",
            7: "Break statement must be inside a loop",
            8: "Array dimension mismatch",
            9: f"Size mismatch on {name} initialization",
            10: f"{name} initialization type mismatch",
            11: f"{name} initialization must be a single element",
            12: "Lists have different sizes",
            13: "List & variable have different sizes",
            14: f"conditional expression is {ltype}, not type(bool)",
            15: f"{name} is not a function",
            16: f"no. arguments to call {name} function mismatch",
            17: f"Type mismatch with parameter {name}",
            18: "The condition expression must be of type(bool)",
            19: "Expression must be a constant",
            20: "Expression is not of basic type",
            21: f"{name} does not reference a variable of basic type",
            22: f"{name} is not a variable",
            23: f"Return of {ltype} is incompatible with {rtype} function definition",
            24: f"Name {name} is already defined in this scope",
            25: f"Unary operator {name} is not supported",
        }
        if not condition:
            msg = error_msgs[msg_code]  # invalid msg_code raises Exception
            print("SemanticError: %s %s" % (msg, coord), file=sys.stdout)
            sys.exit(1)

    def visit_Program(self, node):
        # Visit all of the global declarations
        self.symtab.new_context()
        for _decl in node.gdecls:
            self.visit(_decl)
        # TODO: Manage the symbol table
    
    def visit_FuncDef(self, node: FuncDef):
        # Initialize the list of declarations that appears inside loops.
        # Save the reference to current function.
        # Visit the return type of the Function, the function declaration,
        # the parameters, and the function body.
        self.symtab.new_context()
        node.decl.prev = "def"

        self.visit(node.type)
        self.visit(node.decl)

        func_type = self.symtab.lookup("func-temp")
        self.symtab.add(node.decl.name.name, func_type)
        
        self.visit(node.body)
        
        # Asserts edge case where function has no explicit return
        ret_type = self.symtab.lookup("ret-temp")
        self._assert_semantic(
            func_type.type.typename == ret_type.typename,
            23,
            node.body.coord,
            ltype=f"type({ret_type.typename})",
            rtype=f"type({func_type.type.typename})"
        )
        self.symtab.top_context().data.pop("ret-temp")
        self.symtab.pop_context()

        # Adds function to global context
        self.symtab.add(node.decl.name.name, func_type)
    
    def visit_ParamList(self, node: ParamList):
        # Just visit all parameters.

        types_list = []
        for _param in node.params:
            self.visit(_param)
            types_list.append(_param.uc_type)
        node.uc_type = types_list

    def visit_BinaryOp(self, node: BinaryOp):
        # Visit the left and right expression
        self.visit(node.lvalue)
        ltype = node.lvalue.uc_type

        self.visit(node.rvalue)
        rtype = node.rvalue.uc_type

        self._assert_semantic(rtype == ltype, 5, node.coord, node.op)
        if node.op in ltype.binary_ops:
            ops = ltype.binary_ops
            is_bool = 0
        else:
            ops = ltype.rel_ops
            is_bool = 1
        
        # ops = ltype.binary_ops if node.op in ltype.binary_ops else ltype.rel_ops
        self._assert_semantic(
            node.op in ops, 6, node.coord, node.op,
            f"type({ltype.typename})"
        )
        
        node.uc_type = self.typemap["bool"] if is_bool else rtype


        # TODO:
        # - Make sure left and right operands have the same type
        # - Make sure the operation is supported
        # - Assign the result type

    def visit_Assignment(self, node):
        # visit right side
        self.visit(node.rvalue)
        rtype = node.rvalue.uc_type
        # visit left side (must be a location)
        _var = node.lvalue
        self.visit(_var)
        if isinstance(_var, ID):
            self._assert_semantic(_var.scope is not None,
                                  1, node.coord, name=_var.name)
        ltype = node.lvalue.uc_type
        # Check that assignment is allowed
        self._assert_semantic(ltype == rtype, 4, node.coord,
                              ltype=f"type({ltype.typename})", rtype=f"type({rtype.typename})")
        # Check that assign_ops is supported by the type
        self._assert_semantic(
            node.op in ltype.assign_ops, 5, node.coord, name=node.op, ltype=ltype
        )

        node.uc_type = rtype
    
    def visit_GlobalDecl(self, node):
        # Just visit each global declaration.
        for _decl in node.decls:
            if isinstance(_decl.type, FuncDecl):
                _decl.prev = "glob"
            self.visit(_decl)
    
    def visit_Decl(self, node: Decl):
        # Visit the types of the declaration (VarDecl, ArrayDecl, FuncDecl).
        # Check if the function or the variable is defined, otherwise return an error.
        # If there is an initial value defined, visit it.
        
        def assert_init(arr, init, coord):
                arr.size = arr.size if arr.size > 0 else len(init)
                self._assert_semantic(arr.size == len(init), 13, coord)

                size = len(init[0]) if isinstance(init[0], list) else 0
                for e in init:
                    if size != 0: self._assert_semantic(len(e) == size, 12, coord)

                for e in init:
                    if isinstance(e, list): assert_init(arr.type, e, coord)

        if node.init is not None: self.visit(node.init)

        if isinstance(node.type, VarDecl):
            self.visit(node.type)

            # Edge case for var declared in func params
            func_context = None
            for context in self.symtab.tables:
                
                if "func-temp" in context.data:
                    func_context = context
                    break
            if func_context is not None:
                v = func_context.lookup(node.name.name)
                self._assert_semantic(v is None, 24, node.name.coord, node.name.name)

            # STD Case
            v = self.symtab.top_context().lookup(node.name.name)
            if v is None:
                self.symtab.add(node.name.name, node.type.uc_type)
            else:
                self._assert_semantic(False, 24, node.name.coord, node.name.name)
            
            self._assert_semantic(not isinstance(node.init, InitList), 11, node.name.coord, node.name.name)

            if node.init is not None:
                self._assert_semantic(node.init.uc_type == node.type.uc_type, 10, node.name.coord, node.name.name)
            
        if isinstance(node.type, FuncDecl):
            if node.prev != "def":
                self.symtab.new_context()

            self.visit(node.type)

            if node.prev != "def":
                func_type = self.symtab.lookup("func-temp")
                self.symtab.pop_context()
                self.symtab.add("func-temp", func_type)
                self.symtab.add(node.name.name, func_type)


            # TODO: add func to symbol table
        
        if isinstance(node.type, ArrayDecl):
            self.visit(node.type)

            array_type = node.type.uc_type

            if node.init is not None and isinstance(node.init, InitList):
                assert_init(array_type, node.init.uc_type, node.name.coord)
            elif node.init is not None and node.init.type == "string":
                if (array_type.size != 0):
                    self._assert_semantic(array_type.size > len(node.init.value), 8, node.name.coord)
            elif node.init is not None:
                self._assert_semantic(array_type.size == 1, 9, node.name.coord, node.name.name)
            else:
                curr_arr = array_type
                while (isinstance(curr_arr, ArrayType)):
                    self._assert_semantic(curr_arr.size > 0, 8, node.name.coord)
                    curr_arr = curr_arr.type

            self.symtab.add(node.name.name, node.type.uc_type)
            # TODO: add func to symbol table
        
        node.uc_type = node.type.uc_type

    def visit_VarDecl(self, node: VarDecl):
        # First visit the type to adjust the list of types to uCType objects.
        # Then, get the name of variable and make sure it is not defined in the current scope, 
        # otherwise return an error. Next, insert its identifier in the symbol table.
        # Finally, copy the type to the identifier.

        self.visit(node.type)
        node.uc_type = node.type.uc_type

    def visit_ArrayDecl(self, node: ArrayDecl):
        # First visit the type to adjust the list of types to uCType objects.
        # Array is a modifier type, so append this info in the ID object.
        # Visit the array dimension if defined else the dim will be infered after visit initialization in Decl object.

        self.visit(node.type)

        dim = 0
        if node.dim is not None:
            self.visit(node.dim)
            dim = int(node.dim.value)
        
        node.uc_type = ArrayType(node.type.uc_type, dim)



    def visit_FuncDecl(self, node: FuncDecl):
        # Start by visiting the type. Add the function to the symbol table.
        # Then, visit the arguments.
        # Create the type of the function using its return type and the type of its arguments.

        self.visit(node.type)

        # Sets Functions params
        func_type = FuncType(node.type.uc_type, None)
        if node.params is not None:
            self.visit(node.params)
            func_type.parameters = node.params.uc_type
        else:
            func_type.parameters = []

        # Adds function do symtab as stub because its name its not know here
        self.symtab.add("func-temp", func_type)
        node.uc_type = func_type

    def visit_DeclList(self, node: DeclList):
        # Visit all of the declarations that appear inside the statement.
        # Append the declaration to the list of decls in the current function.
        # This list will be used by the code generation to allocate the variables.

        # TODO: Pergunta - "Append the declaration to the list of decls in the current function. 
        # This list will be used by the code generation to allocate the variables." Fazem parte
        # desse lab mesmo?

        for _decl in node.decls:
            self.visit(_decl)


    def visit_Type(self, node: Type):
        # Get the matching basic uCType.

        node.uc_type = self.typemap[node.name]

    def visit_If(self, node: If):
        # First, visit the condition. Then, check if the conditional expression is of boolean type or return a type error. 
        # Finally, visit the statements related to the then, and to the else (in case there are any).

        self.visit(node.cond)
        self._assert_semantic(node.cond.uc_type.typename == "bool", 18, node.cond.coord)

        self.visit(node.iftrue)

        if node.iffalse is not None:
            self.visit(node.iffalse)
        
    def visit_For(self, node: For):
        # Then, visit the initialization, the condition and check if the conditional expression is of boolean type or return a type error.
        # Next, visit the increment (next) and the body of the loop (stmt).

        self.symtab.new_context()
        self.visit(node.init)
        self.visit(node.cond)
        self._assert_semantic(node.cond.uc_type.typename == "bool", 18, node.cond.coord)
        self.visit(node.next)
        self.symtab.add("curr-loop", node)
        self.visit(node.body)
        self.symtab.pop_context()

    def visit_While(self, node: While):

        # Then, visit the condition and check if the conditional expression is of boolean type or return a type error.
        # Finally, visit the body of the while (stmt).

        self.symtab.new_context()
        self.visit(node.cond)
        self._assert_semantic(node.cond.uc_type.typename == "bool", 14, node.coord, ltype=f"type({node.cond.uc_type.typename})")
        self.symtab.add("curr-loop", node)
        self.visit(node.body)
        self.symtab.pop_context()

    def visit_Compound(self, node: Compound):
        # Visit the list of block items (declarations or statements).

        self.symtab.new_context()

        for _block in node.staments:
            self.visit(_block)

        ret_type = self.symtab.lookup("ret-temp")
        self.symtab.pop_context()

        self.symtab.add("ret-temp", ret_type if ret_type is not None else self.typemap["void"])

    # def visit_Assignment(self, node: Assignment):
    #     pass

    def visit_Break(self, node: Break):
        # check the Break statement is inside a loop. If not, it must return an error. Bind it to the current loop node.
        
        curr_loop = self.symtab.lookup("curr-loop")
        self._assert_semantic(curr_loop is not None, 7, node.coord)

        # TODO: Bind it to current loop node

    def visit_FuncCall(self, node: FuncCall):
        # Verify that the given name is a function, or return an error if it is not. Initialize the node type and name using the symbole table. 
        # Check that the number and the type of the arguments correspond to the parameters in the function definition or return an error.
        
        func_type = self.symtab.lookup(node.name.name)
        self._assert_semantic(isinstance(func_type, FuncType), 15, node.name.coord, node.name.name)
        
        # Gets number of arguments of a function
        # node.args can be None, <ID | Constant> or ExprList
        # respectively 0, 1, len arguments
        num_args = 0
        if node.args is not None:
            self.visit(node.args)
            num_args = 1

        if isinstance(node.args, ExprList):
            num_args = len(node.args.exprs)
        
        self._assert_semantic(num_args == len(func_type.parameters), 16, node.coord, node.name.name)

        # Checks if parameters have correct types
        if num_args == 1:
            func_param_type = func_type.parameters[0]
            # #FIXME: If node.args is a binary op assert will be printed with wrong formating
            self._assert_semantic(func_param_type == node.args.uc_type, 17, node.coord, node.args.name if hasattr(node.args, "name") else node.args)
        elif num_args > 1:
            for idx, expr in enumerate(node.args.exprs):
                # FIXME: wrong expression name when expr is not and ID
                name = expr.name if isinstance(expr, ID) else expr
                self._assert_semantic(func_type.parameters[idx] == expr.uc_type, 17, expr.coord, name)
        else:
            pass


        node.uc_type = func_type.type
        
        # TODO: Initialize the node type...

    def visit_Assert(self, node: Assert):
        # Visit the expression and verify it is of boolean type or return a type error.

        self.visit(node.expr)
        self._assert_semantic(node.expr.uc_type.typename == "bool", 3, node.expr.coord)

    def visit_EmptyStatement(self, node: EmptyStatement):
        pass

    def visit_Print(self, node: Print):
        # Just visit each expression and check if it is of basic type. Returns an error otherwise.
        if node.expr is None:
            pass # Print() is always valid
        elif isinstance(node.expr, ExprList):
            for _expr in node.expr.exprs:
                self.visit(_expr)
                self._assert_semantic(_expr.uc_type.typename in ["char", "int", "string"], 20, node.coord)
        else:
            self.visit(node.expr)
            if isinstance(node.expr.uc_type, ArrayType):
                self._assert_semantic(node.expr.uc_type.typename in ["char", "int", "string"], 21, node.expr.coord, node.expr.name)
            else:
                self._assert_semantic(node.expr.uc_type.typename in ["char", "int", "string"], 20, node.expr.coord)

    def visit_Read(self, node: Read):
        # Visit each name and verify that all identifiers used have been defined and are variables.

        name_list = node.names if node.names is isinstance(node.names, list) else [node.names]
        for _name in name_list:
            self.visit(_name)

    def visit_Return(self, node: Return):
        # Visit the expression and check that its type is identical to the return type of the function definition.

        if node.expr is None:
            ret_type = self.typemap["void"]
        else:
            self.visit(node.expr)
            ret_type = node.expr.uc_type

        func_type = self.symtab.lookup("func-temp")
        self._assert_semantic(
            func_type.type.typename == ret_type.typename,
            23,
            node.coord,
            ltype=f"type({ret_type.typename})",
            rtype=f"type({func_type.type.typename})"
        )

        self.symtab.add("ret-temp", ret_type)

    def visit_Constant(self, node: Constant):
        # Get the matching uCType and convert the value to respective type.

        node.uc_type = self.typemap[node.type]

    def visit_ID(self, node: ID):
        # Look for its declaration in the symbol table and bind the ID to it. Also, initialize the type, kind, and scope attributes.
        # TODO: initialize the type, kind, and scope attributes.

        node.uc_type = self.symtab.lookup(node.name)
        self._assert_semantic(node.uc_type is not None, 1, node.coord, node.name)
        node.scope = -1
    
    # def visit_BinaryOp(self, node: BinaryOp):
    #     pass

    def visit_UnaryOp(self, node: UnaryOp):
        # Start by visiting the operand of the operation.
        # Verify the operator of the operation is compatible with the operand type, attempts to use unsupported operators should result in an error.
        # Set the type of the current node representing the unary operation with the same type as the operand.

        self.visit(node.expr)
        node.uc_type = node.expr.uc_type
        self._assert_semantic(
            node.op in node.uc_type.unary_ops, 25, node.coord, node.op
        )

    def visit_ExprList(self, node: ExprList):
        # Visit each element of the list and verify that identifiers have already been defined or return an error.

        types_list = []
        for _expr in node.exprs:
            self.visit(_expr)
            types_list.append(_expr.uc_type)
        node.uc_type = types_list

    def visit_ArrayRef(self, node: ArrayRef):
        # Start by visiting the subscript. If the subscript is an identifier, verify that it has already been defined or return an error.
        # Check that the type of the subscript is integer or return an error. Visit the name and initialize the type of the node.

        self.visit(node.name)
        self.visit(node.subscript)
        
        self._assert_semantic(node.subscript.uc_type == self.typemap["int"], 2, node.subscript.coord, ltype=f"type({node.subscript.uc_type.typename})")
        node.uc_type = node.name.uc_type.type


    def visit_InitList(self, node: InitList):
        # Visit each element of the list. If they are scalar (not InitList), verify they are constants or return an error.

        types_list = []
        for _e in node.exprs:
            self.visit(_e)

            if isinstance(_e, InitList):
                pass
            else:
                self._assert_semantic(isinstance(_e, Constant), 19, _e.coord)
                # TODO: Pergunta - assert if Constant type == Array Type?
            types_list.append(_e.uc_type)
        node.uc_type = types_list


if __name__ == "__main__":
    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file", help="Path to file to be semantically checked", type=str
    )
    args = parser.parse_args()

    # get input path
    input_file = args.input_file
    input_path = pathlib.Path(input_file)

    # check if file exists
    if not input_path.exists():
        print("Input", input_path, "not found", file=sys.stderr)
        sys.exit(1)

    # set error function
    p = UCParser()
    # open file and parse it
    with open(input_path) as f:
        ast = p.parse(f.read())
        sema = Visitor()
        sema.visit(ast)
