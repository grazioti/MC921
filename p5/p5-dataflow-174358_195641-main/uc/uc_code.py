import argparse
import pathlib
import sys
from typing import Dict, List, Tuple
from uc.uc_ast import *
from uc.uc_block import CFG, BasicBlock, Block, ConditionBlock, format_instruction
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor, STStack
from uc.uc_block import *
from uc.uc_type import *


class CodeGenerator(NodeVisitor):
    """
    Node visitor class that creates 3-address encoded instruction sequences
    with Basic Blocks & Control Flow Graph.
    """

    def __init__(self, viewcfg: bool):
        self.viewcfg: bool = viewcfg
        self.current_block: Block = None

        # version dictionary for temporaries. We use the name as a Key
        self.fname: str = "_glob_"
        self.versions: Dict[str, int] = {self.fname: 0}

        # The generated code (list of tuples)
        # At the end of visit_program, we call each function definition to emit
        # the instructions inside basic blocks. The global instructions that
        # are stored in self.text are appended at beginning of the code
        self.code: List[Tuple[str]] = []

        self.text: List[Tuple[str]] = []  # Used for global declarations & constants (list, strings)

        # TODO: Complete if needed.
        self.symtab = STStack()
        self.typemap = {
            "int": IntType,
            "char": CharType,
            "bool": BoolType,
            "string": StringType,
            "void": VoidType,
            "array": ArrayType,
            "func": FuncType
        }
        self.curr_loop = []
        self.exit_block = None
        self.exit_locat = None

    def show(self, buf=sys.stdout):
        _str = ""
        for _code in self.code:
            _str += format_instruction(_code) + "\n"
        buf.write(_str)

    def new_temp(self) -> str:
        """
        Create a new temporary variable of a given scope (function name).
        """
        if self.fname not in self.versions:
            self.versions[self.fname] = 1
        name = "%" + "%d" % (self.versions[self.fname])
        self.versions[self.fname] += 1
        return name

    def new_text(self, typename: str) -> str:
        """
        Create a new literal constant on global section (text).
        """
        name = "@." + typename + "." + "%d" % (self.versions["_glob_"])
        self.versions["_glob_"] += 1
        return name

    def new_for(self) -> str:
        """
        Create a new temporary label to a for loop
        """
        if "_for_" not in self.versions:
            self.versions["_for_"] = 1
        name = self.versions["_for_"]
        self.versions["_for_"] += 1
        return name

    def new_while(self) -> str:
        """
        Create a new temporary label to a while loop
        """
        if "_while_" not in self.versions:
            self.versions["_while_"] = 1
        name = self.versions["_while_"]
        self.versions["_while_"] += 1
        return name

    def new_assert(self) -> str:
        """
        Create a new temporary label to a assers statment
        """
        if "_assert_" not in self.versions:
            self.versions["_assert_"] = 1
        name = self.versions["_assert_"]
        self.versions["_assert_"] += 1
        return name

    def new_if(self) -> str:
        """
        Create a new temporary label to a assers statment
        """
        if "_if_" not in self.versions:
            self.versions["_if_"] = 1
        name = self.versions["_if_"]
        self.versions["_if_"] += 1
        return name

    def is_global(self, name):
        """
        Checks if a variable is declared in a global context
        """
        res = False
        label = ""

        if name in self.symtab.data[0]:
            for global_name in self.text:
                if name == global_name[1].split(".")[1].split("_")[1]:
                    res = True
                    label = global_name[1]
                    break
        return (res, label)

        
    # You must implement visit_Nodename methods for all of the other
    # AST nodes.  In your code, you will need to make instructions
    # and append them to the current block code list.
    #
    # A few sample methods follow. Do not hesitate to complete or change
    # them if needed.

    def visit_Constant(self, node: Node):
        # if node.type.name == "string":
        if node.type == "string":
            _target = self.new_text("str")
            inst = ("global_string", _target, node.value)
            self.text.append(inst)
        else:
            # Create a new temporary variable name
            _target = self.new_temp()
            # Make the SSA opcode and append to list of generated instructions
            if node.type == 'int':
                node.value = int(node.value)
            inst = ("literal_" + node.type, node.value, _target)
            self.current_block.append(inst)
        # Save the name of the temporary variable where the value was placed
        node.gen_location = _target

        node.uc_type = self.typemap[node.type]

    def visit_BinaryOp(self, node: BinaryOp):
        def get_type(type):
            if not isinstance(type, ArrayType):
                return type
            return get_type(type.type)
        
        binary_ops = {
            "+": "add",
            "-": "sub",
            "*": "mul",
            "/": "div",
            "%": "mod",
            "<": "lt",
            "<=": "le",
            ">=": "ge",
            ">": "gt",
            "==": "eq",
            "!=": "ne",
            "&&": "and",
            "||": "or",
            "!": "not"
        }

        # Visit the left and right expressions
        self.visit(node.lvalue)
        self.visit(node.rvalue)

        # TODO:
        # - Load the location containing the left expression
        # - Load the location containing the right expression

        # Make a new temporary for storing the result
        target = self.new_temp()

        # Create the opcode and append to list
        # print(node.lvalue.name)
        # print(self.symtab.data)

        op_name = node.lvalue
        while hasattr(op_name, 'name'):
            op_name = op_name.name

        op_type = get_type(self.symtab.lookup(op_name)) if (hasattr(node.lvalue, 'name')) else get_type(node.lvalue.uc_type)
        
        opcode = binary_ops[node.op] + "_"
        if node.op in ["&&", "||", "!", "=="]:
            opcode += "bool"
        elif isinstance(op_type, FuncType):
            opcode += op_type.type.typename
        else:
            opcode += op_type.typename
        inst = (opcode, node.lvalue.gen_location, node.rvalue.gen_location, target)
        self.current_block.append(inst)

        # Store location of the result on the node
        node.gen_location = target
        node.uc_type = op_type

    def visit_Print(self, node: Node):
        # Visit the expression
        if node.expr is not None:
            self.visit(node.expr)
        else:
            inst = ("print_void", )
            self.current_block.append(inst)
            return

        # TODO: Load the location containing the expression
        # Create the opcode and append to list
        if (isinstance(node.expr, ExprList)):
            for _expr in node.expr.exprs:
                self.visit(_expr)
                inst = ("print_" + _expr.uc_type.typename, _expr.gen_location)
                self.current_block.append(inst)
        else:
            inst = ("print_" + node.expr.uc_type.typename, node.expr.gen_location)
            self.current_block.append(inst)

        # TODO: Handle the cases when node.expr is None or ExprList

    def visit_VarDecl(self, node: Node):
        def get_size(init):
            sizes = [len(init)]

            if isinstance(init[0], InitList):
                sizes += get_size(init[0].exprs)
            
            return sizes

        def get_constant_size(decl):
            sizes = [decl.dim.value]

            if isinstance(decl.type, ArrayDecl):
                sizes += get_constant_size(decl.type)
            
            return sizes
        
        # Allocate on stack memory
        # _varname = "%" + node.declname.name
        _varname = node.declname.gen_location
        
        # print(node)
        if isinstance(node.decl.type, ArrayDecl):
            _init = node.decl.init
            if isinstance(_init, InitList):
                _sizes = "".join(map(lambda x: f"_{x}", get_size(_init.exprs)))
            elif isinstance(_init, Constant) and _init.type == "string":
                _sizes = f"_{len(_init.value)}"
            else:
                _sizes = "".join(map(lambda x: f"_{x}", get_constant_size(node.decl.type)))
                # _sizes = f"_{node.decl.type.dim.value}"

            inst = ("alloc_" + node.type.name + _sizes, _varname)
        else:    
            inst = ("alloc_" + node.type.name, _varname)
        self.current_block.append(inst)

        # Store optional init val
        _init = node.decl.init
        
        if isinstance(_init, InitList):
            node.decl.init.name = node.declname

        if _init is not None:
            self.visit(_init)
            if isinstance(_init, InitList):
                _sizes = "".join(map(lambda x: f"_{x}", get_size(_init.exprs)))
                inst = (
                    "store_" + node.type.name + _sizes,
                    _init.gen_location,
                    node.declname.gen_location,
                )
            elif isinstance(_init, Constant) and _init.type == "string":
                inst = (
                    "store_" + node.type.name + "_%d" % len(_init.value),
                    _init.gen_location,
                    node.declname.gen_location,
                )
            else:
                inst = (
                    "store_" + node.type.name,
                    _init.gen_location,
                    node.declname.gen_location,
                )
            self.current_block.append(inst)

    def visit_Program(self, node: Node):
        # Visit all of the global declarations
        self.symtab.new_context()
        for _decl in node.gdecls:
            self.visit(_decl)
        # At the end of codegen, first init the self.code with
        # the list of global instructions allocated in self.text
        self.code = self.text.copy()
        # Also, copy the global instructions into the Program node
        node.text = self.text.copy()
        # After, visit all the function definitions and emit the
        # code stored inside basic blocks.
        for _decl in node.gdecls:
            if isinstance(_decl, FuncDef):
                # _decl.cfg contains the Control Flow Graph for the function
                # cfg points to start basic block
                bb = EmitBlocks()
                bb.visit(_decl.cfg)
                for _code in bb.code:
                    self.code.append(_code)

        if self.viewcfg:  # evaluate to True if -cfg flag is present in command line
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name)
                    dot.view(_decl.cfg)  # _decl.cfg contains the CFG for the function

    # TODO: Complete.
    def visit_FuncDef(self, node: FuncDef):
        # Initialize the necessary blocks to construct the CFG of the function.
        # Visit the function declaration. Visit all the declarations within the function.
        # After allocating all declarations, visit the arguments initialization.
        # Visit the body of the function to generate its code.
        # Finally, setup the return block correctly and generate the return statement (even for void function).

        self.symtab.new_context()

        node.cfg = BasicBlock(node.decl.name.name)
        self.exit_block = BasicBlock("exit")
        self.exit_locat = self.new_temp()

        self.current_block = node.cfg

        self.visit(node.type)
        self.visit(node.decl)

        func_type = self.symtab.lookup("func-temp")
        self.symtab.add(node.decl.name.name, func_type)
        
        self.visit(node.body)
        
        self.symtab.top_context().data.pop("ret-temp")
        self.symtab.pop_context()

        # Adds function to global context
        self.symtab.add(node.decl.name.name, func_type)

        self.current_block.next_block = self.exit_block
        self.exit_block.predecessors.append(self.current_block)
        self.current_block = self.exit_block
        self.current_block.append(('exit:', ))

        if func_type.type.typename == "void":
            self.current_block.append(('return_void', ))
        else:
            self.current_block.append(('return_' + func_type.type.typename, self.exit_locat))

    def visit_ParamList(self, node: ParamList):
        # Just visit all arguments.
        
        for _param in node.params:
            self.visit(_param)

    def visit_GlobalDecl(self, node: GlobalDecl):
        # Visit each global declaration that are not function declarations. 
        # Indeed, it is usually simpler to visit the function declaration when visiting
        # the definition of the function to generate all code at once.

        for _decl in node.decls:
            if isinstance(_decl.type, FuncDecl):
                self.symtab.add(_decl.name.name, FuncType(_decl.type.type.uc_type, None))
                continue
            
            if isinstance(_decl.type, VarDecl):
                typename = _decl.type.uc_type.typename
                _target = self.new_text("const_" + _decl.name.name)
                inst = ("global_" + typename, _target, int(_decl.init.value))
                self.text.append(inst)
                self.symtab.add(_decl.name.name, _decl.type.uc_type)
            
            if isinstance(_decl.type, ArrayDecl):
                if isinstance(_decl.init, InitList):
                    _decl.init.name = _decl.name
                self.visit(_decl.init)
                self.symtab.add(_decl.name.name, _decl.type.uc_type)


    def visit_Decl(self, node: Decl):
        # Visit the type of the node (i.e., VarDecl, FuncDecl, etc.).
        node.type.declname = node.name
        node.type.decl = node

        node.name.prev = 'decl'
        self.visit(node.name)
        
        self.visit(node.type)
        if isinstance(node.type, VarDecl):
            v = self.symtab.top_context().lookup(node.name.name)
            if v is None:
                self.symtab.add(node.name.name, node.type.uc_type)
        
        if isinstance(node.type, ArrayDecl):
            self.symtab.add(node.name.name, node.type.uc_type)

    def visit_ArrayDecl(self, node: ArrayDecl):
        # Visit the node type.
        node.type.declname = node.declname
        node.type.decl = node.decl

        self.visit(node.type)

    def visit_FuncDecl(self, node: FuncDecl):
        # Generate the function definition (including function name, return type and arguments types).
        # This is also a good time to generate the entry point for function, allocate a temporary for
        # the return statement (if not a void function), and visit the arguments.
        
        node.type.declname = node.declname
        node.type.decl = node.type

        args = []
        for _args in node.params.params if node.params is not None else []:
            args.append((_args.uc_type.typename, self.new_temp()))

        self.current_block.append(('define_' + node.type.uc_type.typename, '@' + node.declname.name, args))
        self.current_block.append(('entry:', ))

        if node.type.uc_type.typename != "void":
            self.current_block.append(('alloc_' + node.type.uc_type.typename, self.exit_locat))

        # Sets Functions params
        func_type = FuncType(node.type.uc_type, None)
        if node.params is not None:
            self.visit(node.params)
            func_type.parameters = node.params.uc_type
        else:
            func_type.parameters = []
        
        for idx, _args in enumerate(node.params.params if node.params is not None else []):
            self.current_block.append(
                ('store_' + _args.uc_type.typename, args[idx][1], _args.name.gen_location)
            )

        # Adds function do symtab as stub because its name its not know here
        self.symtab.add("func-temp", func_type)
        node.uc_type = func_type

        
        
    def visit_DeclList(self, node: DeclList):
        # Visit all of the declarations that appear inside for statement.

        for _decl in node.decls:
            self.visit(_decl)

    def visit_Type(self, node: Type):
        # Do nothing: just pass.
        pass

    def visit_If(self, node: If):
        # First, generate the evaluation of the condition (visit it).
        # Create the required blocks and the branch for the condition.
        # Move to the first block and generate the statement related to
        # the then, create the branch to exit. In case, there is an else block,
        # generate it in a similar way.

        if_id = self.new_if()

        cond = ConditionBlock(f"if.{if_id}")
        iftrue = BasicBlock(f'if.then.{if_id}')
        iffalse = BasicBlock(f'if.else.{if_id}')
        end = BasicBlock(f'if.end.{if_id}')

        self.current_block.next_block = cond
        cond.predecessors.append(self.current_block)
        self.current_block = cond
        cond.taken = iftrue
        cond.fall_through = iffalse
        iftrue.predecessors.append(cond)
        iffalse.predecessors.append(cond)
        cond.next_block = iftrue

        # cond
        # TODO: create cond inst
        self.visit(node.cond)
        self.current_block.append(
            ('cbranch', "%" + "%d" % (self.versions[self.fname] - 1), f'%if.then.{if_id}', f'%if.else.{if_id}')
        )

        # iftrue
        self.current_block = iftrue
        iftrue.append((f'if.then.{if_id}:', ))
        self.visit(node.iftrue)
        self.current_block.next_block = iffalse
        end.predecessors.append(self.current_block)
        self.current_block.append(('jump', f'%if.end.{if_id}'))

        # iffalse
        self.current_block = iffalse
        iffalse.append((f'if.else.{if_id}:', ))
        if node.iffalse is not None:
            self.visit(node.iffalse)
        end.predecessors.append(self.current_block)
        self.current_block.append(('jump', f'%if.end.{if_id}'))

        self.current_block.next_block = end
        self.current_block = end
        self.current_block.append((f'if.end.{if_id}:', ))


    
    def visit_For(self, node: For):
        # First, generate the initialization of the For and creates all
        # the blocks required. Then, generate the jump to the condition block
        # and generate the condition and the correct conditional branch.
        # Generate the body of the For followed by the jump to the increment block.
        # Generate the increment and the correct jump.

        self.symtab.new_context()
        self.visit(node.init)
        for_id = self.new_for()
        self.current_block.append(('jump', f'%for.cond.{for_id}'))
        
        tmp = self.current_block
        

        cond = ConditionBlock(f'for.cond.{for_id}')
        body = BasicBlock(f'for.body.{for_id}')
        inc = BasicBlock(f'for.inc.{for_id}')
        end = BasicBlock(f'for.end.{for_id}')
        self.curr_loop.append(end)

        cond.predecessors.append(self.current_block)
        self.current_block.next_block = cond
        self.current_block = cond
        self.current_block.append((f'for.cond.{for_id}:', ))
        self.visit(node.cond)
        self.current_block.append(
            ('cbranch', "%" + "%d" % (self.versions[self.fname] - 1), f'%for.body.{for_id}', f'%for.end.{for_id}')
        )

        body.predecessors.append(self.current_block)
        cond.fall_through = body
        cond.next_block = body
        self.current_block = body
        self.current_block.append((f'for.body.{for_id}:', ))
        self.symtab.add("curr-loop", node)
        self.current_block = body
        self.visit(node.body)
        self.current_block.append(('jump', f'%for.inc.{for_id}'))

        cond.predecessors.append(inc)
        inc.predecessors.append(self.current_block)
        self.current_block.next_block = inc
        self.current_block = inc
        self.current_block.append((f'for.inc.{for_id}:', ))
        self.visit(node.next)
        self.current_block.append(('jump', f'%for.cond.{for_id}'))

        cond.taken = end
        end.predecessors.append(cond)
        inc.next_block = end
        self.current_block = end
        self.current_block.append((f'for.end.{for_id}:', ))

        self.curr_loop.pop()
        self.symtab.pop_context()

    def visit_While(self, node: While):
        # The generation of While is similar to For except that
        # it does not require the part related to initialization and increment.

        self.symtab.new_context()

        tmp = self.current_block
        while_id = self.new_while()

        cond = ConditionBlock(f'while.cond.{while_id}')
        body = BasicBlock(f'while.body.{while_id}')
        end = BasicBlock(f'while.end.{while_id}')
        self.curr_loop.append(end)

        cond.predecessors.append(self.current_block)
        self.current_block.append(('jump', f'%while.cond.{while_id}', ))
        self.current_block.next_block = cond
        self.current_block = cond
        self.current_block.append((f'while.cond.{while_id}:', ))
        self.visit(node.cond)
        self.current_block.append(
            ('cbranch', "%" + "%d" % (self.versions[self.fname] - 1), f'%while.body.{while_id}', f'%while.end.{while_id}')
        )

        body.predecessors.append(cond)
        cond.predecessors.append(body)
        cond.fall_through = body
        cond.next_block = body
        self.current_block = body
        self.current_block.append((f'while.body.{while_id}:', ))
        self.symtab.add("curr-loop", node)
        self.visit(node.body)
        self.current_block.append(('jump', f'%while.cond.{while_id}'))
        
        cond.taken = end
        end.predecessors.append(cond)
        body.next_block = end
        self.current_block = end
        self.current_block.append((f'while.end.{while_id}:', ))

        self.curr_loop.pop()
        self.symtab.pop_context()

    def visit_Compound(self, node: Compound):
        # Visit the list of block items (declarations or statements).

        self.symtab.new_context()

        for _block in node.staments:
            self.visit(_block)

        ret_type = self.symtab.lookup("ret-temp")
        self.symtab.pop_context()

        self.symtab.add("ret-temp", ret_type if ret_type is not None else self.typemap["void"])

    def visit_Assignment(self, node: Assignment):
        # First, visit right side and load the value according to its type.
        # Then, visit the left side and generate the code according to the assignment operator
        # and the type of the expression (ID or ArrayRef).

        if (isinstance(node.lvalue, ArrayRef)):
            node.lvalue.assignment = True

        self.visit(node.lvalue)
        self.visit(node.rvalue)
        
        if (isinstance(node.lvalue, ID)):
            self.current_block.append(('store_' + node.lvalue.uc_type.typename, node.rvalue.gen_location, node.lvalue.gen_location))
            res, loc = self.is_global(node.lvalue.name)
            if (res):
                self.current_block.append(('store_' + node.lvalue.uc_type.typename, node.lvalue.gen_location, loc))
        elif (isinstance(node.lvalue, ArrayRef)):
            self.current_block.append(('store_' + node.lvalue.uc_type.typename + "_*", node.rvalue.gen_location, node.lvalue.gen_location))
            # res, loc = self.is_global(node.lvalue.name.name)
            # print(res, loc, node.lvalue.name.name)
            # if (res):
            #     self.current_block.append(('elem_' + node.lvalue.uc_type.typename))
            #     self.current_block.append(('store_' + node.lvalue.uc_type.typename + "_*", node.lvalue.gen_location, loc))
        else:
            self.current_block.append(('store_' + node.lvalue.uc_type.typename, "%" + "%d" % (self.versions[self.fname] - 1), node.lvalue.gen_location))

    def visit_Break(self, node: Break):
        # Generate a jump instruction to the current exit label.
        
        # FIXME: Keep current exit label
        self.current_block.append(
            ('jump', "%" + self.curr_loop[-1].label)
        )

    def visit_FuncCall(self, node: FuncCall):
        # Start by generating the code for the arguments:
        # for each one of them, visit the expression
        # and generate a param_type instruction with its value.
        # Then, allocate a temporary for the return value
        # and generate the code to call the function.

        arg_list = node.args.exprs if isinstance(node.args, ExprList) else [node.args]

        for _arg in arg_list:
            self.visit(_arg)
            name = self.new_temp()
            self.current_block.append(
                ('load_' + _arg.uc_type.typename, _arg.gen_location, name)
            )
            self.current_block.append(
                ('param_' + _arg.uc_type.typename, name)
            )
        
        func_type = self.symtab.lookup(node.name.name)
        out = self.new_temp()
        self.current_block.append(
            ('call_' + func_type.type.typename, '@' + node.name.name, out)
        )

        node.gen_location = out
        


    def visit_Assert(self, node: Assert):
        # The assert is a conditional statement which generate code quite similar to the If Block.
        # If the expression is false, the program should issue an error message (assertfail)
        # and terminate. If the expression is true, the program proceeds to the next sentence.

        # Visit the assert condition. Create the blocks for the condition
        # and adust their predecessors. Generate the branch instruction
        # and adjust the blocks to jump according to the condition.
        # Generate the code for unsuccessful assert, generate the print instruction
        # and the jump instruction to the return block, and successful assert.

        self.visit(node.expr)

        assert_id = self.new_assert()

        blk = ConditionBlock(f"assert.{assert_id}")
        blk_true = BasicBlock(f"assert.true.{assert_id}")
        blk_false = BasicBlock(f"assert.false.{assert_id}")

        # Links blocks
        self.current_block.next_block = blk
        blk.predecessors.append(self.current_block)

        blk_true.predecessors.append(blk)
        blk_false.predecessors.append(blk)
        self.current_block = blk

        blk.fall_through = blk_false
        blk.taken = blk_true

        blk_false.next_block = blk_true
        blk.next_block = blk_false

        self.current_block.append(
            ('cbranch', "%" + "%d" % (self.versions[self.fname] - 1), f'%assert.true.{assert_id}', f'%assert.false.{assert_id}')
        )

        name = self.new_text("str")
        self.text.append(('global_type', name, 'assertion_fail on ' + str(node.expr.coord).strip("@").strip()))

        self.current_block = blk_false
        self.exit_block.predecessors.append(blk_false)
        self.current_block.append((f'assert.false.{assert_id}:', ))
        self.current_block.append(('print_string', name))
        self.current_block.append(('jump', "%exit"))

        self.current_block = blk_true
        self.current_block.append((f'assert.true.{assert_id}:', ))
        # FIX-ME: jump %exit in not in the right place
        # self.current_block.append(('jump', "%exit"))
        
        # after = BasicBlock("")
        # blk.taken.next_block = after
        # after.predecessors.append(blk.taken)

        # self.current_block = blk_true

    def visit_Read(self, node: Read):
        # For each name, you need to visit it,
        # load it if necessary and generate a read instruction for each element.
        pass

    def visit_Return(self, node: Return):
        # If there is an expression, you need to visit it,
        # load it if necessary and store its value to the return location.
        # Then generate a jump to the return block if needed.
        # Do not forget to update the predecessor of the return block.

        # self.current_block.append(('exit:', ))

        if node.expr is not None:
            self.visit(node.expr)
            self.current_block.append(('store_' + node.expr.uc_type.typename, node.expr.gen_location, self.exit_locat))
        self.current_block.append(('jump', '%exit'))
            # self.current_block.append(('return_int', "%" + "%d" % (self.versions[self.fname] - 1)))
        # else:
            # self.current_block.append(('return', ))



    def visit_ID(self, node: ID):
        # Get the name of the temporary (or register) where the value of
        # the variable is stored. This temporary (gen_location,
        # in the sample code) was stored next to the variable's
        # declaration during its allocation. For this, you can 
        # consult the symbol table or use the bind attribute 
        # that's link the identifier with its declaration
        # (usually made during semantic analysis).

        # FIXME: new_temp should add label instead of %n
        # FIXME: Scope issues - Might have duplicate <var>.x
        def get_type(type):
            if not isinstance(type, ArrayType):
                return type
            return get_type(type.type)

        def get_size(type):
            sizes = [type.size]

            if isinstance(type.type, ArrayType):
                sizes += [*get_size(type.type)]
            
            return sizes
        
        node.scope = 0 if not hasattr(node, 'prev') else 1
        for tb in self.symtab.data:
            if node.name in tb.keys():
                node.scope += 1
        _type = self.symtab.lookup(node.name)
        node.uc_type = get_type(_type)
        node.gen_location = f"%{node.name}.{node.scope}"


        if (isinstance(self.symtab.lookup(node.name), FuncType)):
            return
        
        # print(self.symtab.data)
        _typename = ""
        if isinstance(_type, ArrayType):
            _sizes = map(lambda x: f"_{x}", get_size(_type))
            _typename += "".join(_sizes)

        if (node.name in self.symtab.data[0]):
            loc = None
            for name in self.text:
                if node.name == name[1].split(".")[1].split("_")[1]:
                    loc = name[1]
                    break
            self.current_block.append(
                ('alloc_' + node.uc_type.typename + _typename, node.gen_location)
            )
            self.current_block.append(
                ('store_' + node.uc_type.typename + _typename, loc, node.gen_location)
            )

    def visit_UnaryOp(self, node: UnaryOp):
        # The generation of unary operations are similar to binary operations
        # except that they have only a single expression.
        unary_ops = {
            "+": "add",
            "-": "sub",
            "!": "not"
        }

        lvalue = self.new_temp()
        if node.op != "!":
            self.current_block.append(('literal_' + node.uc_type.typename, 0, lvalue))
        self.visit(node.expr)

        # Make a new temporary for storing the result
        target = self.new_temp()
        op_name = node.expr
        while hasattr(op_name, 'name'):
            op_name = op_name.name

        op_type = self.symtab.lookup(op_name) if (hasattr(node.expr, 'name')) else node.expr.uc_type

        opcode = unary_ops[node.op] + "_"
        if node.op == "!":
            opcode += "bool"
        elif isinstance(op_type, FuncType):
            opcode += op_type.type.typename
        else:
            opcode += op_type.typename
        
        if ("not_" in opcode):
            inst = (opcode, node.expr.gen_location, target)
        else:
            inst = (opcode, lvalue, node.expr.gen_location, target)

        self.current_block.append(inst)

        # Store location of the result on the node
        node.gen_location = target
        node.uc_type = op_type

    def visit_ExprList(self, node: ExprList):
        # Do nothing, just pass:
        # the Expression List must be treated in the scope that uses it.
        pass

    def visit_ArrayRef(self, node: ArrayRef):
        # Start by visiting the subscript.
        # Load the values of the index in a new temporary.
        # If the array has multiple dimensions:
        # you need to generate arithmetic instructions to compute
        # the index of the element in the array.
        def get_name(ref):
            if isinstance(ref, ID):
                return ref.name
            return get_name(ref.name)
    
        def get_typename(type):
            if not isinstance(type, ArrayType):
                return type
            return get_typename(type.type)
        
        if not isinstance(node.name, ArrayRef) and hasattr(node, "nested"):
            self.visit(node.subscript)
            self.visit(node.name)

            _type = self.symtab.lookup(get_name(node.name))
            _typename = get_typename(_type)

            _literal = self.new_temp()
            # FIXME: _type.type.size only works for matrices
            self.current_block.append((
                'literal_int', _type.type.size, _literal
            ))

            _mul = self.new_temp()
            self.current_block.append((
                'mul_int', _literal, node.subscript.gen_location, _mul
            ))

            node.gen_location = _mul
            node.uc_type = _typename

            return

        if isinstance(node.name, ArrayRef):
            node.name.nested = True
            self.visit(node.subscript)
            self.visit(node.name)

            _addr = self.new_temp()
            self.current_block.append((
                'add_int', node.subscript.gen_location, node.name.gen_location, _addr
            ))

            _name = node.name
            while not isinstance(_name, ID):
                _name = _name.name
            self.visit(_name)

            _type = self.symtab.lookup(get_name(node.name))
            _typename = get_typename(_type)

            _target = self.new_temp()
            self.current_block.append(
                ('elem_' + _typename.typename,
                _name.gen_location,
                _addr,
                _target)
            )

            if not hasattr(node, "assignment"):
                _load = self.new_temp()
                self.current_block.append(
                    ('load_' + _typename.typename + "_*", _target, _load)
                )

                node.gen_location = _load
                node.uc_type = _typename
            else:
                node.gen_location = _target
                node.uc_type = _typename

            return

        if not isinstance(node.name, ArrayRef):
            self.visit(node.subscript)
            self.visit(node.name)

            _type = self.symtab.lookup(get_name(node.name))
            _typename = get_typename(_type)

            res, loc = self.is_global(node.name.name)
            if (res):
                gen_loc = loc
            else:
                gen_loc = node.name.gen_location

            _target = self.new_temp()
            self.current_block.append(
                ('elem_' + _typename.typename,
                gen_loc,
                node.subscript.gen_location,
                _target)
            )

            if not hasattr(node, "assignment"):
                _load = self.new_temp()
                self.current_block.append(
                    ('load_' + _typename.typename + "_*", _target, _load)
                )
                # FIXME: Compute idx if there are multiple dimensions

                node.gen_location = _load
                node.uc_type = _typename
            else:
                node.gen_location = _target
                node.uc_type = _typename

            return
        

    def visit_InitList(self, node: InitList):
        # Evaluate each element of the list and add its value
        # to the node value (which is a list).
        def get_elements(init):
            elements = []
            
            for _element in init:
                if isinstance(_element, Constant) and _element.type == "int":
                    elements.append(int(_element.value))
                if isinstance(_element, InitList):
                    elements.append(get_elements(_element.exprs))
            
            return elements

        def get_type(init):
            for _element in init:
                if isinstance(_element, Constant):
                    return _element.uc_type
                if isinstance(_element, InitList):
                    return get_type(_element.exprs)
            return None

        def get_size(init):
            sizes = [len(init)]

            if isinstance(init[0], InitList):
                sizes += get_size(init[0].exprs)
            
            return sizes
        
        elements = get_elements(node.exprs)
        _target = self.new_text("const_" + node.name.name)
        _type = get_type(node.exprs)
        _sizes = "".join(map(lambda x: f"_{x}", get_size(node.exprs)))
        inst = (f"global_{_type.typename}{_sizes}", _target, elements)
        self.text.append(inst)

        node.gen_location = _target




if __name__ == "__main__":

    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script only runs the interpreter on the uCIR. \
              Use the other options for printing the uCIR, generating the CFG or for the debug mode.",
        type=str,
    )
    parser.add_argument(
        "--ir",
        help="Print uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--cfg", help="Show the cfg of the input_file.", action="store_true"
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    args = parser.parse_args()

    print_ir = args.ir
    create_cfg = args.cfg
    interpreter_debug = args.debug

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

    gen = CodeGenerator(create_cfg)
    gen.visit(ast)
    gencode = gen.code

    if print_ir:
        print("Generated uCIR: --------")
        gen.show()
        print("------------------------\n")

    vm = Interpreter(interpreter_debug)
    vm.run(gencode)
