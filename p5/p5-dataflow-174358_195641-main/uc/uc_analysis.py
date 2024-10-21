import argparse
import pathlib
import sys
from typing import List, Dict, Tuple
from uc.uc_ast import FuncDef, Node
from uc.uc_block import CFG, EmitBlocks, format_instruction
from uc.uc_code import BasicBlock, ConditionBlock, CodeGenerator
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor

def block_iter(block):
    while block:
        yield block.label, block.instructions.copy()
        block = block.next_block

class DataFlow(NodeVisitor):
    def __init__(self, viewcfg: bool):
        # flag to show the optimized control flow graph
        self.viewcfg: bool = viewcfg
        # list of code instructions after optimizations
        self.code: List[Tuple[str]] = []
        self.text: List[Tuple[str]] = []
        # TODO

        self.opcode_gen = {
            "alloc": 1,
            "load": 2,
            "store": 2,
            "literal": 2,
            "elem": 3,
            "add": 3,
            "sub": 3,
            "mul": 3,
            "div": 3,
            "mod": 3,
            "not": 2,
            "lt": 3,
            "le": 3,
            "ge": 3,
            "gt": 3,
            "eq": 3,
            "ne": 3,
            "and": 3,
            "or": 3
        }

        # self.bool_to_num = lambda x: '1' if x else '0'

        self.fold = {
            "add": lambda a, b: a + b,
            "sub": lambda a, b: a - b,
            "mul": lambda a, b: a * b,
            "div": lambda a, b: a / b,
            "mod": lambda a, b: a % b,
            # "lt":  lambda a, b: self.bool_to_num(a < b),
            # "le":  lambda a, b: self.bool_to_num(a <= b),
            # "ge":  lambda a, b: self.bool_to_num(a > b),
            # "gt":  lambda a, b: self.bool_to_num(a >= b),
            # "eq":  lambda a, b: self.bool_to_num(a == b),
            # "ne":  lambda a, b: self.bool_to_num(a != b),
            # "and": lambda a, b: self.bool_to_num(a and b),
            # "or":  lambda a, b: self.bool_to_num(a or b)
        }

        self.binary_ops = {
            "add",
            "sub",
            "mul",
            "div",
            "mod",
            "lt",
            "le",
            "ge",
            "gt",
            "eq",
            "ne",
            "and",
            "or", 
            "not",
            }
        self.single_use_ops = {
            "store",
            "load",
            "not",
            "cbranch",
            "return",
            "print",
            "print",
            "param"
        }
        self.assign_ops = {
            "add",
            "and",
            "call",
            "div",
            "elem",
            "eq",
            "ge",
            "get",
            "gt",
            "le",
            "literal",
            "load",
            "store",
            "lt",
            "mod",
            "mul",
            "ne",
            "not",
            "or",
            "sub",
        }

        self.mem_ops = {"load", "store"}
        self.vector_ops = {"elem"}
        self.relational_ops = {"lt", "le", "ge", "gt", "eq", "ne", "and", "or", "not"}
        self.unary_ops = {"not"}
        self.branch_ops = {"cbranch"}
        self.func_builtin_ops = {"return", "print", "param"}

        self.defs: Dict[str, set] = {}
        self.rd_gens = {}
        self.rd_kill = {}
        self.rd_in = {}
        self.rd_out = {}

        self.lv_use = {}
        self.lv_def = {}
        self.lv_in = {}
        self.lv_out = {}


    def show(self, buf=sys.stdout):
        _str = ""
        for _code in self.code:
            _str += format_instruction(_code) + "\n"
        buf.write(_str)

    # TODO: add analyses

    def clear_rd(self):
        self.defs = {}
        self.rd_gens = {}
        self.rd_kill = {}
        self.rd_in = {}
        self.rd_out = {}
    
    def clear_lv(self):
        self.lv_use = {}
        self.lv_def = {}
        self.lv_in = {}
        self.lv_out = {}

    def get_target(self, inst):
        return inst[-1]
    
    def get_opcode(self, inst):
        return inst[0].split("_")[0]

    def get_optype(self, inst):
        return inst[0].split("_")[1]
    
    def blocks(self, block):
        while block:
            yield block
            block = block.next_block

    def get_block(self, cfg, label):

        for b in self.blocks(cfg):
            if b.label == label:
                return b
        
        return None
    
    def fix_cfg(self, cfg):
        for b in self.blocks(cfg):
            opcode = self.get_opcode(b.instructions[-1])
            target = self.get_target(b.instructions[-1])

            if opcode == "jump" and isinstance(b, BasicBlock):
                target_block = self.get_block(cfg, target.strip("%"))
                b.branch = target_block

                assert b in target_block.predecessors
            elif isinstance(b, BasicBlock):
                b.branch = b.next_block
            
            # comment out to handle recursion
            # for inst in b.instructions:
            #     opcode = self.get_opcode(inst)
            #     if opcode == "call" and inst[1].strip("@") == cfg.label:
            #         cfg.predecessors.append(b)
        
        # for b in self.blocks(cfg):
        #     print(b.label)
        #     for p in b.predecessors:
        #         print("\t" + p.label)

    def iter_cfg(self, cfg):
        q = [cfg]
        out, visited = [], []

        while len(q):
            b = q.pop(0)

            if b is None or b in visited:
                continue
            
            visited.append(b)

            if isinstance(b, ConditionBlock):
                q.append(b.taken)
                q.append(b.fall_through)
            elif isinstance(b, BasicBlock):
                q.append(b.branch)
            
            out.append(b)
        
        # TODO: Remove assert used for debug
        assert len(out) == len([b for b in self.blocks(cfg)])

        return out

    def iter_block(self, block):
        for b in self.iter_cfg(block):
            yield b.label, b.instructions

    def filter_assign_instructions(self, instructions):
        for idx, inst in enumerate(instructions):
            if self.get_opcode(inst) in self.opcode_gen:
                yield idx, inst

        # filtered = filter(
        #     lambda x: self.get_opcode(x) in self.opcode_gen,
        #     insts
        # )


        # return list(filtered)
    
    def buildRD_blocks(self, cfg):
        for label, instructions in self.iter_block(cfg):

            for idx, inst in self.filter_assign_instructions(instructions):
                target = self.get_target(inst)
                definition = (label, idx)
                
                if target not in self.defs:
                    self.defs[target] = set()
                self.defs[target].add(definition)
                # self.defs[target].add(target)

        # print("DEFS:")
        # for key, value in self.defs.items():
        #     print(key)
        #     for e in value:
        #         print(f"\t{e}")
        #     print()


    def computeRD_gen_kill(self, cfg):
        for label, instructions in self.iter_block(cfg):
            self.rd_gens[label] = set()
            self.rd_kill[label] = set()

            for idx, inst in self.filter_assign_instructions(instructions):
                target = self.get_target(inst)
                definition = (label, idx)

                self.rd_gens[label].add(definition)
                # self.rd_gens[label].add(target)
                # ???
                self.rd_kill[label] = self.rd_kill[label].union(self.defs[target] - self.rd_gens[label])

        # print("GENS:")
        # for key, value in self.rd_gens.items():
        #     print(key)
        #     for e in value:
        #         print(f"\t{e}")
        #     print()
        
        # print("KILLS:")
        # for key, value in self.rd_kill.items():
        #     print(key)
        #     for e in value:
        #         print(f"\t{e}")
        #     print()

    def computeRD_in_out(self, cfg):
        changed = set()
        
        # initialize
        for label, _ in self.iter_block(cfg):
            self.rd_out[label] = set()
            # self.rd_in[label] = set()

        # put all blocks into the changed set
        for b in self.blocks(cfg):
            changed.add(b)
        
        # iterates until fixed point
        while changed:
            # print(changed)
            # takes last item from set anr marks it
            # as empty (choice is arbitrary)
            b = changed.pop()

            if b.label not in self.rd_in:
                self.rd_in[b.label] = set()

            # calculates IN[b] from predecessors (OUT[p])
            for p in b.predecessors:
                self.rd_in[b.label] = self.rd_in[b.label].union(self.rd_out[p.label])
                
            
            oldout = self.rd_out[b.label]
            self.rd_out[b.label] = self.rd_gens[b.label].union(
                self.rd_in[b.label] - self.rd_kill[b.label]
            )

            # no need to recompute successors
            if (self.rd_out[b.label] == oldout):
                continue
            
            # adds successors that might have changed
            successors = []
            if isinstance(b, ConditionBlock):
                successors.append(b.taken)
                successors.append(b.fall_through)
            elif isinstance(b, BasicBlock):
                successors.append(b.branch)
            
            # # comment out to handle recursive calls
            # for inst in b.instructions:
            #     if self.get_opcode(inst) == "call":
            #         successors.append(self.get_block(cfg, inst[1].strip("@")))
            #         print(inst, self.get_block(cfg, inst[1].strip("@")))
            
            for s in successors:
                if s is None: continue
                changed.add(s)

        # for b in self.blocks(cfg):
        #     print(b.label)
        #     for p in b.predecessors:
        #         print(f"\t{p.label}")

        # # prints IN and OUT for debug
        # print("IN:")
        # for key, value in self.rd_in.items():
        #     print(key)
        #     for e in value:
        #         print(f"\t{e}")
        #     print()
        
        # print("\nOUT:")
        # for key, value in self.rd_out.items():
        #     print(key)
        #     for e in value:
        #         print(f"\t{e}")
        #     print()
    
    def get_constant_values(self, cfg, block, values):
        def get_constant(t):
            nonlocal values
            
            # comment out to consider global constants
            for _, name, value in self.text:
                if isinstance(value, list):
                    continue
                if isinstance(value, str):
                    continue

                if t == name:
                    values[t] = value
                    break

            return values.get(t)
        
        def set_constant(t, v):
            nonlocal values

            # gets actuall value if is not literal
            if isinstance(v, str): v = get_constant(v)
            
            if t not in values:
                values[t] = v
            else:
                values[t] = values[t] if v == values[t] else None


        # for label, idx in self.rd_in[block.label]:
        for label, idx in self.rd_out[block.label]:
            # print(block.label, label)
            b = self.get_block(cfg, label)
            inst = b.instructions[idx]

            opcode = self.get_opcode(inst)
            target = self.get_target(inst)

            if opcode == "literal" or opcode == "store":
                # if label == "for.cond.1":
                #     print(inst)
                set_constant(target, inst[1])
        
        # print(values)
        # print(block.label, values)
        # return values

    def constant_propagation(self, cfg):
        values = {}
        for b in self.blocks(cfg):
            self.get_constant_values(cfg, b, values)
            # print(values)
            # print(b.label, values)

            # propagates known constants and folds values
            for idx, inst in enumerate(b.instructions):
                opcode = self.get_opcode(inst)
                target = self.get_target(inst)

                if opcode == "store" and values.get(inst[1]) is not None:
                    optype = self.get_optype(inst)

                    b.instructions[idx] = (
                        "literal_" + optype,
                        values.get(inst[1]),
                        target
                    )
                    values[target] = values.get(inst[1])

                elif opcode in self.fold and values.get(inst[1]) and values.get(inst[2]):
                    optype = self.get_optype(inst)

                    res = self.fold[opcode](values.get(inst[1]), values.get(inst[2]))
                    # print("Folded ", inst[1], " + ", inst[2], " == ", res)
                    b.instructions[idx] = (
                        "literal_" + optype,
                        res,
                        target
                    )
                    values[target] = res
                
                # # ???
                # if opcode == "load" and values.get(inst[1]):
                #     optype = self.get_optype(inst)

                #     b.instructions[idx] = (
                #         "literal_" + optype,
                #         values.get(inst[1]),
                #         target
                #     )


    def buildLV_blocks(self, cfg):
        for b in self.blocks(cfg):
            self.lv_def[b.label] = set()
            self.lv_use[b.label] = set()
            self.lv_in[b.label] = set()
            self.lv_out[b.label] = set()

    def computeLV_use_def(self, cfg):
        for b in self.blocks(cfg):
            for idx, inst in enumerate(b.instructions):
                opcode = self.get_opcode(inst)

                # computes lv_use
                if opcode in self.binary_ops:
                    self.lv_use[b.label].add(inst[1]) # left
                    self.lv_use[b.label].add(inst[2]) # right
                elif opcode == "cbranch":
                    self.lv_use[b.label].add(inst[1])
                elif opcode in self.single_use_ops:
                    if self.get_optype(inst) != "void":
                        self.lv_use[b.label].add(inst[1])
                elif opcode == "elem":
                    self.lv_use[b.label].add(inst[1]) # src
                    self.lv_use[b.label].add(inst[2]) # idx
                
                # computes lv_def
                if opcode in self.assign_ops or opcode == "alloc":
                    self.lv_def[b.label].add(self.get_target(inst))
                elif opcode == "elem":
                    self.lv_def[b.label].add(self.get_target(inst))

                # edge case for store_int*
                if opcode == "store" and "*" in inst[0]:
                    self.lv_use[b.label].add(inst[2])
                

        # for b in self.blocks(cfg):
        #     print(b.label)
        #     print("\tV_USE:")
        #     print(f"\t\t{self.lv_use[b.label]}")
        #     print("\tLV_DEF:")
        #     print(f"\t\t{self.lv_def[b.label]}")

    def get_sucessors(self, block):
        sucessors = []
        if isinstance(block, ConditionBlock):
            sucessors.append(block.taken)
            sucessors.append(block.fall_through)
        elif isinstance(block, BasicBlock):
            sucessors.append(block.branch)
        
        return list(filter(lambda x: x is not None, sucessors))

    def computeLV_in_out(self, cfg):
        in_dict, out_dict = {}, {}
        old_in_dict, old_out_dict = {}, {}

        # initialize
        for label, _ in self.iter_block(cfg):
            self.lv_in[label] = set()
            self.lv_out[label] = set()

            in_dict[label] = self.lv_in[label]
            out_dict[label] = self.lv_out[label]

        # iterates until fixed point
        while in_dict != old_in_dict or out_dict != old_out_dict:
            # print("STEP:")
            for label, _ in self.iter_block(cfg):
                old_in_dict[label] = in_dict[label]
                old_out_dict[label] = out_dict[label]

                self.lv_in[label] = self.lv_use[label].union(
                    self.lv_out[label] - self.lv_def[label]
                )
                self.lv_out[label] = set()
                for succ in self.get_sucessors(self.get_block(cfg, label)):
                    self.lv_out[label] = self.lv_out[label].union(self.lv_in[succ.label])
                
                # print(f"\t{label}")
                # print(f"\t\t{self.lv_in[label]}")
                # print(f"\t\t{self.lv_out[label]}")
                # print()
                in_dict[label] = self.lv_in[label].copy()
                out_dict[label] = self.lv_out[label].copy()
        
        # print("LV_IN:")
        # for label, _ in self.iter_block(cfg):
        #     print(f"\t{label}")
        #     print(f"\t\t{self.lv_in[label]}")
        
        # print("LV_OUT:")
        # for label, _ in self.iter_block(cfg):
        #     print(f"\t{label}")
        #     print(f"\t\t{self.lv_out[label]}")


    def deadcode_elimination(self, cfg):
        # print("DEAD CODE:")
        for b in self.blocks(cfg):
            to_discard = []
            for idx, inst in enumerate(b.instructions):
                if len(inst) == 1: continue # ignores labels

                opcode = self.get_opcode(inst)
                target = self.get_target(inst)
                
                if opcode not in self.assign_ops:
                    continue


                if target not in self.lv_out[b.label] and target not in self.lv_use[b.label]:
                    # print(opcode, target)
                    # print(self.lv_out[b.label])
                    # print(self.lv_use[b.label])
                    # print()
                    to_discard.append(idx)
        
            
            for idx in reversed(to_discard):
                b.instructions.pop(idx)

            # print()
            # print(b.label)
            # for i in to_discard:
            #     print(f"\t{i}")



    def short_circuit_jumps(self, cfg):
        for b in self.blocks(cfg):
            size = len(b.instructions)
            idx = 0

            # finds first jump inside block
            while idx < size and b.instructions[idx][0] != "jump":
                idx += 1
            
            # if jump was not last instruction
            # removes all following instructions
            if idx < size - 1:
                del b.instructions[idx + 1:]

    def merge_blocks(self, cfg):
        pass
    
    def discard_already_allocd(self, cfg):
        allocd = {}

        for b in self.blocks(cfg):
            to_discard = []

            # iterates through all instruction in block
            # to find allocs tha can be removed
            for idx, inst in enumerate(b.instructions):
                opcode = self.get_opcode(inst)
                target = self.get_target(inst)

                if opcode != "alloc":
                    continue
                
                if target not in allocd:
                    allocd[target] = True
                else:
                    to_discard.append(idx)
            
            # removes from last to first to no messup
            # list indexes
            for idx in reversed(to_discard):
                b.instructions.pop(idx)
    
    def discard_literal_allocs(self, cfg):

        for b in self.blocks(cfg):
            allocs = {}
            to_discard = []

            for idx, inst in enumerate(b.instructions):
                opcode = self.get_opcode(inst)
                target = self.get_target(inst)

                if opcode == "alloc":
                    allocs[target] = idx
                
                if opcode == "literal" and target in allocs:
                    to_discard.append(allocs[target])
            
            # removes from last to first to no messup
            # list indexes
            for idx in sorted(to_discard, reverse=True):
                # print(idx, b.label, b.instructions[idx])
                b.instructions.pop(idx)
            
    def discard_unused_allocs(self, cfg):
        pass

        for b in self.blocks(cfg):
            to_discard = []

            for idx, inst in enumerate(b.instructions):
                opcode = self.get_opcode(inst)
                if opcode != "alloc":
                    continue
                
                target = self.get_target(inst)

                for use_set in self.lv_use.values():
                    if target in use_set:
                        break
                else:
                    to_discard.append(idx)

            for idx in reversed(to_discard):
                b.instructions.pop(idx)



    def appendOptimizedCode(self, cfg):
        bb = EmitBlocks()
        bb.visit(cfg)
        for _code in bb.code:
            self.code.append(_code)
    

    def visit_Program(self, node: Node):
        # First, save the global instructions on code member
        self.code = node.text[:]  # [:] to do a copy
        self.text = node.text[:]
        for _decl in node.gdecls:
            if isinstance(_decl, FuncDef):
                self.fix_cfg(_decl.cfg)
                # start with Reach Definitions Analysis
                self.buildRD_blocks(_decl.cfg)
                self.computeRD_gen_kill(_decl.cfg)
                self.computeRD_in_out(_decl.cfg)
                # and do constant propagation optimization
                self.constant_propagation(_decl.cfg)

                # after do live variable analysis
                self.buildLV_blocks(_decl.cfg)
                self.computeLV_use_def(_decl.cfg)
                self.computeLV_in_out(_decl.cfg)
                # and do dead code elimination
                self.deadcode_elimination(_decl.cfg)

                # after that do cfg simplify (optional)
                self.short_circuit_jumps(_decl.cfg)
                self.merge_blocks(_decl.cfg)
                self.discard_unused_allocs(_decl.cfg)
                self.discard_already_allocd(_decl.cfg)
                self.discard_literal_allocs(_decl.cfg)

                # finally save optimized instructions in self.code
                self.appendOptimizedCode(_decl.cfg)

                # clears for next iter
                self.clear_rd()
                self.clear_lv()

        if self.viewcfg:
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name + ".opt")
                    dot.view(_decl.cfg)


if __name__ == "__main__":

    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script runs the interpreter on the optimized uCIR \
              and shows the speedup obtained from comparing original uCIR with its optimized version.",
        type=str,
    )
    parser.add_argument(
        "--opt",
        help="Print optimized uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--speedup",
        help="Show speedup from comparing original uCIR with its optimized version.",
        action="store_true",
        default=True,
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    parser.add_argument(
        "-c",
        "--cfg",
        help="show the CFG of the optimized uCIR for each function in pdf format",
        action="store_true",
    )
    args = parser.parse_args()

    speedup = args.speedup
    print_opt_ir = args.opt
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

    gen = CodeGenerator(False)
    gen.visit(ast)
    gencode = gen.code

    opt = DataFlow(create_cfg)
    opt.visit(ast)
    optcode = opt.code
    if print_opt_ir:
        print("Optimized uCIR: --------")
        opt.show()
        print("------------------------\n")

    speedup = len(gencode) / len(optcode)
    sys.stderr.write(
        "[SPEEDUP] Default: %d Optimized: %d Speedup: %.2f\n\n"
        % (len(gencode), len(optcode), speedup)
    )

    vm = Interpreter(interpreter_debug)
    vm.run(optcode)
