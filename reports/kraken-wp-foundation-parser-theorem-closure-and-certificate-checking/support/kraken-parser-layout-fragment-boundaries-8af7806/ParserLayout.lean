module
import Kraken.X64.Parser
import Kraken.X64.Semantics
meta import Kraken.X64.Parser.Basic
meta import Kraken.X64.Semantics
meta import Kraken.Layout
open Kraken.X64.Parser

def input1 := ".section .rodata\nvalue:\n.byte 1\n.p2align 4\n.text\nmain: movq $42, %rax\nret\n"
def input2 := ".section .rodata\nvalue:\n.byte 2\n.p2align 4\n.text\nmain: movq $42, %rax\nret\n"
#eval stripDirectives input1
#eval (parse input1).map List.length
#eval (parse (stripDirectives input1)).map List.length
#eval match parse (stripDirectives input1), parse (stripDirectives input2) with
  | .ok p, .ok q => p == q
  | _, _ => false
#eval (parse ".align 16").map List.length
#eval (parse (stripDirectives ".align 16")).map List.length
#eval (parse "movq (%rdi), (%rsi)").map List.length
#eval (parse "syscall").map List.length
#eval (parse "mov $1, (%rax)").map List.length

def duplicates : Executable := {startAddr := 4096, program := [
  ⟨.label "same", 0⟩, ⟨.instr (.regular .W64 .W64 (.nop 1)), 1⟩,
  ⟨.label "same", 0⟩, ⟨.instr (.regular .W64 .W64 (.nop 1)), 1⟩]}
#eval (Executable.labels duplicates).label "same"
#eval (Executable.labels duplicates).label "missing"
def badLayout : Executable := {startAddr := 9223372036854775807, program := [⟨.instr (.regular .W64 .W64 (.nop 1)), 1⟩,
              ⟨.instr (.regular .W64 .W64 (.nop 1)), 1⟩] }
#eval (badLayout.withAddresses.map fun x => x.addr.toInt)
def zeroSize : Executable := {startAddr := 4096, program := [
  ⟨.instr (.regular .W64 .W64 (.nop 1)), 0⟩,
  ⟨.instr (.regular .W64 .W64 (.nop 1)), 0⟩]}
#eval (zeroSize.directivesAtAddress 4096).length
