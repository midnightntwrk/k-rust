// A stack machine: the shape of a virtual machine or an instruction set (`k2lean/docs/direction.md`
// §7). A program is a list of instructions; the operand stack is a cons sort, as KEVM's word stack
// is; an instruction that cannot run halts with a status (an exceptional halt, an acceptable
// ending), so no reachable configuration is stuck (`gen --progress`, SND-13). `kOk` says that `<k>`
// holds only instructions, programs and halts (the machine's well-formedness, a kind 1 invariant);
// `halted` says that the machine has halted (its acceptable endings).
requires "domains.md"

module VM-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "push" "(" Int ")" | "add" | "div" | "pop"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module VM
  imports VM-SYNTAX
  imports INT
  imports BOOL
  syntax Stack ::= ".Stack" | Int ":" Stack
  syntax Status ::= "ok" | "underflow" | "divzero"
  syntax KItem ::= "#halt" "(" Status ")"
  configuration <T> <k> $PGM:Pgm </k> <stack> .Stack </stack> </T>

  rule <k> I:Instr ; P:Pgm => I ~> P ... </k> [label(seq)]
  rule <k> .Pgm => #halt(ok) ... </k> [label(end)]
  rule <k> push(I) => .K ... </k> <stack> S => I : S </stack> [label(push)]
  rule <k> add => .K ... </k> <stack> A : B : S => A +Int B : S </stack> [label(add)]
  rule <k> add => #halt(underflow) ... </k> <stack> .Stack </stack> [label(add-underflow0)]
  rule <k> add => #halt(underflow) ... </k> <stack> _ : .Stack </stack> [label(add-underflow1)]
  rule <k> div => .K ... </k> <stack> A : B : S => A /Int B : S </stack> requires B =/=Int 0 [label(div)]
  rule <k> div => #halt(divzero) ... </k> <stack> _ : B : _ </stack> requires B ==Int 0 [label(div-zero)]
  rule <k> div => #halt(underflow) ... </k> <stack> .Stack </stack> [label(div-underflow0)]
  rule <k> div => #halt(underflow) ... </k> <stack> _ : .Stack </stack> [label(div-underflow1)]
  rule <k> pop => .K ... </k> <stack> _ : S => S </stack> [label(pop)]
  rule <k> pop => #halt(underflow) ... </k> <stack> .Stack </stack> [label(pop-underflow)]

  syntax Bool ::= kOk(K) [function, total]
                | itemOk(KItem) [function, total]
                | halted(K) [function, total]
  rule kOk(.K) => true
  rule kOk(I ~> K) => itemOk(I) andBool kOk(K)
  rule itemOk(_:Instr) => true
  rule itemOk(_:Pgm) => true
  rule itemOk(#halt(_)) => true
  rule itemOk(_) => false [owise]
  rule halted(.K) => true
  rule halted(#halt(_) ~> _) => true
  rule halted(_) => false [owise]
endmodule
