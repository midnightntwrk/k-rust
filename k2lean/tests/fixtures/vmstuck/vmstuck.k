// The stack machine of `vm` without the rule that halts `pop` on an empty stack: a gap in the
// semantics. `gen --progress` finds it as the one case of `progress` that does not close, `pop`'s;
// it is refuted by hand with the configuration `<k> pop </k> <stack> .Stack </stack>`, which
// satisfies `kOk`, has not halted, and has no rule (`generated/vmstuck/KVmStuck/ProgressHand.lean`).
requires "domains.md"

module VMSTUCK-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "push" "(" Int ")" | "add" | "div" | "pop"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module VMSTUCK
  imports VMSTUCK-SYNTAX
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

  // `gen --measure steps@k`: what is left to run, so every program halts (the machine has no jump).
  // An instruction counts one; a program twice its instructions plus one (`seq` takes one step per
  // instruction, `end` one); a halt counts nothing.
  syntax Int ::= steps(K) [function, total]
               | isz(KItem) [function, total]
               | plen(Pgm) [function, total]
  rule steps(.K) => 0
  rule steps(I ~> K) => isz(I) +Int steps(K)
  rule isz(_:Instr) => 1
  rule isz(P:Pgm) => plen(P)
  rule isz(_) => 0 [owise]
  rule plen(.Pgm) => 1
  rule plen(_ ; P) => 2 +Int plen(P)
  rule plen(_) >=Int 0 => true [simplification]
  rule steps(_) >=Int 0 => true [simplification]
endmodule
