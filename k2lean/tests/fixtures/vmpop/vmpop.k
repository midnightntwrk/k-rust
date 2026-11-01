// `vmpri` with `pop` in two steps: `pop` becomes `#pop` where the stack is not empty
// (`pop-start`), and `#pop` pops (`pop-done`); `itemOk` holds of `#pop`; every other rule is
// `vmpri`'s. Against `vmpop1` (`pop` in one step), `k2lean refine` relates them by a stuttering
// bisimulation with the ranks of `vmpri` (`demos/VmPopRefine`, `docs/design.md` section 3.5):
// `pop-underflow`, the `owise` rule, overlaps `pop` at a rank after it, so its steps correspond
// only where the split's first step does not apply in either definition.
requires "domains.md"

module VMPOP-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "push" "(" Int ")" | "add" | "div" | "pop"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module VMPOP
  imports VMPOP-SYNTAX
  imports INT
  imports BOOL
  syntax Stack ::= ".Stack" | Int ":" Stack
  syntax Status ::= "ok" | "underflow" | "divzero"
  syntax KItem ::= "#halt" "(" Status ")"
  syntax KItem ::= "#pop"
  configuration <T> <k> $PGM:Pgm </k> <stack> .Stack </stack> </T>

  rule <k> I:Instr ; P:Pgm => I ~> P ... </k> [label(seq)]
  rule <k> .Pgm => #halt(ok) ... </k> [label(end)]
  rule <k> push(I) => .K ... </k> <stack> S => I : S </stack> [label(push)]
  rule <k> add => #halt(underflow) ... </k> <stack> .Stack </stack> [label(add-underflow0), priority(40)]
  rule <k> add => #halt(underflow) ... </k> <stack> _ : .Stack </stack> [label(add-underflow1), priority(40)]
  rule <k> add => .K ... </k> <stack> A : B : S => A +Int B : S </stack> [label(add)]
  rule <k> div => .K ... </k> <stack> A : B : S => A /Int B : S </stack> requires B =/=Int 0 [label(div)]
  rule <k> div => #halt(divzero) ... </k> <stack> _ : B : _ </stack> requires B ==Int 0 [label(div-zero)]
  rule <k> div => #halt(underflow) ... </k> <stack> .Stack </stack> [label(div-underflow0)]
  rule <k> div => #halt(underflow) ... </k> <stack> _ : .Stack </stack> [label(div-underflow1)]
  rule <k> pop => #pop ... </k> <stack> _ : _ </stack> [label(pop-start)]
  rule <k> #pop => .K ... </k> <stack> _ : S => S </stack> [label(pop-done)]
  rule <k> pop => #halt(underflow) ... </k> [label(pop-underflow), owise]

  syntax Bool ::= kOk(K) [function, total]
                | itemOk(KItem) [function, total]
                | halted(K) [function, total]
  rule kOk(.K) => true
  rule kOk(I ~> K) => itemOk(I) andBool kOk(K)
  rule itemOk(_:Instr) => true
  rule itemOk(_:Pgm) => true
  rule itemOk(#halt(_)) => true
  rule itemOk(#pop) => true
  rule itemOk(_) => false [owise]
  rule halted(.K) => true
  rule halted(#halt(_) ~> _) => true
  rule halted(_) => false [owise]
endmodule
