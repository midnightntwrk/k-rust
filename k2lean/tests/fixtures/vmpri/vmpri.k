// The stack machine of `vm` written with priorities, as instruction sets often are: `add`'s
// underflow halts are special cases tried first (`priority(40)`), `pop`'s is the `owise` rule, the
// rest have the default priority, so `Step` has three ranks. `gen --progress` states that some rule
// of some rank applies (`Progress.App`), which is the unranked statement's meaning: the least rank
// that applies is the one `Step` takes (`Progress.App.least`). `add`'s case closes by rank 0 on the
// short stacks and by rank 1 on the others; `pop`'s by its `owise` rule (SND-15).
requires "domains.md"

module VMPRI-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "push" "(" Int ")" | "add" | "div" | "pop"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module VMPRI
  imports VMPRI-SYNTAX
  imports INT
  imports BOOL
  syntax Stack ::= ".Stack" | Int ":" Stack
  syntax Status ::= "ok" | "underflow" | "divzero"
  syntax KItem ::= "#halt" "(" Status ")"
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
  rule <k> pop => .K ... </k> <stack> _ : S => S </stack> [label(pop)]
  rule <k> pop => #halt(underflow) ... </k> [label(pop-underflow), owise]

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
