// The shapes of `operand_bindings.rs`: a sequencing rule whose operand is an instruction, a guarded
// rule and its complement, and a decoding rule with an `Int` binder.
module BINDINGS-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= inc(Int) [symbol(inc)]
                 | op(Int)  [symbol(op)]
  syntax Pgm ::= Instr
               | Instr ";" Pgm [symbol(seq)]
endmodule

module BINDINGS
  imports BINDINGS-SYNTAX
  imports INT
  imports BOOL

  configuration <T> <k> $PGM:Pgm </k> <acc> 0 </acc> </T>

  rule [split]: <k> I:Instr ; P:Pgm => I ~> P ... </k>
  rule [big]: <k> inc(N) => .K ... </k> <acc> A => A +Int N </acc> requires N >Int 100
  rule [small]: <k> inc(N) => .K ... </k> requires N <=Int 100
  rule [decode]: <k> op(B) => .K ... </k> <acc> A => A +Int B </acc>
endmodule
