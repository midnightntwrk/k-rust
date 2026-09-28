// Execution-identity audit fixture (EI-05, attack AT2). `f` is declared total but has an
// equation for 0 only, so `f(1)` stays in a state as a function residue: a value the
// definition does not fix. A mutant that adds `f(1) => 5` changes that residue into a value.
module RESIDUE-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= write(Int) [symbol(write)] | load(Int) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)] | seq(Op, Prog) [symbol(seq)]
endmodule

module RESIDUE
  imports RESIDUE-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule [f]: f(0) => 0

  rule [write]: seq(write(_), P) => P
  rule [load]:  seq(load(_), P) => P
endmodule
