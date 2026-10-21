// SYM-3B-05 audit fixture: symmem's write/load over `Int` addresses, plus rules whose
// applicability to a symbolic `Int` subject depends on its value without a `requires`
// (a repeated variable, `Int` and `Bool` literals, an `owise` fallback) and one whose
// `requires` uses `&Int`, which k-rust's SMT translation leaves uninterpreted (`smtlib`).
module SYMNARROW-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | copy(Int, Int) [symbol(copy)]
              | pin(Int) [symbol(pin)]
              | flag(Bool) [symbol(flag)]
              | pick(Int) [symbol(pick)]
              | gate(Int) [symbol(gate)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module SYMNARROW
  imports SYMNARROW-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]: seq(write(addr(A), V), P) => P
  rule [load]:  seq(load(addr(A), V), P) => P
  rule [copy]:  seq(copy(A, A), P) => P
  rule [pin]:   seq(pin(0), P) => P
  rule [flag]:  seq(flag(true), P) => P
  rule [pick]:  seq(pick(0), P) => P
  rule [pickOwise]: seq(pick(_), _) => halt [owise]
  // `A &Int 1` is 0 or 1, so no instance takes this rule.
  rule [gate]:  seq(gate(A), P) => P requires A &Int 1 ==Int 2
endmodule
