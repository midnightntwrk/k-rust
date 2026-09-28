// Execution-identity audit fixture (EI-05, attack AT1). guardedmem with an existential:
// `write` continues with `stamp(?T)`, so the definition has existential rewrite variables and
// no initial variable is stable for the difference certificate. An AS5 guard split whose
// inserted copy renames `?T` to `?U` gives runs that are equal up to that renaming.
module FRESHGEN-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | stamp(Int) [symbol(stamp)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module FRESHGEN
  imports FRESHGEN-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]:      seq(write(addr(A), _), P) => seq(stamp(?T), P) requires A >=Int 0
  rule [writeFault]: seq(write(addr(A), _), _) => fault requires A <Int 0
  rule [stamp]:      seq(stamp(_), P) => P
  rule [load]:       seq(load(addr(A), _), P) => P requires A >=Int 0
  rule [loadFault]:  seq(load(addr(A), _), _) => fault requires A <Int 0
endmodule
