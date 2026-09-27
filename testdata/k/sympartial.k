// SYM-3B-05 audit fixture: a `requires` over a partial function. The ground instance
// `half(0)` is stuck (`10 /Int 0` is undefined). k-rust 347f693e simplified the symbolic
// condition `10 /Int A ==Int 10 /Int A` to `true` and dropped its definedness `A =/=Int 0`;
// since k-rust KK-45/KK-46 the condition states it, and the symbolic run splits like the
// ground one.
module SYMPARTIAL-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | half(Int) [symbol(half)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module SYMPARTIAL
  imports SYMPARTIAL-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]: seq(write(addr(A), V), P) => P
  rule [load]:  seq(load(addr(A), V), P) => P
  rule [half]:  seq(half(A), P) => P requires 10 /Int A ==Int 10 /Int A
endmodule
