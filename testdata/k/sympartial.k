// SYM-3B-05 audit fixture: a `requires` over a partial function. The ground instance
// `half(0)` is stuck (`10 /Int 0` is undefined). k-rust 347f693e simplified the symbolic
// condition `10 /Int A ==Int 10 /Int A` to `true` and dropped its definedness `A =/=Int 0`;
// since k-rust KK-45/KK-46 the condition states it, and the symbolic run splits like the
// ground one. `halflet` states a condition with the same definedness through `#let` (it holds
// wherever it is defined); k-rust declared the generated lambda `total` whatever its body until
// KK-71, and the condition then lost `A =/=Int 0`. The portable build parses `#let` since KK-72.
module SYMPARTIAL-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | half(Int) [symbol(half)]
              | halflet(Int) [symbol(halflet)]
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
  rule [halflet]: seq(halflet(A), P) => P
    requires (#let Y = A #in 10 /Int Y) <=Int (#let Y = A #in 10 /Int Y)
endmodule
