// A diamond (FZ-DIFFEND): `go(N)` reaches `d(N)` at depth 2 through `b(N)` or through `c(N)`.
// Only the `c` path reads an implementation-chosen value: `size(keys_list(M))` of a two-key map
// (`MAP.keys_list`, class `order`), whose value is 2 in every listing order but marks all the
// same. Under `state-set` the two arrivals at `d(N)` merge: the result has one `d(N)` leaf, and
// the `c` path's mark is on the result's list, not on that leaf; under `path-set` the `c` path's
// leaf carries it. Strategy `any` follows `b` (written first), which reads nothing.

module DIAMOND-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module DIAMOND
  imports DIAMOND-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) | c(Int) | d(Int)

  configuration <k> $PGM:Pgm </k>

  rule [ab]: <k> go(N) => b(N) ... </k>
  rule [ac]: <k> go(N) => c(N) ... </k>
  rule [bd]: <k> b(N) => d(N) ... </k>
  rule [cd]: <k> c(N) => d(N +Int size(keys_list((1 |-> 0) (2 |-> 0))) -Int 2) ... </k>
endmodule
