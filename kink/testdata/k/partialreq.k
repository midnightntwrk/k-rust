// variable-identity TB-01 (D-B, trust-base item T-UNSAT): rule conditions over the partial
// `/Int`. A remainder leaf has K instances where the division is undefined (Y = 0): `pos`'s
// condition is false or undefined there, and `same`'s condition holds wherever it is defined,
// so its remainder is empty except where `X /Int Y` is undefined. A solver that treated `/Int`
// as total without the remainder's definedness would refute that remainder.
module PARTIALREQ-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= pos(Int, Int) [symbol(pos)]
                | same(Int, Int) [symbol(same)]
                | yes(Int) [symbol(yes)]
                | "halt" [symbol(halt)]
endmodule

module PARTIALREQ
  imports PARTIALREQ-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  rule [pos]:  pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0
  rule [same]: same(X, Y) => halt requires X /Int Y <=Int X /Int Y
  rule [yes]:  yes(_) => halt
endmodule

// variable-identity TV-01 review 2 (T-UNSAT attacks): complementary rule conditions over a
// partial term. Where the partial term is undefined neither condition holds, so the remainder
// is a stuck state with K instances; only the definedness inside both negations keeps a
// solver that reads the partial operation as total from refuting it.
//   dv:  /Int, undefined at Y = 0.
//   md:  %Int, undefined at Y = 0.
//   cmp: the partial function part, defined only at 0 (undefined at X = 1).
//   ow:  part's condition against an owise rule, which applies where part(X) is undefined.
//   pair: no rule; carries a test-written path condition.
module TV01UNSAT-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= part(Int) [function, symbol(part)]
  syntax Prog ::= dv(Int, Int) [symbol(dv)]
                | md(Int, Int) [symbol(md)]
                | cmp(Int) [symbol(cmp)]
                | ow(Int) [symbol(ow)]
                | pair(Int, Int) [symbol(pair)]
                | "yes" [symbol(yes)]
                | "no" [symbol(no)]
endmodule

module TV01UNSAT
  imports TV01UNSAT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  rule [part]: part(0) => 7
  rule [dvyes]: dv(X, Y) => yes requires X /Int Y >Int 0
  rule [dvno]:  dv(X, Y) => no  requires X /Int Y <=Int 0
  rule [mdyes]: md(X, Y) => yes requires X %Int Y ==Int 0
  rule [mdno]:  md(X, Y) => no  requires X %Int Y =/=Int 0
  rule [cmpyes]: cmp(X) => yes requires part(X) ==Int 7
  rule [cmpno]:  cmp(X) => no  requires part(X) =/=Int 7
  rule [owyes]: ow(X) => yes requires part(X) ==Int 7
  rule [owno]:  ow(_) => no [owise]
endmodule
