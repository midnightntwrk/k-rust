// state-observations SO-09, attack (b): steps taken from a state whose path condition holds a
// partial `/Int` under a negation. `same`'s condition holds wherever `X /Int Y` is defined, so
// its owise successor `other(X, Y)` has exactly the instances Y = 0, where the division is
// undefined; `pos`'s owise successor has the instances Y = 0 and those with X /Int Y <=Int 0.
// Read with `/Int` total and without the definedness inside the negation, the owise path
// condition of `same` would be refutable, and every event on that path Absent.
module PARTIALSTEP-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= same(Int, Int) [symbol(same)]
                | pos(Int, Int) [symbol(pos)]
                | other(Int, Int) [symbol(other)]
                | done(Int) [symbol(done)]
                | "halt" [symbol(halt)]
endmodule

module PARTIALSTEP
  imports PARTIALSTEP-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  rule [same]:    same(X, Y) => halt requires X /Int Y <=Int X /Int Y
  rule [sameOw]:  same(X, Y) => other(X, Y) [owise]
  rule [pos]:     pos(X, Y) => halt requires X /Int Y >Int 0
  rule [posOw]:   pos(X, Y) => other(X, Y) [owise]
  rule [other]:   other(_, Y) => done(Y)
endmodule
