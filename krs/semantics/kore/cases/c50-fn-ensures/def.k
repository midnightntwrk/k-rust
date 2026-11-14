// A function equation with an ensures (the sentences of kcore-spec's f2-examples/ens.k):
// `half(N) => N /Int 2 ensures N >=Int 0`, whose axiom is `half(N) = \and(N /Int 2, N >=Int 0 = true)`.
// The ensures is part of the right side: where the equation decides and N >=Int 0 holds, half(N)
// is N /Int 2; where it is false, half(N) has no value. Expected from the text: run(4) steps to
// done(2), a final configuration; run(-4) applies its rule with an undefined result, so it has no
// successor and is not final. The finals are done(2) alone.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= "go" | run(Int) | done(Int)
  syntax Int ::= half(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule half(N) => N /Int 2 ensures N >=Int 0
  rule <k> go => run(4) </k>
  rule <k> go => run(-4) </k>
  rule <k> run(N) => done(half(N)) </k>
endmodule
