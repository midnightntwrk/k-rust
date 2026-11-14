// c50 with an [owise] equation beside the one with an ensures (the sentences of kcore-spec's
// f2-examples/ens-owise.k): `half(_) => 0 [owise]`. The ensures is part of the first equation's
// right side and never part of whether it applies: at -4 the first equation's argument pattern
// matches and it has no requires, so it decides, and the [owise] equation does not apply there.
// Expected from the text: the same as c50, done(2) alone; half(-4) has no value, not 0, so run(-4)
// has no successor and is not final. Reading the ensures as a requires would give done(0) too.
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
  rule half(_) => 0 [owise]
  rule <k> go => run(4) </k>
  rule <k> go => run(-4) </k>
  rule <k> run(N) => done(half(N)) </k>
endmodule
