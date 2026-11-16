module E6-RANGEMAP-PATTERN
  imports INT
  imports RANGEMAP
  syntax KItem ::= "go" [symbol(go)] | "a" [symbol(a)] | m(RangeMap) [symbol(m)]
  rule <k> go => m([0, 2) r|-> a) </k>
  rule <k> m(([A, B) r|-> V) Rest) => V </k>
endmodule
