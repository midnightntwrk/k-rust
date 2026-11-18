module E6-RANGEMAP-REST
  imports INT
  imports SET
  imports RANGEMAP
  syntax KItem ::= "go" [symbol(go)] | "a" [symbol(a)] | "b" [symbol(b)]
  syntax KItem ::= res(RangeMap, Bool, Bool, RangeMap, RangeMap) [symbol(res)]
  rule <k> go => res(.RangeMap,
                     ([0, 3) r|-> a) <=RangeMap (([0, 3) r|-> a) ([5, 7) r|-> b)),
                     (([0, 3) r|-> a) ([5, 7) r|-> b)) <=RangeMap ([0, 3) r|-> a),
                     removeAll(([0, 10) r|-> a), SetItem([3, 5))),
                     updateRangeMap(([0, 10) r|-> a), ([3, 5) r|-> b))) </k>
endmodule
