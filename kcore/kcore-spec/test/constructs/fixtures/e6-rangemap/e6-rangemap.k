module E6-RANGEMAP
  imports INT
  imports RANGEMAP
  syntax KItem ::= "go" [symbol(go)] | "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)]
  syntax KItem ::= res(Int, KItem, KItem, Bool, Bool, Int, Range, Int, Int, RangeMap) [symbol(res)]
  syntax RangeMap ::= "m" [function, total, symbol(m)]
  rule m => ([0, 3) r|-> a) ([5, 7) r|-> b)
  rule <k> go => res(size(m), m[1], m[3] orDefault c, 2 in_keys(m), 3 in_keys(m),
                     size(([0, 3) r|-> a) ([3, 5) r|-> a)), find_range(([0, 3) r|-> a) ([3, 5) r|-> a), 4),
                     size(([0, 10) r|-> a) [ [3, 5) <- b ]), size(([0, 10) r|-> a) [ [3, 5) <- undef ]),
                     ([0, 10) r|-> a) -RangeMap ([3, 5) r|-> a)) </k>
endmodule
