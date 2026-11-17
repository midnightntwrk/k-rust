module E6-RANGEMAP-KEYS
  imports INT
  imports SET
  imports RANGEMAP
  syntax KItem ::= "go" [symbol(go)] | "a" [symbol(a)] | "b" [symbol(b)]
  syntax KItem ::= res(Set) [symbol(res)]
  rule <k> go => res(keys(([0, 3) r|-> a) ([5, 7) r|-> b))) </k>
endmodule
