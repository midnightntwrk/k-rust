module FN-SYNTAX
  imports INT-SYNTAX
  syntax T ::= "z" [symbol(z)] | c(T) [symbol(c)]
  syntax KItem ::= go(Int) [symbol(go)] | run(Int, T) [symbol(run)]
  syntax Int ::= size(T) [function, symbol(size)]
endmodule
module FN
  imports FN-SYNTAX
  imports INT
  configuration <k> $PGM:K </k>
  rule <k> go(N) => run(N, z) </k>
  rule <k> run(N, T) => run(N -Int 1, c(T)) </k> requires N >Int 0
  rule <k> run(0, T) => size(T) </k>
  rule size(z) => 0
  rule size(c(T)) => 1 +Int size(T)
endmodule
