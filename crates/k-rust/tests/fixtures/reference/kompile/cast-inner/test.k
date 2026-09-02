module CAST-INNER
  imports INT
  imports LIST
  imports MAP
  syntax KItem ::= start(List) [symbol(start)]
                 | startm(Map) [symbol(startm)]
                 | go(Int) [symbol(go)]
  rule <k> start(L) => go({L[0]}:>Int) ... </k>
  rule <k> startm(M) => go({M[0]}:>Int) ... </k>
  configuration <k> $PGM:KItem </k>
endmodule
