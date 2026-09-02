module EXISTS-ANON
  imports INT
  imports BOOL
  imports ML-SYNTAX
  syntax Bool ::= h(Int) [function, symbol(h)]
  rule h(X) => true requires #Exists _ . (X ==Int _ +Int 1) [simplification]
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(I) => go(I -Int 1) ... </k> requires h(I)
  configuration <k> $PGM:KItem </k>
endmodule
