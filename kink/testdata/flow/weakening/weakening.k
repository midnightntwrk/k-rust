module WEAK-SYNTAX
  imports INT-SYNTAX
  syntax Val ::= v(Int) [symbol(v)]
  syntax Prog ::= runf(Int) [symbol(runf)] | rung(Int) [symbol(rung)] | runh(Int) [symbol(runh)] | out(Int) [symbol(out)]
  syntax Val ::= f(Int) [function, total, symbol(f)]
               | g(Int) [function, symbol(g)]
               | h(Int) [function, symbol(h)]
  syntax Int ::= w(Int) [function, total, symbol(w)]
endmodule

module WEAK
  imports WEAK-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [runf]: <k> runf(I) => f(I) </k>
  rule [rung]: <k> rung(I) => g(I) </k>
  rule [runh]: <k> runh(I) => h(I) </k>
  rule [out]: <k> v(I) => out(I) </k>
  rule [f-zero]: f(0) => v(1)
  rule [f-pos]: f(I) => v(I) requires I >Int 0
  rule [f-neg]: f(I) => v(0 -Int I) requires I <Int 0
  rule [g-zero]: g(0) => v(7)
  rule [g-else]: g(_) => v(3) [owise]
  rule [h-one]: h(1) => v(2)
  rule [h-pos]: h(I) => v(I) requires I >Int 1
  rule [h-low]: h(_) => v(5) [priority(60)]
  rule [w-def]: w(I) => I +Int 1
  rule [w-lemma]: w(I) +Int 0 => w(I) [simplification]
endmodule
