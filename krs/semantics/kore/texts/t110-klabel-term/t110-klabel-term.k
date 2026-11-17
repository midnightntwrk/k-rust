module T110-KLABEL-TERM
  imports INT
  syntax Exp ::= bar() [symbol(bar)]
  syntax KItem ::= h(K) [symbol(h)]
  rule <k> bar() => h(#klabel(`bar`)) ... </k>
endmodule
