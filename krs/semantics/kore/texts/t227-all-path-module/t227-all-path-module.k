// A module carrying all-path, with one rewrite rule.
module T227-ALL-PATH-MODULE [all-path]
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  rule <k> a() => b() ... </k>
endmodule
