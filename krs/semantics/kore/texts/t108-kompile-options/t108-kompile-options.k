module T108-KOMPILE-OPTIONS-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | a(Int) [symbol(a)] | b(Int) [symbol(b)]
endmodule
module T108-KOMPILE-OPTIONS
  imports T108-KOMPILE-OPTIONS-SYNTAX
  imports INT
  imports MAP
  syntax Int ::= f(Int) [function, symbol(f)]
               | fh(Int) [function, hook(FOO.bar), symbol(fh)]
  rule f(0) => 1
  rule f(_) => 2 [owise]
  configuration <t> <k> $PGM:Exp </k> <m> .Map </m> </t>
  rule <k> a(X) => b(f(X)) ... </k> <m> M => M[X <- 1] </m>
  rule <k> b(X) => X ... </k> requires X >Int 1 +Int 1
endmodule
