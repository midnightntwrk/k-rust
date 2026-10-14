// Alias reversal: token and application right-hand sides, chained aliases, and a macro that is never reversed (krs-unparse unit-test oracle).
module ALIASES-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "zero" [symbol(zero), alias]
               | "sq" "(" Exp ")" [symbol(sq), alias]
               | "one" [symbol(one), macro]
               | "inc" "(" Exp ")" [symbol(inc)]
               | "inc2" "(" Exp ")" [symbol(inc2), alias]
               | "inc4" "(" Exp ")" [symbol(inc4), alias]
               > left: Exp "*" Exp [symbol(mul)]
  syntax Pgm ::= Exp ";" [symbol(stmt)]
               | Pgm Pgm [symbol(pgms), right, format(%1%n%2)]
endmodule

module ALIASES
  imports ALIASES-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule zero => 0
  rule sq(E) => E * E
  rule one => 1
  rule inc2(E) => inc(inc(E))
  rule inc4(E) => inc2(inc2(E))
endmodule
