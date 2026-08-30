module DEEP-TERM
  imports INT

  syntax Term ::= "zero" [symbol(zero)]
                | "wrap" "(" Term ")" [symbol(wrap)]
                | "build" "(" Int ")"
  syntax Input ::= Term

  configuration <k> $PGM:Input </k>

  rule <k> build(N) => wrap(build(N -Int 1)) </k> requires N >Int 0
  rule <k> build(0) => zero </k>
endmodule
