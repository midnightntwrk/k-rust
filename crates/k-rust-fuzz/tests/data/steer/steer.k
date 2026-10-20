module UNSP-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module UNSP
  imports UNSP-SYNTAX
  imports INT
  imports STRING
  imports K-EQUAL
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  syntax Int ::= f(Int)  [function, symbol(f)]
  rule [fa]: f(N) => 1 requires (1 <<Int N) >Int 0
  rule [fb]: f(N) => 2 requires N >Int 0
  rule [start]: <k> go(N) => .K ... </k> <out> _ => f(N) </out>
endmodule
