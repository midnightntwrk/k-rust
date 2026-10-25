// go(N) branches to a(N) or b(N); a(N) divides 10 by N (an undefined step at N = 0), b(N) ends.
module ND-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule

module ND
  imports ND-SYNTAX
  imports INT
  syntax KItem ::= a(Int) | b(Int)
  configuration <k> $PGM:Pgm </k> <out> 0 </out>
  rule <k> go(N) => a(N) ... </k>
  rule <k> go(N) => b(N) ... </k>
  rule <k> a(N) => .K ... </k> <out> _ => 10 /Int N </out>
  rule <k> b(N) => .K ... </k> <out> _ => N +Int 100 </out>
endmodule
