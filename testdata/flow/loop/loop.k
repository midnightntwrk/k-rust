// Flow fixture (F-03): programs that end, one that never ends, a rule no
// program reaches and a function equation that coverage cannot observe.
module LOOP-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "spin" "(" Exp ")" [strict, symbol(spin)]
               | "countdown" "(" Exp ")" [strict, symbol(countdown)]
               | "twice" "(" Exp ")" [strict, symbol(twice)]
               | "unused" "(" Exp ")" [strict, symbol(unused)]
endmodule

module LOOP
  imports LOOP-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  syntax Int ::= double(Int) [function, symbol(double)]
  rule double(I) => I *Int 2
  rule [spin]: spin(I:Int) => spin(I +Int 1)
  rule [countdown]: countdown(I:Int) => countdown(I -Int 1) requires I >Int 0
  rule [done]: countdown(0) => 0
  rule [twice]: twice(I:Int) => double(I)
  rule [unused]: unused(I:Int) => I
endmodule
