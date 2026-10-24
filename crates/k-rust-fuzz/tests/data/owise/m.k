// FZ-POLISH review B1: g(X) => c requires X <=Int 0 beside two owise equations, a => and bb =>.
// The owise pair is not confluent at g(1) (both owise equations apply there and equate the
// constructors a and bb of one sort), never at g(0), where the priority-50 equation applies.
// This side stores g(N +Int 0).

module OW-SYNTAX
  imports INT-SYNTAX
  syntax A ::= "a" | "bb" | "c"
  syntax Pgm ::= go(Int)
endmodule
module OW
  imports OW-SYNTAX
  imports INT
  syntax A ::= g(Int) [function, total]
  rule g(X) => c requires X <=Int 0
  rule [ow1]: g(_) => a  [owise]
  rule [ow2]: g(_) => bb [owise]
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(N) => .K </k> <s> _ => g(N +Int 0) </s>
endmodule
