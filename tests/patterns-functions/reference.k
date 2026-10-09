// The aliases fixture written by hand in K, the way a K author writes it:
// the gate requires Java K to run it exactly as it runs the emitted K.
module ALIASES-REFERENCE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Value ::= Int | Bool
  syntax Exp ::= Value | Seq
               | "pair" "(" Exp "," Exp ")"
               | "dup" "(" Exp ")"
               | "wrap" "(" Exp ")"
  syntax Seq ::= "cons" "(" Exp "," Seq ")" | "nil"
               | "rest" "(" Seq ")" [function, total]
endmodule

module ALIASES-REFERENCE
  imports ALIASES-REFERENCE-SYNTAX

  syntax KResult ::= Value

  configuration <k> $PGM:Exp </k>

  rule <k> dup((pair(A, B) #as P)) => pair(P, pair(B, A)) ... </k>
  rule <k> wrap((pair(A, _) #as P)) => pair(A, P) ... </k>
  rule rest(cons(_, (cons(_, _) #as More))) => More
  rule rest(_) => nil [owise]
endmodule
