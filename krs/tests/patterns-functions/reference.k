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

// The alternatives fixture written by hand in K.
module ALTERNATIVES-REFERENCE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Value ::= Int | Bool
  syntax Exp ::= Value
               | "color" "(" Exp ")"
               | "pick" "(" Exp ")"
               | "pair" "(" Exp "," Exp ")"
               | "red" "(" ")"
               | "green" "(" ")"
               | "blue" "(" ")"
  syntax Int ::= "code" "(" Exp ")" [function]
endmodule

module ALTERNATIVES-REFERENCE
  imports ALTERNATIVES-REFERENCE-SYNTAX

  syntax KResult ::= Value

  configuration <k> $PGM:Exp </k>

  rule code((red() #Or green() #Or blue())) => 1
  rule <k> color((red() #Or green() #Or blue())) => 1 ... </k>
  rule <k> (red() #Or green() #Or blue()) => 1 ... </k>
  rule <k> pick((pair(X, red()) #Or pair(X, green()))) => X ... </k>
endmodule

// The matches fixture written by hand in K; the negations use `:/=K`.
module MATCHES-REFERENCE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Value ::= Int | Bool
  syntax Exp ::= Value
               | "isPair" "(" Exp ")"
               | "pair" "(" Exp "," Exp ")"
               | "unit" "(" ")"
               | "boxed" "(" Exp ")"
  syntax Bool ::= "twin" "(" Exp ")" [function, total]
                | "known" "(" Exp ")" [function, total]
endmodule

module MATCHES-REFERENCE
  imports MATCHES-REFERENCE-SYNTAX
  imports BOOL

  syntax KResult ::= Value

  configuration <k> $PGM:Exp </k>

  rule <k> isPair(E) => true ... </k> requires pair(_, _) :=K E
  rule <k> isPair(E) => false ... </k> requires pair(_, _) :/=K E
  rule <k> boxed(E) => true ... </k> requires pair((pair(_, _) #as P), P) :=K E
  rule <k> boxed(E) => false ... </k> requires pair((pair(_, _) #as P), P) :/=K E
  rule twin(E) => pair(X, X) :=K E
  rule known(E) => (pair(_, _) #Or unit()) :=K E
endmodule

// The let fixture written by hand in K, with `#fun(P => B)(A)`, which K
// defines `#let P = A #in B` to be.
module LETS-REFERENCE-SYNTAX
  imports INT-SYNTAX

  syntax Value ::= Int
  syntax Exp ::= Value
               | "swap" "(" Exp ")"
               | "pair" "(" Exp "," Exp ")"
               | "shadow" "(" Exp ")"
               | "positive" "(" Exp ")"
  syntax Exp ::= "swapPair" "(" Exp ")" [function]
  syntax Int ::= "scale" "(" Exp ")" [function]
endmodule

module LETS-REFERENCE
  imports LETS-REFERENCE-SYNTAX
  imports INT

  syntax KResult ::= Value

  configuration <k> $PGM:Exp </k>

  rule <k> swap(E) => #fun(pair(X, Y) => pair(Y, X))(E) ... </k>
  rule <k> shadow(E) => pair(#fun(E2 => E2)(pair(E, E)), E) ... </k>
  rule <k> positive(E) => 1 ... </k> requires #fun(M:Int => M >Int 0)(E)
  rule swapPair(P) => #fun(pair(X, Y) => pair(Y, X))(P)
  rule scale(E) => #fun(M:Int => #fun(N:Int => N *Int M)(M +Int 1))(E)
endmodule

// The function-context fixture written by hand in K: `barPlus` reads the
// configuration with `[[ .. ]]`, and `barTwice` reads it through `barPlus`.
module CONTEXTS-REFERENCE-SYNTAX
  imports INT-SYNTAX

  syntax Value ::= Int
  syntax Exp ::= Value
               | "readBar" "(" ")"
               | "readTwice" "(" ")"
  syntax Int ::= "barPlus" "(" Int ")" [function, total]
  syntax Int ::= "barTwice" "(" Int ")" [function, total]
endmodule

module CONTEXTS-REFERENCE
  imports CONTEXTS-REFERENCE-SYNTAX
  imports INT

  syntax KResult ::= Value

  configuration <k> $PGM:Exp </k> <bar> 42 </bar> <baz> 0 </baz>

  rule [[ barPlus(N) => B +Int N ]] <bar> B </bar> <baz> 0 </baz> requires 0 <=Int B
  rule barTwice(N) => barPlus(N) +Int barPlus(N)
  rule <k> readBar() => barPlus(1) ... </k>
  rule <k> readTwice() => barTwice(1) ... </k>
endmodule
