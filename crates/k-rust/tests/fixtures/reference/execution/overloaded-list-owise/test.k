module OVERLOADED-LIST-OWISE-SYNTAX
  imports INT-SYNTAX

  syntax Name                                      [token]
  syntax Names ::= List{Name, ","}                [overload(exps)]
  syntax Exp ::= Int | Name
  syntax Exps ::= List{Exp, ","}                  [overload(exps)]
  syntax Val
  syntax Exp ::= Val
  syntax Exps ::= Vals
  syntax Vals ::= List{Val, ","}                  [overload(exps)]
  syntax Bottom
  syntax Bottoms ::= List{Bottom, ","}            [overload(exps)]

  syntax Exp ::= "[" Exps "]" | "pipe" "(" Exps ";" Exp ")" [symbol(pipe)]
  syntax Val ::= "[" Vals "]"
  syntax Pgm ::= "nil-cons" | "one-cons" | "cons-nil"
endmodule

module OVERLOADED-LIST-OWISE
  imports OVERLOADED-LIST-OWISE-SYNTAX
  imports INT

  syntax Val ::= Int | Bottom
  syntax Vals ::= Bottoms
  syntax Exps ::= Names
  syntax Names ::= Bottoms
  syntax KResult ::= Int
  syntax Int ::= selectAux(Exps, Vals) [function]
               | select(Exp, Val) [function]

  rule selectAux(.Exps, .Vals) => 1
  rule selectAux((_:Exp, .Exps), (_:Val, .Vals)) => 1
  rule selectAux(_, _) => 2 [owise]

  rule select([_:Exps], [_:Vals]) => 2
  rule select(_:Name, _:Val) => 2
  rule select(_, _) => 1 [owise]

  configuration <k> $PGM:Pgm </k>
  rule nil-cons => selectAux(.Exps, (1, .Vals))
  rule one-cons => selectAux((1, .Exps), (1, 2, .Vals))
  rule pipe(.Exps ; E:Exp) => E [anywhere]
  rule cons-nil => select(pipe((1, .Exps) ; 1), [.Vals])
endmodule
