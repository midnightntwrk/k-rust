// An overloaded list family (FZ-OVERLIST, FZ-DATAEND): `Ids` and `Exps` are both `overload(Exps)`
// lists and `Exps ::= Ids`, so the compiler emits the overload equations
// `_,_Exps(inj{Id,Exp}(E), inj{Ids,Exps}(Es)) = inj{Ids,Exps}(_,_Ids(E, Es))` and
// `.Exps = inj{Ids,Exps}(.Ids)`, and `_,_Exps` is an equation head. `h(3)` stores
// `_,_Exps(inj{Int,Exp}(3), inj{Ids,Exps}(.Ids))` in `<s>`: no overload equation applies (an
// `Int` is no `Id`), so that application is a normal form and the end is data.

module OV-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule

module OV
  imports OV-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k> <s> .K </s>

  rule [store]: <k> h(Es) => .K </k> <s> _ => Es </s>
endmodule
