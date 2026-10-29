// A fixture of `k2lean noninterference` with the shape of a contract with private state
// (k2lean/docs/design.md, section 3.7): private data comes from `witness()`, each call taking the
// next of the private answers in `<wit>`; the ledger `<ledger>` is public, and every operation on
// it is recorded in the public `<transcript>`, reads included, as is each `emit`; `disclose(E)`
// makes `E`'s value public, and records it in `<disclosed>`, a cell no rule reads. Loops have a
// constant bound. The security checker is the fixture contractsec.
requires "domains.md"

module CONTRACT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports ID-SYNTAX

  syntax Value ::= Int | Bool
  syntax KResult ::= Value

  syntax Expr ::= Value | Id
                | "witness" "(" ")"
                | "read" "(" Id ")"
                | "disclose" "(" Expr ")" [strict]
                | "(" Expr ")" [bracket]
                > left: Expr "+" Expr [seqstrict]
                > non-assoc: Expr "<" Expr [seqstrict]

  syntax Stmt ::= Id "=" Expr ";" [strict(2)]
                | "write" "(" Id "," Expr ")" ";" [strict(2)]
                | "emit" "(" Expr ")" ";" [strict]
                | "if" "(" Expr ")" Stmt "else" Stmt [strict(1)]
                | "repeat" "(" Int ")" Stmt
                | "{" Stmt "}"
                | "{" "}"
                > right: Stmt Stmt
endmodule

module CONTRACT
  imports CONTRACT-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports LIST

  syntax Entry ::= rd(Id, Value) | wr(Id, Value) | ev(Value)

  configuration
    <k> $PGM:Stmt </k>
    <env> .Map </env>
    <ledger> $LEDGER:Map </ledger>
    <wit> $WIT:List </wit>
    <transcript> .List </transcript>
    <disclosed> .List </disclosed>

  rule [var]: <k> X:Id => V ... </k> <env> ... X |-> V ... </env>
  rule [witness]: <k> witness() => V ... </k> <wit> ListItem(V:Value) => .List ... </wit>
  rule [read]: <k> read(X) => V ... </k> <ledger> ... X |-> V ... </ledger>
       <transcript> ... (.List => ListItem(rd(X, V))) </transcript>
  rule [disclose]: <k> disclose(V:Value) => V ... </k> <disclosed> ... (.List => ListItem(V)) </disclosed>
  rule [plus]: <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule [lt]: <k> I1:Int < I2:Int => I1 <Int I2 ... </k>

  rule [assign]: <k> X = V:Value ; => .K ... </k> <env> E => E [ X <- V ] </env>
  rule [write]: <k> write(X, V:Value) ; => .K ... </k> <ledger> L => L [ X <- V ] </ledger>
       <transcript> ... (.List => ListItem(wr(X, V))) </transcript>
  rule [emit]: <k> emit(V:Value) ; => .K ... </k> <transcript> ... (.List => ListItem(ev(V))) </transcript>
  rule [if-true]: <k> if (true) S else _ => S ... </k>
  rule [if-false]: <k> if (false) _ else S => S ... </k>
  rule [repeat]: <k> repeat(N) S => S ~> repeat(N -Int 1) S ... </k> requires N >Int 0
  rule [repeat-done]: <k> repeat(N) _ => .K ... </k> requires N <=Int 0
  rule [block]: <k> { S } => S ... </k>
  rule [skip]: <k> { } => .K ... </k>
  rule [seq]: <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>
endmodule
