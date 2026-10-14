module PROBE-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Exp ::= Int | Id
               | "zeroAlias" [symbol(zeroAlias), alias]
               | "(" Exp ")" [bracket]
               > left: Exp "*" Exp [symbol(mul), strict]
               > left: Exp "+" Exp [symbol(add), strict]
  syntax Stmt ::= Id "=" Exp ";" [symbol(assign), strict(2)]
                | "{" Stmt "}" [symbol(block), format(%1%i%n%2%d%n%3)]
                | Stmt Stmt [symbol(seq), format(%1%n%2), right]
endmodule
module PROBE
  imports PROBE-SYNTAX
  imports INT
  imports MAP
  imports ID
  configuration <k color="green"> $PGM:Stmt </k> <env> .Map </env>
  syntax KResult ::= Int
  rule zeroAlias => 0
  rule <k> X:Id = I:Int ; => .K ...</k> <env> E => E[X <- I] </env>
  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ...</k>
  rule <k> { S } => S ...</k>
  rule I1 + I2 => I1 +Int I2
  rule I1 * I2 => I1 *Int I2
endmodule
