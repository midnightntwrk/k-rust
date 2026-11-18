module EXPR-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Value   ::= Int
                   | Bool

  syntax KResult ::= Value

  syntax Expr    ::= Value
                   | "(" Expr ")"   [bracket, format(%1%2%3)]

  syntax Expr    ::= "-" Expr       [strict, format(%1%2)]
                   | "!" Expr       [strict, format(%1%2)]
                   > left:
                     Expr "*" Expr  [seqstrict]
                   | Expr "/" Expr  [seqstrict]
                   > left:
                     Expr "+" Expr  [seqstrict]
                   | Expr "-" Expr  [seqstrict]
                   > left:
                     Expr ">=" Expr [seqstrict]
                   | Expr ">"  Expr [seqstrict]
                   | Expr "<=" Expr [seqstrict]
                   | Expr "<"  Expr [seqstrict]
                   > left:
                     Expr "==" Expr [seqstrict]
                   | Expr "!=" Expr [seqstrict]
                   > left:
                     Expr "&&" Expr [strict(1)]
                   > left:
                     Expr "||" Expr [strict(1)]
endmodule


module EXPR-RULES
  imports EXPR-SYNTAX
  imports INT
  imports BOOL

  rule - X => 0 -Int X
  rule ! B => notBool B

  rule X + Y => X +Int Y
  rule X - Y => X -Int Y
  rule X * Y => X *Int Y
  rule X / Y => X /Int Y

  rule I1 >= I2 => I1 >=Int I2
  rule I1 >  I2 => I1 >Int  I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 <  I2 => I1 <Int  I2

  rule B1 == B2 => B1 ==Bool B2
  rule I1 == I2 => I1 ==Int I2

  rule B1 != B2 => B1 =/=Bool B2
  rule I1 != I2 => I1 =/=Int  I2

  rule true  && B => B
  rule false && _ => false

  rule true  || _ => true
  rule false || B => B
endmodule


module EXPR
    imports EXPR-RULES

    configuration <k> $PGM:Expr </k>
endmodule


module CALC-SYNTAX
  imports EXPR-SYNTAX
  imports ID-SYNTAX

  syntax Expr ::= Id

  syntax Stmt ::= Id "=" Expr ";" [group(stmt), strict(2), format(%1 %2 %3%4)]
  syntax Stmt ::= right:
                  Stmt Stmt       [group(seq-stmt), format(%1%n%2)]

  syntax priority stmt > seq-stmt
endmodule


module CALC
  imports CALC-SYNTAX
  imports EXPR-RULES

  configuration
    <k   color="green">  $PGM:Stmt </k>
    <env color="yellow"> $ENV:Map  </env>

  rule [step]: <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>

  rule [var]:
    <k> X:Id => V ... </k>
    <env> X |-> V ... </env>

  rule [assign]:
    <k> X = V:Value ; => .K ... </k>
    <env> E => E [ X <- V ] </env>
endmodule


module IMP-SYNTAX
  imports CALC-SYNTAX

  syntax Stmt ::= "if" "(" Expr ")" Stmt "else" Stmt [group(stmt), strict(1), avoid, format(%1 %2%3%4% %5 %6 %7)] // dangling else
                | "if" "(" Expr ")" Stmt             [group(stmt), format(%1 %2%3%4 %5)]
                | "while" "(" Expr ")" Stmt          [group(stmt), format(%1 %2%3%4 %5)] // not strict!
                | "{" Stmt "}"                       [group(stmt), format(%1%i%n%2%d%n%3)]
                | "{" "}"                            [group(stmt), format(%1%2)]
endmodule


module IMP
  imports IMP-SYNTAX
  imports CALC

  rule [if-true]:  <k> if ( true  ) S1 else _  => S1 ... </k>
  rule [if-false]: <k> if ( false ) _  else S2 => S2 ... </k>

  rule [if-else]: <k> if ( C ) S => if ( C ) S else {} ... </k>

  rule [while]:
    <k>
      while ( C ) S
      =>
      if ( C ) {
        S
        while ( C ) S
      }
      ...
    </k>

  rule [block]: <k> { S } => S ~> { } ... </k>

  rule [done]: <k> { } => .K ... </k>
endmodule


module IMP-VERIFICATION-SYNTAX
    imports ID-SYNTAX

    syntax Id ::= r"\\$[a-zA-Z0-9\\_]+" [token]
endmodule


module IMP-VERIFICATION
    imports IMP-VERIFICATION-SYNTAX
    imports IMP

    // inequality sign normalization
    rule          A  >Int B  => B  <Int A [simplification]
    rule          A >=Int B  => B <=Int A [simplification]
    rule notBool (A  <Int B) => B <=Int A [simplification]
    rule notBool (A <=Int B) => B  <Int A [simplification]
endmodule

module IMP-SUM-SPEC
  imports IMP-VERIFICATION

  claim [sum-spec]:
      <k>
        while (!($n <= 0)) {
          $s = $s + $n;
          $n = $n + -1;
        }
      =>
        .K
      ...
      </k>
    <env>
        $n |-> (N:Int => 0)
        $s |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
    </env>
  requires N >=Int 0
  [circularity]

  claim [two-sum-spec]:
      <k>
        while (!($n <= 0)) {
          $s1 = $s1 + $n;
          $n = $n + -1;
        }
        while (!($m <= 0)) {
          $s2 = $s2 + $m;
          $m = $m + -1;
        }
      =>
        .K
      ...
      </k>
    <env>
        $n |-> (N:Int => 0)
        $m |-> (M:Int => 0)
        $s1 |-> (S1:Int => S1 +Int ((N +Int 1) *Int N /Int 2))
        $s2 |-> (S2:Int => S2 +Int ((M +Int 1) *Int M /Int 2))
    </env>
  requires N >=Int 0
   andBool M >=Int 0
  [circularity]

endmodule
