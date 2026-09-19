module STAR-CELL-HEATING-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= Int
               | "(" Exp ")" [bracket]
               | Exp "[" Exp "]" [strict]
               > Exp "+" Exp [strict]
  syntax Stmt ::= Exp ";" [strict]
                | "spawn" "{" Stmt "}" ";"
                | Stmt Stmt [left]
endmodule

module STAR-CELL-HEATING-SET
  imports STAR-CELL-HEATING-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int
  configuration
    <tasks>
      <task multiplicity="*" type="Set">
        <k> $PGM:Stmt </k>
      </task>
    </tasks>
  rule I:Int[J:Int] => I +Int J [anywhere]
  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ...</k>
  rule <k> _:Int ; => .K ...</k>
  rule <k> I:Int + J:Int => I +Int J ...</k>
  rule <tasks> <task> <k> spawn { S } ; => .K ...</k> </task>
       (.Bag => <task> <k> S </k> </task>) ...</tasks>
endmodule

module STAR-CELL-HEATING
  imports STAR-CELL-HEATING-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int
  configuration
    <threads>
      <thread multiplicity="*" type="Map">
        <id> 0 </id>
        <k> $PGM:Stmt </k>
      </thread>
    </threads>
    <next> 1 </next>
  rule I:Int[J:Int] => I +Int J [anywhere]
  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ...</k>
  rule <k> _:Int ; => .K ...</k>
  rule <k> I:Int + J:Int => I +Int J ...</k>
  rule <thread>... <k> spawn { S } ; => .K ...</k> ...</thread>
       <next> N => N +Int 1 </next>
       (.Bag => <thread>... <k> S </k> <id> N </id> ...</thread>)
endmodule
