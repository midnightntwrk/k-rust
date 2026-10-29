// Threads in a cell map whose `<k>` computes with a strict operator (`gen --progress`, SND-17): a
// value on `<k>` followed by a freezer is cooled by a rule whose head is the hole, a variable of
// sort `Exp`; a value of a subsort (`Int`) is at such a head, so the cooling rule is a candidate of
// the case of the value's head.
requires "domains.md"

module THREADEXP-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | Exp "+" Exp [strict]
endmodule

module THREADEXP
  imports THREADEXP-SYNTAX
  imports INT
  configuration <T>
      <threads> <thread multiplicity="*" type="Map" initial="">
        <id> 0 </id> <k> $PGM:Exp </k>
      </thread> </threads>
    </T>
  syntax KResult ::= Int
  rule I1:Int + I2:Int => I1 +Int I2 [label(add)]
endmodule
