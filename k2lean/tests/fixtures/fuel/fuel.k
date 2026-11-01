// Tasks that pay for every step from their own fuel (gas, generically): `<task>` cells, each with
// its code and its fuel. A step costs one; `spawn(G, Q)` gives a new task `G` of the parent's fuel
// and costs the parent two more (one for the step, one for the task it creates). The measure is
// what is left, `work(<tasks>)`: one per task plus its fuel, summed over the collection. Each rule
// lowers it locally, but `finish` (a task with no code left goes, with its fuel) lowers it only
// because that fuel is nonnegative, and the sum is nonnegative only because every task's fuel is:
// the invariant `nonneg@fuel`, for every element (`gen --measure ... --measure-invariant`).
requires "domains.md"

module FUEL-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "nop"
                 | "spawn" "(" Int "," Prog ")"
  syntax Prog ::= List{Instr, ";"}
endmodule

module FUEL
  imports FUEL-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <T>
      <tasks> <task multiplicity="*" type="Map" initial="">
        <id> 0 </id> <k> $PGM:Prog </k> <fuel> 10 </fuel>
      </task> </tasks>
      <next> 1 </next>
    </T>

  rule <k> nop ; P => P </k> <fuel> F => F -Int 1 </fuel> requires F >Int 0 [label(nop)]
  rule <tasks> <task> <k> spawn(G, Q) ; P => P </k> <fuel> F => F -Int G -Int 2 </fuel> ... </task>
         (.Bag => <task> <id> N </id> <k> Q </k> <fuel> G </fuel> </task>) ... </tasks>
       <next> N => N +Int 1 </next>
    requires 0 <=Int G andBool G +Int 2 <=Int F [label(spawn)]
  rule <tasks> <task> <k> .Prog </k> ... </task> => .Bag ... </tasks> [label(finish)]

  // `gen --invariant nonneg@fuel`: every task's fuel
  syntax Bool ::= nonneg(Int) [function, total]
  rule nonneg(F) => F >=Int 0

  // `gen --measure work@tasks --measure-invariant`: one per task plus its fuel
  syntax Int ::= work(TasksCell) [function]
  rule work(<tasks> .Bag </tasks>) => 0
  rule work(<tasks> <task> <id> _ </id> <k> _ </k> <fuel> F </fuel> </task> Ts </tasks>)
    => 1 +Int F +Int work(<tasks> Ts </tasks>)
endmodule
