// A pool of tickets: `<issued>` binds each ticket issued (an id to its holder), `<left>` is how many
// may still be issued, `<cap>` how many may be issued in all. The rules check `<left>`; the measure
// counts what was issued, `cap - count(issued)`, the tickets still to issue. The two are related
// only by the invariant `pool` (what was issued and what is left add up to the cap), so the measure
// is nonnegative only where the invariant holds: `gen --measure ... --measure-invariant`
// (`Measure.bound`), with each rule's decrease local to the bindings it writes.
requires "domains.md"

module TICKETS-SYNTAX
  imports INT-SYNTAX
endmodule

module TICKETS
  imports TICKETS-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  configuration <T>
      <pool> <issued> .Map </issued> <left> 3 </left> <cap> 3 </cap> <next> 0 </next> </pool>
    </T>

  // one ticket, at the next id, to the holder 0
  rule <issued> M => M [ N <- 0 ] </issued> <left> L => L -Int 1 </left> <next> N => N +Int 1 </next>
    requires L >Int 0 andBool notBool N in_keys(M) [label(issue)]
  // two tickets at once, by pattern
  rule <issued> M => (N |-> 1) ((N +Int 1) |-> 1) M </issued> <left> L => L -Int 2 </left>
       <next> N => N +Int 2 </next>
    requires L >=Int 2 andBool notBool N in_keys(M) andBool notBool (N +Int 1) in_keys(M)
    [label(batch)]

  // how many tickets were issued: a sum over the map, a weight of one per binding
  syntax Int ::= count(Map) [function]
  rule count(.Map) => 0
  rule count((_ |-> _) R) => 1 +Int count(R)

  // `gen --invariant pool@pool`
  syntax Bool ::= pool(PoolCell) [function, total]
  rule pool(<pool> <issued> M </issued> <left> L </left> <cap> C </cap> <next> _ </next> </pool>)
    => count(M) +Int L ==Int C andBool L >=Int 0

  // `gen --measure todo@pool --measure-invariant`: the tickets still to issue
  syntax Int ::= todo(PoolCell) [function, total]
  rule todo(<pool> <issued> M </issued> <left> _ </left> <cap> C </cap> <next> _ </next> </pool>)
    => C -Int count(M)

  // `gen --step-property poolMono@pool --step-property-trans`: at every step the next id never
  // decreases and what is left never grows, one function of the whole `<pool>` cell before and after
  syntax Bool ::= poolMono(PoolCell, PoolCell) [function, total]
  rule poolMono(<pool> <issued> _ </issued> <left> L1 </left> <cap> _ </cap> <next> N1 </next> </pool>,
                <pool> <issued> _ </issued> <left> L2 </left> <cap> _ </cap> <next> N2 </next> </pool>)
    => N1 <=Int N2 andBool L2 <=Int L1
endmodule
