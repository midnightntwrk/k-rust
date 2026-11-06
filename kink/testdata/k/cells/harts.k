// Cell projection fixture (kink-campaign tests/cells.rs): harts held by a Map collection keyed by
// <id>, each with an unobservable <tmp>, an optional <res> that holds an unobservable <rv>, and a
// Set collection of jobs, each with an unobservable <jt>; beside them a List collection of items,
// each with an unobservable <it>. Every unobservable cell lies inside an instance, so the
// projection leaves it out of each instance.
module HARTS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= hart(Int, Int, Int) [symbol(hart)]
                | res(Int, Int)       [symbol(res)]
                | free(Int)           [symbol(free)]
                | job(Int, Int, Int)  [symbol(job)]
                | item(Int, Int)      [symbol(item)]
                | seq(Prog, Prog)     [symbol(seq)]
endmodule

module HARTS
  imports HARTS-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
                <harts>
                  <hart multiplicity="*" type="Map">
                    <id> 0 </id>
                    <pc> 0 </pc>
                    <tmp unobservable=""> 0 </tmp>
                    <res multiplicity="?"> <rv unobservable=""> 0 </rv> </res>
                    <jobs>
                      <job multiplicity="*" type="Set"> <jv> 0 </jv> <jt unobservable=""> 0 </jt> </job>
                    </jobs>
                  </hart>
                </harts>
                <items>
                  <item multiplicity="*" type="List"> <iv> 0 </iv> <it unobservable=""> 0 </it> </item>
                </items>

  rule [seq]: <k> seq(P, Q) => P ~> Q ... </k>
  // A hart keyed I, at pc P, with tmp T, its <res> present and no job.
  rule [hart]: <k> hart(I, P, T) => .K ... </k>
               <harts> ( .Bag => <hart> <id> I </id> <pc> P </pc> <tmp> T </tmp>
                                   <res> <rv> 0 </rv> </res> <jobs> .Bag </jobs> </hart> ) ... </harts>
  rule [res]: <k> res(I, R) => .K ... </k>
              <hart> <id> I </id> <res> <rv> _ => R </rv> </res> ... </hart>
  rule [free]: <k> free(I) => .K ... </k>
               <hart> <id> I </id> ( <res> _ </res> => .Bag ) ... </hart>
  rule [job]: <k> job(I, V, T) => .K ... </k>
              <hart> <id> I </id> <jobs> ( .Bag => <job> <jv> V </jv> <jt> T </jt> </job> ) ... </jobs> ... </hart>
  // An item goes in front of the list.
  rule [item]: <k> item(V, T) => .K ... </k>
               <items> ( .Bag => <item> <iv> V </iv> <it> T </it> </item> ) ... </items>
endmodule
