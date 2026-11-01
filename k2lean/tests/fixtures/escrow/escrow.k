// Accounts in a cell collection, and amounts held in escrow in a map keyed by a counter. Value is
// conserved across both: the balances and the amounts held add up to the supply (`conserved`, two
// sums over maps, one over the cell collection, one reading a constructor's field).
requires "domains.md"

module ESCROW-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= "new" "(" Int ")"
              | "mint" "(" Int "," Int ")"
              | "lock" "(" Int "," Int ")"
              | "release" "(" Int "," Int ")"
              | "refund" "(" Int ")"
  syntax Ops ::= List{Op, ";"}
endmodule

module ESCROW
  imports ESCROW-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  // an amount held for its owner
  syntax Hold ::= hold(Int, Int)
  configuration <T>
      <k> $PGM:Ops </k>
      <accounts> <account multiplicity="*" type="Map" initial="">
        <id> 0 </id> <balance> 0 </balance>
      </account> </accounts>
      <escrow> .Map </escrow>
      <next> 0 </next>
      <supply> 0 </supply>
    </T>

  rule <k> O:Op ; Os:Ops => O ~> Os ... </k> [label(seq)]
  rule <k> .Ops => .K ... </k> [label(nil)]
  rule <k> new(A) => .K ... </k>
       <accounts> (.Bag => <account> <id> A </id> <balance> 0 </balance> </account>) ... </accounts>
    [label(new)]
  rule <k> mint(A, X) => .K ... </k>
       <account> <id> A </id> <balance> B => B +Int X </balance> </account>
       <supply> S => S +Int X </supply>
    requires X >=Int 0 [label(mint)]
  // the amount leaves the account into a new escrow entry
  rule <k> lock(A, X) => .K ... </k>
       <account> <id> A </id> <balance> B => B -Int X </balance> </account>
       <escrow> ... .Map => N |-> hold(A, X) ... </escrow>
       <next> N => N +Int 1 </next>
    requires 0 <=Int X andBool X <=Int B [label(lock)]
  // an entry paid to any account, or back to its owner
  rule <k> release(E, C) => .K ... </k>
       <escrow> ... E |-> hold(_, X) => .Map ... </escrow>
       <account> <id> C </id> <balance> B => B +Int X </balance> </account> [label(release)]
  rule <k> refund(E) => .K ... </k>
       <escrow> ... E |-> hold(A, X) => .Map ... </escrow>
       <account> <id> A </id> <balance> B => B +Int X </balance> </account> [label(refund)]

  syntax Int ::= bals(AccountsCell) [function]
               | held(Map) [function]
  rule bals(<accounts> .Bag </accounts>) => 0
  rule bals(<accounts> <account> <id> _ </id> <balance> B </balance> </account> R </accounts>)
    => B +Int bals(<accounts> R </accounts>)
  rule held(.Map) => 0
  rule held((_E |-> hold(_, X)) R) => X +Int held(R)

  // `gen --invariant conserved@T`
  syntax Bool ::= conserved(TCell) [function, total]
  rule conserved(<T> <k> _ </k> <accounts> AS </accounts> <escrow> E </escrow> <next> _ </next>
                    <supply> S </supply> </T>)
    => bals(<accounts> AS </accounts>) +Int held(E) ==Int S
endmodule
