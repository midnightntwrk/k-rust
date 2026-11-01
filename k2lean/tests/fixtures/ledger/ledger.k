// A ledger of balances: accounts in a map cell `<bal>` (an id to its balance), the supply minted so
// far and the fees collected. Value is conserved: every balance and every fee comes from minting, so
// the balances and the fees add up to the supply (`conserved`, a sum over the map read by
// `gen --invariant`). Rules write the map both ways K allows: by pattern (`A |-> (B => B +Int X)`, a
// binding deleted or inserted) and by the map hooks (`M[A <- 0]`, `M[A <- undef]`).
requires "domains.md"

module LEDGER-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= "open" "(" Int ")"
              | "close" "(" Int ")"
              | "drop" "(" Int ")"
              | "mint" "(" Int "," Int ")"
              | "burn" "(" Int "," Int ")"
              | "transfer" "(" Int "," Int "," Int ")"
              | "fee" "(" Int "," Int ")"
  syntax Ops ::= List{Op, ";"}
endmodule

module LEDGER
  imports LEDGER-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  configuration <T>
      <k> $PGM:Ops </k>
      <books> <bal> .Map </bal> <supply> 0 </supply> <fees> 0 </fees> </books>
    </T>

  rule <k> O:Op ; Os:Ops => O ~> Os ... </k> [label(seq)]
  rule <k> .Ops => .K ... </k> [label(nil)]
  rule <k> open(A) => .K ... </k> <bal> M => M [ A <- 0 ] </bal>
    requires notBool A in_keys(M) [label(open)]
  rule <k> close(A) => .K ... </k> <bal> ... A |-> 0 => .Map ... </bal> [label(close)]
  rule <k> drop(A) => .K ... </k> <bal> M => M [ A <- undef ] </bal>
    requires M [ A ] ==K 0 [label(drop)]
  rule <k> mint(A, X) => .K ... </k> <bal> ... A |-> (B => B +Int X) ... </bal>
       <supply> S => S +Int X </supply>
    requires X >=Int 0 [label(mint)]
  rule <k> burn(A, X) => .K ... </k> <bal> ... A |-> (B => B -Int X) ... </bal>
       <supply> S => S -Int X </supply>
    requires 0 <=Int X andBool X <=Int B [label(burn)]
  rule <k> transfer(A, C, X) => .K ... </k>
       <bal> ... A |-> (BA => BA -Int X) C |-> (BC => BC +Int X) ... </bal>
    requires 0 <=Int X andBool X <=Int BA [label(transfer)]
  rule <k> fee(A, X) => .K ... </k> <bal> ... A |-> (B => B -Int X) ... </bal>
       <fees> F => F +Int X </fees>
    requires 0 <=Int X andBool X <=Int B [label(fee)]

  // The total of the balances: a sum over the map, in no particular order (`+Int` is associative
  // and commutative, so every order gives one total).
  syntax Int ::= total(Map) [function]
  rule total(.Map) => 0
  rule total((_A |-> B:Int) R) => B +Int total(R)

  // `gen --invariant conserved@books`
  syntax Bool ::= conserved(BooksCell) [function, total]
  rule conserved(<books> <bal> M </bal> <supply> S </supply> <fees> F </fees> </books>)
    => total(M) +Int F ==Int S
endmodule
