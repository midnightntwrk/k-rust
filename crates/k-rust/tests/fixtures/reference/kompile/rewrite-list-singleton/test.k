// Reduced from k/k-distribution/tests/regression-new/issue-1573/test.k (stage-12 finding:
// the `fun` rule's UNIQUE_ID differs from the reference because k-rust wraps each side of the
// `1 => foo(1)` rewrite in the user-list singleton constructor separately, where K's
// AddEmptyLists instantiates the rewrite at lub(Int, Int) = Int and wraps the whole rewrite).
module REWRITE-LIST-SINGLETON
  imports INT

  syntax IntList ::= List{Int, ""}

  syntax KItem ::= "go" | "fun" | "clear"

  configuration
    <top>
      <k> go ~> $PGM:K </k>
      <v> .IntList </v>
    </top>

  syntax Int ::= foo(Int) [function]
  rule foo(I) => 10 *Int I

  rule <k> go => .K ... </k>
       <v> _ => 1 </v>

  rule <k> fun => .K ... </k>
       <v> 1 => foo(1) </v>

  rule <k> clear => .K ... </k>
       <v> L:IntList => 2 L </v>
endmodule
