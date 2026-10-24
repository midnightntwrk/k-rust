// A kind 1 invariant over a cell inside two nested cell collections (k2lean/docs/invariants.md;
// the gate's library `nested`, and crates/k2lean/tests/cli.rs):
// every <group> of the <groups> cell map holds a cell map of <member>s, each with a counter <v>
// that only ever grows by two or is reset. `k2lean gen --invariant even@v` lifts the K function
// `even` over both collections: for every group, for every member of it, `even` of its counter
// is `true`. `even` is structurally recursive on `Nat`, so its K equations are its unfolding set.
module NESTED-SYNTAX
  syntax Nat ::= "z" | s(Nat)
  syntax Cmd ::= bump(Nat, Nat)      // add 2 to the counter of member M of group G
               | reset(Nat, Nat)     // set member M of group G back to z
               | group(Nat)          // a new group G with one member z
               | member(Nat, Nat)    // a new member M of group G
               | move(Nat, Nat, Nat) // move member M of group G to group H
               | seq(Cmd, Cmd)
endmodule

module NESTED
  imports NESTED-SYNTAX
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <groups>
      <group multiplicity="*" type="Map">
        <gid> z </gid>
        <members>
          <member multiplicity="*" type="Map">
            <mid> z </mid>
            <v> z </v>
          </member>
        </members>
      </group>
    </groups>

  syntax Bool ::= even(Nat) [function, total]
  rule even(z) => true
  rule even(s(z)) => false
  rule even(s(s(N))) => even(N)

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k>
  rule <k> bump(G, M) => .K ... </k>
       <group> <gid> G </gid> <member> <mid> M </mid> <v> N => s(s(N)) </v> </member> ... </group>
  rule <k> reset(G, M) => .K ... </k>
       <group> <gid> G </gid> <member> <mid> M </mid> <v> _ => z </v> </member> ... </group>
  rule <k> group(G) => .K ... </k>
       <groups> ... (.Bag => <group> <gid> G </gid> <members> <member> <mid> z </mid> <v> z </v> </member> </members> </group>) </groups>
  rule <k> member(G, M) => .K ... </k>
       <group> <gid> G </gid> <members> ... (.Bag => <member> <mid> M </mid> <v> z </v> </member>) </members> </group>
  rule <k> move(G, M, H) => .K ... </k>
       <group> <gid> G </gid> <members> ... (<member> <mid> M </mid> <v> N </v> </member> => .Bag) </members> </group>
       <group> <gid> H </gid> <members> ... (.Bag => <member> <mid> M </mid> <v> N </v> </member>) </members> </group>
endmodule
