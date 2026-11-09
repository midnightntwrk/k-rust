// Flow fixture: the shapes of an invariant's violation form that the critical-pair check shows to
// be a function with no premise. Each function is a priority group of one `false` equation (or
// `true`, for the existential dual) over a collection pattern whose bindings the rest of the
// left-hand side does not fix, beside an `owise` equation; the result reads no binding the
// pattern chose, so the self-pair joins. Each shape guards a pair of rules split on its
// condition: the corpus steps the rule the condition refutes, and the rule it makes hold, which
// no program fires, is the argued obligation. The recursive walk reads the binding it chose, and
// is the negative control.
module SHAPES-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= cmp(Int, Int)   [symbol(cmp)]
               | touch(Int, Int) [symbol(touch)]
               | store(Int)      [symbol(store)]
               | drop(Int)       [symbol(drop)]
               | "boot"          [symbol(boot)]
               | read(Int)       [symbol(read)]
               > Pgm ";" Pgm     [symbol(seq), right]
endmodule

module SHAPES
  imports SHAPES-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports SET

  // A permission, a user-declared constructor sort.
  syntax Perm ::= "ro" [symbol(ro)] | "rw" [symbol(rw)]

  configuration
    <t>
      <k> $PGM:Pgm </k>
      <memory> 8 |-> 0 9 |-> 1 </memory>
      <owners> 1 |-> SetItem(8) </owners>
      <perms> 0 |-> ro 8 |-> rw </perms>
      <roots> SetItem(8) </roots>
      <rom> 0 |-> 7 </rom>
      <romEnd> 4 </romEnd>
    </t>

  // Whether an address lies in the ROM region, which ends at `E`.
  syntax Bool ::= inRom(Int, Int) [function, total, symbol(inRom)]
  rule inRom(E, A) => A <Int E

  // Whether a permission allows a store, by its constructor.
  syntax Bool ::= writable(Perm) [function, total, symbol(writable)]
  rule writable(rw) => true
  rule writable(ro) => false

  // Two bound entries with a pairwise property: the values grow with the keys.
  syntax Bool ::= monotone(Map) [function, total, symbol(monotone)]
  rule monotone((K1:Int |-> V1:Int) (K2:Int |-> V2:Int) _:Map) => false
    requires K1 <Int K2 andBool V2 <Int V1
  rule monotone(_) => true [owise]

  // A nested collection: no owner's set of pages holds a ROM page.
  syntax Bool ::= ownedOutside(Map, Int) [function, total, symbol(ownedOutside)]
  rule ownedOutside((_ |-> (SetItem(P:Int) _:Set)) _:Map, E) => false requires inRom(E, P)
  rule ownedOutside(_, _) => true [owise]

  // An enum in the guard: no ROM address is writable.
  syntax Bool ::= romReadOnly(Map, Int) [function, total, symbol(romReadOnly)]
  rule romReadOnly((K:Int |-> P:Perm) _:Map, E) => false requires inRom(E, K) andBool writable(P)
  rule romReadOnly(_, _) => true [owise]

  // A set pattern: no root lies in the ROM region.
  syntax Bool ::= rootsOutside(Set, Int) [function, total, symbol(rootsOutside)]
  rule rootsOutside(SetItem(X:Int) _:Set, E) => false requires inRom(E, X)
  rule rootsOutside(_, _) => true [owise]

  // The existential dual: some binding lies in the ROM region.
  syntax Bool ::= someRom(Map, Int) [function, total, symbol(someRom)]
  rule someRom((K:Int |-> _) _:Map, E) => true requires inRom(E, K)
  rule someRom(_, _) => false [owise]

  // Two invariants combined over two such functions.
  syntax Bool ::= monotoneRoots(Map, Set, Int) [function, total, symbol(monotoneRoots)]
  rule monotoneRoots(M, S, E) => monotone(M) andBool rootsOutside(S, E)

  // The negative control: a recursive walk whose right-hand side reads the binding it chose.
  syntax Bool ::= outsideRomWalk(Map, Int) [function, total, symbol(outsideRomWalk)]
  rule outsideRomWalk(.Map, _) => true
  rule outsideRomWalk((K:Int |-> _) M, E) => notBool inRom(E, K) andBool outsideRomWalk(M, E)
  rule outsideRomWalk((_ |-> _) M, E) => outsideRomWalk(M, E) [owise]

  // An argued item's rule holds every cell its invariant reads: the compare rules hold `roots`
  // and `romEnd`, and the drop rules `memory`, for the combined invariant, and `unloaded` holds
  // `romEnd`, each unconstrained.
  rule [cmpOk]:  <k> cmp(A, B) => .K ... </k> <memory> (A |-> X) (B |-> Y) _ </memory>
    <roots> _ </roots> <romEnd> _ </romEnd> requires notBool (A <Int B andBool Y <Int X)
  rule [cmpBad]: <k> cmp(A, B) => .K ... </k> <memory> (A |-> X) (B |-> Y) _ </memory>
    <roots> _ </roots> <romEnd> _ </romEnd> requires A <Int B andBool Y <Int X

  // An owner's set is read whole, a set of one page. Where the inner set has a rest, the
  // backend's equation matching leaves the nested set pattern of `ownedOutside` undecided against
  // it, and so does the connection (`tests/coverage_argued.rs`).
  rule [touchOk]:  <k> touch(O, P) => .K ... </k> <owners> (O |-> SetItem(P)) _ </owners>
    <romEnd> E </romEnd> requires notBool inRom(E, P)
  rule [touchRom]: <k> touch(O, P) => .K ... </k> <owners> (O |-> SetItem(P)) _ </owners>
    <romEnd> E </romEnd> requires inRom(E, P)

  rule [storeOk]:  <k> store(A) => .K ... </k> <perms> (A |-> P:Perm) _ </perms>
    <romEnd> E </romEnd> requires notBool (inRom(E, A) andBool writable(P))
  rule [storeRom]: <k> store(A) => .K ... </k> <perms> (A |-> P:Perm) _ </perms>
    <romEnd> E </romEnd> requires inRom(E, A) andBool writable(P)

  rule [dropOk]:  <k> drop(A) => .K ... </k> <roots> SetItem(A) _ </roots> <romEnd> E </romEnd>
    <memory> _ </memory> requires notBool inRom(E, A)
  rule [dropRom]: <k> drop(A) => .K ... </k> <roots> SetItem(A) _ </roots> <romEnd> E </romEnd>
    <memory> _ </memory> requires inRom(E, A)

  rule [loaded]:   <k> boot => .K ... </k> <rom> R:Map </rom> requires size(R) >Int 0
  rule [unloaded]: <k> boot => .K ... </k> <rom> .Map </rom> <romEnd> _ </romEnd>

  rule [readOk]:  <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires notBool inRom(E, A)
  rule [readRom]: <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires inRom(E, A)

  rule [seq]: <k> P:Pgm ; Q:Pgm => P ~> Q ... </k>
endmodule
