// Relational kind 1 invariants of SIMPLE (k2lean/docs/invariants.md, §9): every environment maps
// into the store, that is, every value of an environment is a key (a location) of `<store>`.
// - envsIn@T: every thread's `<env>` and `<genv>`. Not inductive (§8): `setEnv(E)` installs an
//   environment saved in `<k>`, and `return` and `throw` one saved in a stack frame.
// - envsOk@T: the strengthening of `demos/SimpleEnv`: also the environment of every `setEnv(E)`
//   item of every thread's `<k>`, and of every stack frame, with the frame's saved computation and
//   control (whichever of its stacks the frame saved), recursively. Preserved by every rule with no
//   hand case (the gate's heavy library `simpleenvs`, per-sort): `kIn`, `listIn`, `itemIn`, `ctlIn`
//   read the store through its keys only, which k2lean proves from their equations (monotonicity
//   in the store, k2lean/docs/invariants.md §3.1), so the rules that allocate keep it.
// - envsInV@T: envsIn with each environment read through `values(E)`, a list fold, instead of a
//   walk over the map's bindings.
// The thread cell map and the environments are walked by a free-key pattern (`K |-> V REST`, and
// `<thread> … </thread> REST`), which k2lean lowers to `MapHook.chooseFirst` (design.md, §2).
// The thread walks take the `<threads>` cell, not its content: krust compiles a variable written
// as the whole content of `<threads>` (`<T> <threads> Ts </threads> … </T>`) as one `<thread>` cell
// under an unconstrained key, not as the thread cell map (measured 2026-10-25, INV-1).
requires "simple-untyped.md"

module SIMPLE-ENVS
  imports SIMPLE-UNTYPED
  syntax TCell
  syntax ThreadsCell

  // Every value of the environment (the first argument) is a key of the store (the second).
  syntax Bool ::= allIn(Map, Map) [function, total]
  rule allIn(.Map, _) => true
  rule allIn((_ |-> V) E, S) => V in_keys(S) andBool allIn(E, S)

  syntax Bool ::= envsIn(TCell) [function, total]
                | threadsIn(ThreadsCell, Map) [function, total]
  rule envsIn(<T> TS:ThreadsCell <genv> G </genv> <store> S </store> ... </T>)
    => threadsIn(TS, S) andBool allIn(G, S)
  rule threadsIn(<threads> .Bag </threads>, _) => true
  rule threadsIn(<threads> <thread> <id> _ </id> <k> _ </k> <control> <fstack> _ </fstack> <xstack> _ </xstack> </control>
                   <env> E </env> <holds> _ </holds> </thread> Ts </threads>, S)
    => allIn(E, S) andBool threadsIn(<threads> Ts </threads>, S)

  syntax Bool ::= envsOk(TCell) [function, total]
                | threadsOk(ThreadsCell, Map) [function, total]
                | kIn(K, Map) [function, total]
                | listIn(List, Map) [function, total]
                | itemIn(KItem, Map) [function, total]
                | ctlIn(ControlCellFragment, Map) [function, total]
  rule envsOk(<T> TS:ThreadsCell <genv> G </genv> <store> S </store> ... </T>)
    => threadsOk(TS, S) andBool allIn(G, S)
  rule threadsOk(<threads> .Bag </threads>, _) => true
  rule threadsOk(<threads> <thread> <id> _ </id> <k> K </k> <control> <fstack> F </fstack> <xstack> X </xstack> </control>
                   <env> E </env> <holds> _ </holds> </thread> Ts </threads>, S)
    => allIn(E, S) andBool kIn(K, S) andBool listIn(F, S) andBool listIn(X, S) andBool threadsOk(<threads> Ts </threads>, S)
  rule kIn(.K, _) => true
  rule kIn(I:KItem ~> K, S) => itemIn(I, S) andBool kIn(K, S)
  rule listIn(.List, _) => true
  rule listIn(ListItem(I) L, S) => itemIn(I, S) andBool listIn(L, S)
  rule itemIn(setEnv(E), S) => allIn(E, S)
  rule itemIn((E, K, C), S) => allIn(E, S) andBool kIn(K, S) andBool ctlIn(C, S)
  rule itemIn((_, _, K, E, C), S) => allIn(E, S) andBool kIn(K, S) andBool ctlIn(C, S)
  rule itemIn(_, _) => true [owise]
  // A frame saves the control cell without the stack it is pushed on (SIMPLE's `lambda` saves it
  // without `<fstack>`, `try` without `<xstack>`), so each cell of the fragment may be absent.
  rule ctlIn(<control>-fragment <fstack> F </fstack> <xstack> X </xstack> </control>-fragment, S)
    => listIn(F, S) andBool listIn(X, S)
  rule ctlIn(<control>-fragment noFstackCell <xstack> X </xstack> </control>-fragment, S) => listIn(X, S)
  rule ctlIn(<control>-fragment <fstack> F </fstack> noXstackCell </control>-fragment, S) => listIn(F, S)
  rule ctlIn(<control>-fragment noFstackCell noXstackCell </control>-fragment, _) => true

  syntax Bool ::= envsInV(TCell) [function, total]
                | threadsInV(ThreadsCell, Map) [function, total]
                | locsIn(List, Map) [function, total]
  rule envsInV(<T> TS:ThreadsCell <genv> G </genv> <store> S </store> ... </T>)
    => threadsInV(TS, S) andBool locsIn(values(G), S)
  rule threadsInV(<threads> .Bag </threads>, _) => true
  rule threadsInV(<threads> <thread> <id> _ </id> <k> _ </k> <control> <fstack> _ </fstack> <xstack> _ </xstack> </control>
                    <env> E </env> <holds> _ </holds> </thread> Ts </threads>, S)
    => locsIn(values(E), S) andBool threadsInV(<threads> Ts </threads>, S)
  rule locsIn(.List, _) => true
  rule locsIn(ListItem(V) L, S) => V in_keys(S) andBool locsIn(L, S)
endmodule
