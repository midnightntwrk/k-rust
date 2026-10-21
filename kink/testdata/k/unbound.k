// variable-identity TB-01 (attack AT12): function equations that k-rust 927b9ce6 never uses,
// modelled on k-rust crates/k-rust/tests/unbound_equations.rs.
//   fres: an unbound result variable. The equation, closed over X and Y, says
//         fres(X) = X +Int 1, but matching fres(X) fixes no Y, so no instance is used.
//   freq: a requires-only variable. Closed over Z the equation says freq(X) = 1 (Z = X +Int 1
//         satisfies the requires), but the requires is contingent for a fixed X.
//   part: a partial function with no equation for any argument but 0.
// The run* rules put a call in a terminal under the free constructor done; pass leaves a call
// written in the initial state where it is.
module UNBOUND-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= fres(Int) [function, symbol(fres)]
               | freq(Int) [function, symbol(freq)]
               | part(Int) [function, symbol(part)]
  syntax Prog ::= runRes(Int) [symbol(runRes)]
                | runReq(Int) [symbol(runReq)]
                | runPart(Int) [symbol(runPart)]
                | pass(Int) [symbol(pass)]
                | done(Int) [symbol(done)]
endmodule

module UNBOUND
  imports UNBOUND-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  rule [fres]: fres(X) => Y requires Y ==Int X +Int 1
  rule [freq]: freq(X) => 1 requires Z >Int X
  rule [part]: part(0) => 7
  rule [runRes]: runRes(I) => done(fres(I))
  rule [runReq]: runReq(I) => done(freq(I))
  rule [runPart]: runPart(I) => done(part(I))
  rule [pass]: pass(I) => done(I)
endmodule

// variable-identity TV-01 review 2: ground terminals and rule choices that depend on a call
// k-rust keeps. The review's mutants disable part's one equation (requires false), so the
// baseline evaluates part(0) = 7 and the mutant keeps part(0); a model of the mutant with
// part(0) = 7 behaves exactly as the baseline, so no test may kill.
//   done/wrap/code/hold/keep: the call under an injection, a free constructor, an exit-code
//     constructor, a list and a map.
//   check: the call decides whether a rule applies (stuck against done).
//   sel/fsel: the call against an owise rule and an owise equation.
//   mk: a rule writes the call.
module TV01TERMINAL-SYNTAX
  imports INT-SYNTAX
  imports LIST
  imports MAP
  syntax Int ::= part(Int) [function, symbol(part)]
               | fsel(Int) [function, symbol(fsel)]
  syntax Val ::= wrap(Int) [symbol(wrap)]
               | Int
  syntax Prog ::= done(Val) [symbol(done)]
                | code(Int) [symbol(code)]
                | hold(List) [symbol(hold)]
                | keep(Map) [symbol(keep)]
                | check(Int) [symbol(check)]
                | sel(Int) [symbol(sel)]
                | "mk" [symbol(mk)]
endmodule

module TV01TERMINAL
  imports TV01TERMINAL-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports LIST
  imports MAP
  configuration <k> .K </k>

  rule [part]: part(0) => 7
  rule [fsel]: fsel(7) => 1
  rule [fselow]: fsel(_) => 0 [owise]
  rule [check]: check(7) => done(7)
  rule [sel]: sel(7) => done(7)
  rule [selow]: sel(_) => done(0) [owise]
  rule [mk]: mk => done(part(0))
endmodule
