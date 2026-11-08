// A console that builds a partial residue and then discards it, for kink-campaign's observation
// slot (tests/observation.rs, `a_discarded_residue_keeps_its_definedness_on_the_path`). `f` is
// partial: its equation gives a value only below 10, and its `#Ceil` lemma says it has one exactly
// there. From a count of 20, `build` puts `f(N)`, the residue `f(20)`, in `<junk>`, under cells
// only; `clear` replaces it by 0; `finish` leaves the count as it is; `spin` then advances the
// count forever, so a run that passes `build` is cut by the depth bound. The baseline's lemma
// refutes the definedness of `f(20)`, so its run from 20 is an undefined step at `build`. The
// mutations the test makes: the lemma is deleted (the definedness of `f(20)` is open: some model
// gives it a value and some none), or build's `f(N)` becomes 0.
module DISCARD-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "run" [symbol(run)]
               | "clear" [symbol(clear)]
               | "go" [symbol(go)]
               | "spin" [symbol(spin)]
endmodule
module DISCARD
  imports DISCARD-SYNTAX
  imports INT
  imports BOOL
  imports ML-SYNTAX
  configuration <k> $PGM:Cmd </k> <n> 0 </n> <junk> 0 </junk>
  syntax Int ::= f(Int) [function, symbol(f)]
  rule [f]: f(X) => X requires X <Int 10
  rule [fceil]: #Ceil(f(X)) => {(X <Int 10) #Equals true} [simplification]
  rule [build]: <k> run => clear </k> <n> N </n> <junk> _ => f(N) </junk>
  rule [clear]: <k> clear => go </k> <junk> _ => 0 </junk>
  rule [finish]: <k> go => spin </k>
  rule [spin]: <k> spin </k> <n> N => N +Int 1 </n>
endmodule
