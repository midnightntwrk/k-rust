// A text importing UNIFICATION (unification.k) and SUBSTITUTION (substitution.md), neither a library
// module: kompile writes their declarations into the user module with their Source in K's builtin
// directory, among them the seven hooked symbols of UNIFICATION and the two of SUBSTITUTION, and
// the account prints how the reader classes each.
requires "unification.k"
requires "substitution.md"
module E6-BUILTINTEXT-UNIF-SUBST
  imports UNIFICATION
  imports SUBSTITUTION
endmodule
