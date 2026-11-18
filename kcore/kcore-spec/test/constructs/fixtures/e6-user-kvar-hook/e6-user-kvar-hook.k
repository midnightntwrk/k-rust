// A user's file declaring a sort as KVAR-SYNTAX declares KVar (`[token, hook(KVAR.KVar)]`), and a
// constructor over it. The reading of a builtin file's own hooked token sort (Parse.ownTokenHookedSort?)
// is not a user's file's: the user's hooked sort is refused (userHookedSort), so the sort is not
// one of the definition's and the constructor's declaration, which names it, is refused (unknownSort).
module E6-USER-KVAR-HOOK
  imports INT
  syntax Name [token, hook(KVAR.KVar)]
  syntax KItem ::= go(Name) [symbol(go)]
endmodule
