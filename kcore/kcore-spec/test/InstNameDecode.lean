/-
  KCore test: the decoder of instance names (KcoreSpec/InstNameDecode.lean) against
  `Parse.instName`, and on concrete names: instances at one and at two sorts decode, the empty
  sort list, an empty sort name, a missing `}`, characters after `}`, a `{` in a sort name and a
  name with no `{` do not, and a head may hold `}` or `,`.
-/
import KcoreSpec.Parse
import KcoreSpec.InstNameDecode

open KCore

/-- `Parse.instName` is the writing the decoder inverts. -/
theorem instDecode?_parseInstName {h : String} {xs : List String} (ok : InstNameOK h xs) :
    instDecode? (Parse.instName h xs) = some (h, xs) :=
  instDecode?_instName ok

example {n : String} {h : String} {xs : List String} (hd : instDecode? n = some (h, xs)) :
    n = Parse.instName h xs :=
  (instDecode?_eq_some hd).2

example : instDecode? "Lblite{Int}" = some ("Lblite", ["Int"]) := by decide +kernel
example : instDecode? "Lblsame{Int,Exp}" = some ("Lblsame", ["Int", "Exp"]) := by decide +kernel
example : instDecode? (Parse.instName "Lblsel" ["K"]) = some ("Lblsel", ["K"]) := by decide +kernel
example : instDecode? "Lbl}a,b{X}" = some ("Lbl}a,b", ["X"]) := by decide +kernel
example : instDecode? "h{}" = none := by decide +kernel
example : instDecode? "h{A,}" = none := by decide +kernel
example : instDecode? "h{,A}" = none := by decide +kernel
example : instDecode? "h{A" = none := by decide +kernel
example : instDecode? "h{A}x" = none := by decide +kernel
example : instDecode? "h{A{B}}" = none := by decide +kernel
example : instDecode? "{A}" = none := by decide +kernel
example : instDecode? "Lbl'Unds'-Int'Unds'" = none := by decide +kernel
example : InstNameOK "Lblsame" ["Int", "Exp"] := by decide +kernel
example : ¬ InstNameOK "Lblsame" [] := by decide +kernel

/-- One kernel instance of injectivity: `Lblite{Int}` is the only name decoding to (Lblite, [Int]). -/
example {n : String} (h : instDecode? n = some ("Lblite", ["Int"])) : n = "Lblite{Int}" :=
  instDecode?_inj h (by decide +kernel)

#print axioms instDecode?_instName
#print axioms instDecode?_eq_some
#print axioms instDecode?_inj
