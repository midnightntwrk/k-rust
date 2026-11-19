/-
  The associativity axiom of a hooked function with no equation, through the reader, on K 7.1.337
  kompile's own texts (`f2-examples/NAME.kompile.kore`, the text whose sha256 the fixture's
  kompile.txt records, with its paths restored). Run from the package root:
  `lake env lean -j1 test/HookAssocLaw.lean`. Facts about the semantics are kernel decisions.

  - `Add` (fixture rdr-hook-assoc, `plus(Int, Int) [function, total, hook(INT.add), assoc]`): the
    reader's `plus` is a parameter the registry's `INT.add` implements; the text's law axiom is read
    as the one law of `Definition.laws` (`laws_eq`), the account's entry "FnLaws owed, open"
    (`entries`), and no law axiom is left unread (`unmatched`). The owed fact holds under every
    interpretation (`fnLaws`, by `hookAssoc_lawAt`: the hook's function is associative).
  - `Sub` (fixture rdr-hook-assoc-sub, the same text with `hook(INT.sub)`): read the same way, with
    the same entry. The owed fact is false under every interpretation (`not_fnLaws`, by
    `intSub_not_lawAt`): the text has no tie.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace KCore.HookAssocLaw

def openEntry : String :=
  "FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here"

theorem anySome {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) : ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- The law axioms no reading takes, as the account lists them. -/
def unmatchedOf (path : String) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => match Parse.parse k with
    | .error r => return [s!"refused: {r.toText}"]
    | .ok d => return (Parse.lawUnmatched k d).map Parse.Refusal.toText

/-- info: [[], []] -/
#guard_msgs in
#eval do
  let a ← unmatchedOf "f2-examples/rdr-hook-assoc.kompile.kore"
  let b ← unmatchedOf "f2-examples/rdr-hook-assoc-sub.kompile.kore"
  IO.println (repr [a, b])

namespace Add

definition_of defn from "f2-examples/rdr-hook-assoc.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def plus : Sym := 384

theorem names : c.symName plus = "Lblplus" := by decide +kernel

/-- The reader's laws of the text: its one law axiom, the associativity of `plus`. -/
theorem laws_eq : defn.laws = [Parse.hookAssocLawOf plus] := by kernel_rfl

theorem entries : defn.laws.map (Parse.fnLawEntry c) = [openEntry] := by decide +kernel

/-- `plus` is a parameter that a hook of `assocIntHooks` implements at Int. -/
theorem param : (c.lookupParam plus).any assocIntHookParam = true := by decide +kernel

private theorem hsh : c.shapesOK = true := by decide +kernel
private theorem hctor : c.isCtor plus = false := by decide +kernel
private theorem hovl : c.isOvl plus = false := by decide +kernel

/-- **The text's law holds at values, under every interpretation**: the `FnLaws` the account lists
as owed. -/
theorem fnLaws (H : HookParams) : FnLaws (cH H) defn.laws := by
  rw [laws_eq]
  intro l hl
  rw [List.mem_singleton] at hl; subst hl
  obtain ⟨k, hk, hk'⟩ := anySome param
  exact hookAssoc_lawAt (c := cH H) hsh hk hk' hctor (by decide) hovl

end Add

namespace Sub

definition_of defn from "f2-examples/rdr-hook-assoc-sub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def minus : Sym := 384

theorem names : c.symName minus = "Lblminus" := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem coreOK_text : c.coreOK = true := by decide_coreOK

/-- The reader's laws of the text: its one law axiom, the associativity of `minus`. -/
theorem laws_eq : defn.laws = [Parse.hookAssocLawOf minus] := by kernel_rfl

theorem entries : defn.laws.map (Parse.fnLawEntry c) = [openEntry] := by decide +kernel

/-- `minus` is a parameter of result sort Int that `INT.sub` implements. -/
theorem param : (c.lookupParam minus).any (fun k => k.impl == some intSub && k.sig.result == Srt.int) = true := by
  decide +kernel

private theorem hctor : c.isCtor minus = false := by decide +kernel
private theorem hovl : c.isOvl minus = false := by decide +kernel

/-- **The text's law is false at values, under every interpretation**: at (1, 1, 1) the left side
is -1 and the right side 1. The `FnLaws` the account lists as owed holds of no interpretation. -/
theorem not_fnLaws (H : HookParams) : ¬ FnLaws (cH H) defn.laws := by
  rw [laws_eq]
  intro h
  obtain ⟨k, hk, hk'⟩ := anySome param
  simp only [Bool.and_eq_true, beq_iff_eq] at hk'
  exact intSub_not_lawAt (c := cH H) hk hk'.1 hk'.2 hctor (by decide) hovl (h _ (List.mem_singleton_self _))

end Sub

end KCore.HookAssocLaw
