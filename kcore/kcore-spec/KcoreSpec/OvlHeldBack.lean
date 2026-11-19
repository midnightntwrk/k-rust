/-
  KCore. The held symbols at a value, for a semantics `coreOK` accepts. The statements over the
  facts a proof reads are in HeldBackCl.lean; here `coreOK` gives those facts.

  - `ovlHeld_back`: an application of an `ovlHeld` symbol that is a value's element has values'
    elements as arguments (`ovlHeld_backCl`), where `hrc` (the definition reads a confined sort
    where the symbol's closure holds a function) gives what `confinedAt_value` concludes.
  - `heldBackAll_collOvl`: the `collHeld` and the `ovlHeld` symbols have `HeldBack` in every model
    of `Γc`. With K's `append` (`appendHeld_backX`) they are the symbols `Semantics.holds` names:
    `heldBackAll_holds`, `backO_of_core` (through `heldBack_holdsCl`).
  - `Semantics.heldFacts_of_core`: what `coreOK` alone gives the statements over a set of held
    symbols, some set with the rules' facts and `HeldBackAll`.
  - `heldOccsO_witnessed`: the variables a term holds (`heldOccs`), at a value.
-/
import KcoreSpec.HeldBackAll
import KcoreSpec.HeldBackCl

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

section OvlHeldBack
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An `ovlHeld` symbol at a value**: in a model of `Γc`, an application of an `ovlHeld` symbol
that is a value's element has values' elements as arguments. `hrc`: the definition reads a
confined sort where the symbol's overload closure holds a function. -/
theorem ovlHeld_back (h : c.coreOK = true) {f : Sym}
    (hrc : (c.fnOverloads f).isEmpty = false → c.readsConfined = true)
    (hI : I ⊧ᴵP Γc c) {o : OvlSig} (hlo : c.lookupOvl f = some o) (hh : c.ovlHeld f = true)
    {w : GroundTerm} (hw : c.sortOf w = some o.sig.result) {bs : List M}
    (hbl : bs.length = (o.sig.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (o.sig.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some o.sig.args ∧ bs = ws.map (elemOf c I) := by
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  exact ovlHeld_backCl (fun φ hφ => hI φ (Or.inl hφ)) hg hsc.trans
    (fun hne => confinedAt_value h (hrc hne) hI) hlo hh hw hbl hbs hm

end OvlHeldBack

/-- **The `collHeld` and the `ovlHeld` symbols have `HeldBack` in every model of `Γc`.** `hrc`: the
definition reads a confined sort where an overload closure holds a function. -/
theorem heldBackAll_collOvl {c : Semantics} (h : c.coreOK = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true) :
    HeldBackAll c (fun f => collHeld c f || c.ovlHeld f) := by
  intro M _ I hI f k hc hh hk
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  exact heldBack_collOvlCl (fun φ hφ => hI φ (Or.inl hφ)) (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)) hg hph hcs
    hcso (fun hany => confinedAt_value h (hrc hany) hI) f k hc hh hk

/-- **The symbols `Semantics.holds` names have `HeldBack` in every model of `Γc`.** `hrc`: the
definition reads a confined sort where an overload closure holds a function. -/
theorem heldBackAll_holds {c : Semantics} (h : c.coreOK = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true) :
    HeldBackAll c c.holds := by
  intro M _ I hI f k hc hh hk
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  exact heldBack_holdsCl (fun φ hφ => hI φ (Or.inl hφ)) (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)) hnn hg
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.1)
    (fun k hk hkr => Semantics.raw_noInst_core_irs h hk hkr) hph hcs hcso
    (fun hany => confinedAt_value h (hrc hany) hI) f k hc hh hk

/-- **Each symbol `Semantics.holds` names has `HeldBack`** in a model of `Γc`. `hrc`: the
definition reads a confined sort where an overload closure holds a function. -/
theorem backO_of_core {c : Semantics} (h : c.coreOK = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c) :
    ∀ f k, c.isCtor f = false → c.holds f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k :=
  heldBackAll_holds h hrc I hI

/-- **What `coreOK` gives the statements over a set of held symbols**: some set at which the rules
have `ruleSorted` and `rulePlainHeldH` and whose symbols have `HeldBack` in every model of `Γc`.
It is the symbols `Semantics.holds` names where the definition reads a confined sort, and no
symbol where it reads none. -/
theorem Semantics.heldFacts_of_core {c : Semantics} (h : c.coreOK = true) :
    ∃ H : Sym → Bool, (∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) ∧
      HeldBackAll c H :=
  heldFacts_of_rules (Semantics.ruleFactsHeld_of_core h) fun hr => heldBackAll_holds h fun _ => hr

/-- **A term's held variables, at a value.** In a model of `Γc`, if the element of a value of a
well-sorted term's sort lies in its translation, at a valuation of its variables in their sorts,
the valuation gives each variable the term holds (`heldOccs`: under constructors, injections and
the symbols `Semantics.holds` names) the element of a value of its sort. `hrc`: the definition
reads a confined sort where an overload closure holds a function. -/
theorem heldOccsO_witnessed {c : Semantics} (h : c.coreOK = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c)
    {vars : List Srt} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c vars) i))))
    {t : Term} {s : Srt} {w : GroundTerm}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s) (hw : c.sortOf w = some s)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e (elemOf c I w)) :
    ∀ i ∈ heldOccs c t, Witnessed c I tbl (canonVars c vars) vars e i := by
  obtain ⟨hok, hsr, hnn, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro i hi
  rw [heldOccs_eq] at hi
  exact occsUnder_witnessed (fun φ hφ => hI φ (Or.inl hφ)) hg hsc.trans hnn.1 (canonVars_length c vars) hin
    fns_headsOK (backO_of_core h hrc hI) ht hw hm i hi

end KCore
