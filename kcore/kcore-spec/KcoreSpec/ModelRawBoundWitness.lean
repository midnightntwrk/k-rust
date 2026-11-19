/-
  KCore. A semantics that meets every condition of `coreOK` but the part of `paramsPlain` that asks
  an open generator (a `raw` parameter) to be numbered outside the registry (`nRegSyms ≤` its
  number), and `FnHyp`, whose `Γ` has no model: so `SoundC` fails of it (`not_sound`), and that
  part cannot be left out of `paramsPlain`.

  One own sort S and the nullary open generator `k : → S`, numbered 75, the registry's `#EOF`
  (`regSymNames`), which no module of the semantics declares; no function, rule or collection.
  `Γ` reads the parameter twice. `gens S` lists it (every `raw` parameter of result S is a
  generator of S), and it is no open generator for `isOpenGen`, which asks `lookupOpen`, and
  `lookupOpen` answers for no symbol numbered below `nRegSyms` (the registry's symbols have the
  library's fixed meaning). So `consItemsK` writes its Cons-Fun: `k()` is one element of S.
  `ΓDomains` writes its graph through `paramVal`, which offers the application `k()` itself and
  keeps it only where it is a value of S; `sortOf` reads a constructor term's head through the
  constructors, the overloading symbols and `lookupOpen`, none of which answers for 75, so
  `k()` is no value and the graph is `k() = ⊥`. Numbered `nRegSyms + 5` instead (`c0`), the
  parameter is an open generator, `k()` its own value, and `coreOK` holds (`c0_coreOK`).
  The decidable facts are kernel decisions, each part of `coreOK` on its own.
-/
import KcoreSpec.Sound
import KcoreSpec.CoreDecide
import KcoreSpec.ModelOvlLibCtorWitness

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore

namespace Faithful

namespace RawBoundWitness

open ML

/-- The library: Int and Bool below KItem, `#KConfigValue`. -/
def lib0 : Lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }

def sS : Srt := nRegSorts
/-- The `k` cell's sort (its optional sort `kcS + 1`). -/
def kcS : Srt := nRegSorts + 1
def kl : Sym := nRegSyms + 3
/-- The registry's `#EOF`. -/
def eof : Sym := 75
/-- The open generator's number outside the registry, in `c0`. -/
def own : Sym := nRegSyms + 5

def cellCtors : List CtorSig :=
  [⟨topLabel, [kcS, Srt.counter], Srt.top⟩, ⟨topFragLabel, [kcS + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kl, [Srt.k], kcS⟩, ⟨kl + 1, [], kcS + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(kcS, kcS + 1), (Srt.counter, Srt.counterOpt)]

/-- The open generator `k : → S` numbered `n`, without a registry hook or a law. -/
def kOf (n : Sym) : ParamSig := { sig := ⟨n, [], sS⟩, raw := true }

/-- The open generator numbered 75 where `b` is false, `nRegSyms + 5` (named `Lblk`) where it is
true. -/
def cOf (b : Bool) : Semantics :=
  { lib := lib0
    sortNames := ["S", "KCell", "KCellOpt"]
    symNames := ["LblisS", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] ++
      (if b then ["Lblk"] else [])
    userSorts := [Srt.top, Srt.topFrag, sS, kcS, kcS + 1, Srt.counter, Srt.counterOpt]
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [kOf (if b then own else eof)] }

/-- The witness: the open generator numbered 75. -/
def c : Semantics := cOf false

/-- The open generator numbered outside the registry. -/
def c0 : Semantics := cOf true

/-! ## Every condition of `coreOK` but `paramsPlain`'s raw bound, and `FnHyp` -/

theorem subsortsOK_of (b : Bool) : (cOf b).subsortsOK = true := by cases b <;> decide_cheap
theorem clauses_of (b : Bool) :
    ((cOf b).fns.all fun f => f.clauses.all ((cOf b).clauseSorted f (List.map Fn.sig (cOf b).fns))) = true := by
  cases b <;> rfl
theorem rules_of (b : Bool) : ((cOf b).rules.all (cOf b).ruleSorted) = true := by cases b <;> rfl
theorem rulesPlain_of (b : Bool) : (cOf b).rulesPlain = true := by cases b <;> rfl
theorem clausesPlain_of (b : Bool) : (cOf b).clausesPlain = true := by cases b <;> rfl
theorem shapesOK_of (b : Bool) : (cOf b).shapesOK = true := by cases b <;> decide_cheap
theorem predsApart_of (b : Bool) : (cOf b).predsApart = true := by cases b <;> decide_cheap
theorem idsOK_of (b : Bool) : (cOf b).idsOK = true := by cases b <;> decide_cheap
theorem overloadsOK_of (b : Bool) : (cOf b).overloadsOK = true := by cases b <;> decide_cheap

open Faithful.Model in
theorem names_fast_of (b : Bool) : namesApartFast (cOf b) = true := by cases b <;> decide +kernel

open Faithful.Model in
theorem ites_of (b : Bool) : itesApart (cOf b) = true := by cases b <;> decide_itesApart

set_option maxHeartbeats 1000000 in
open Faithful.Model in
theorem faith_light_of (b : Bool) : (namesNumbered (cOf b) && genWf (cOf b) && collSortsOK (cOf b) &&
    collsOK (cOf b) && patHeadsOK (cOf b) && LitsApart (cOf b) && sortsNumbered (cOf b) &&
    kindsApart (cOf b) && ctorsOnce (cOf b) && fnsApart (cOf b)) = true := by cases b <;> decide_cheap

open Faithful.Model in
theorem faithCoreOK_of (b : Bool) : (cOf b).faithCoreOK = true := by
  have h := faith_light_of b
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  unfold Semantics.faithCoreOK
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, namesApartK_of_fast (names_fast_of b), ites_of b,
    Bool.and_self]

/-- The parameter's shape but its number: no registry hook, no law, no name like an instance of a
sort-parametric symbol, and `shapesOK`; for both numbers. -/
theorem raw_parts_of (b : Bool) : (kOf (if b then own else eof)).impl.isNone = true ∧
    (kOf (if b then own else eof)).assoc = false ∧ (kOf (if b then own else eof)).idem = false ∧
    (instDecode? ((cOf b).symName (kOf (if b then own else eof)).sig.name)).isNone = true ∧
    (cOf b).shapesOK = true := by
  refine ⟨rfl, rfl, rfl, ?_, shapesOK_of b⟩
  cases b <;> decide +kernel

/-- The witness's open generator is numbered below `nRegSyms`. -/
theorem not_rawBound : decide (nRegSyms ≤ (kOf eof).sig.name) = false := by decide +kernel

theorem not_paramsPlain : c.paramsPlain = false := by decide +kernel
theorem not_sortedOK : c.sortedOK = false := by decide +kernel
theorem not_coreOK : c.coreOK = false := by decide +kernel

theorem c0_paramsPlain : (cOf true).paramsPlain = true := by decide +kernel

/-- With the open generator numbered outside the registry, `coreOK` holds. -/
theorem c0_coreOK : c0.coreOK = true := by
  show ((cOf true).sortedOK && (cOf true).faithCoreOK && (cOf true).predsApart &&
    (cOf true).idsOK && (cOf true).overloadsOK) = true
  have hs : (cOf true).sortedOK = true := by
    unfold Semantics.sortedOK
    rw [subsortsOK_of, clauses_of, rules_of, rulesPlain_of, clausesPlain_of, c0_paramsPlain]; rfl
  rw [hs, faithCoreOK_of, predsApart_of, idsOK_of, overloadsOK_of]; rfl

/-- No function, no rule, and an open generator without a law. -/
theorem fnHyp : FnHyp c := by
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined (by decide +kernel), ?_⟩
  · intro fn hfn; exact absurd hfn List.not_mem_nil
  · intro fn hfn; exact absurd hfn List.not_mem_nil
  · intro fn hfn; exact absurd hfn List.not_mem_nil
  · intro fn hfn; exact absurd hfn List.not_mem_nil
  · intro k hk _
    rw [show c.params = [kOf eof] from rfl, List.mem_singleton] at hk
    subst hk
    exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h Bool.false_ne_true⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `paramsPlain`'s raw bound holds (`paramsPlain`'s other parts at
the one parameter), and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    (c.fns.all fun f => f.clauses.all (c.clauseSorted f (List.map Fn.sig c.fns))) = true ∧
    (c.rules.all c.ruleSorted) = true ∧ c.rulesPlain = true ∧ c.clausesPlain = true ∧
    ((kOf eof).impl.isNone = true ∧ (kOf eof).assoc = false ∧ (kOf eof).idem = false ∧
      (instDecode? (c.symName (kOf eof).sig.name)).isNone = true ∧ c.shapesOK = true) ∧
    c.faithCoreOK = true ∧ c.predsApart = true ∧
    c.idsOK = true ∧ c.overloadsOK = true ∧ FnHyp c :=
  ⟨subsortsOK_of false, clauses_of false, rules_of false, rulesPlain_of false, clausesPlain_of false,
    raw_parts_of false, faithCoreOK_of false, predsApart_of false,
    idsOK_of false, overloadsOK_of false, fnHyp⟩

/-! ## `Γ c` has no model -/

def kSig : CtorSig := ⟨eof, [], sS⟩

theorem s_cons : sS ∈ consSorts c := by decide +kernel
/-- The open generator is S's one generator, and `isOpenGen` does not answer for it. -/
theorem gens_eq : (c.gens sS).filter (!c.isOpenGen ·) = [Gen.ctor kSig] := rfl
theorem gen_mem : Gen.ctor kSig ∈ (c.gens sS).filter (!c.isOpenGen ·) := gens_eq ▸ List.mem_singleton_self _
theorem gen_not_fnOvl : c.fnOvl (.ctor kSig) = false := by decide +kernel
theorem k_mem : kOf eof ∈ c.params := List.mem_singleton_self _
theorem sorts_nil : c.sortsOf [] = some (kOf eof).sig.args := rfl
/-- `k()` is no value, so the parameter's graph is empty there. -/
theorem paramVal_nil : c.paramVal eof [] = none := by decide +kernel
theorem inst_none : instDecode? (c.symName eof) = none := by decide +kernel

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem koreList_trW : ∀ ws : List GroundTerm, (GroundTerm.koreList c ws).map (KoreAML.tr ⟨[], []⟩) = ws.map (den c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | w :: ws => by rw [GroundTerm.koreList, List.map_cons, List.map_cons, koreList_trW ws]; rfl

theorem elems_all2W (hI : I ⊧ᴵP Γ c) (e : Valuation M) : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) (ws.map (den c)) (ws.map (elemOf c I))
  | [], _, _ => .nil
  | w :: ws, ss, h => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact .cons (elemOf_spec hI h1 e).1 (elems_all2W hI e h2)

/-- The element of an application of a symbol with the signature `k` is the one `k`'s generator
builds from its arguments' elements. -/
theorem den_sig_gsW (hI : I ⊧ᴵP Γ c) {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hn : k.name = f)
    (hws : c.sortsOf ws = some k.args) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_trW, interp_appList_sing _ _ _ (elems_all2W hI e hws)]
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

end

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  -- `k()` is one element of S, by its Cons-Fun
  obtain ⟨y, -, hye⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem s_cons gen_mem gen_not_fnOvl, rfl⟩))
    (xs := []) rfl (fun _ _ _ h _ => by simp at h)
  have hy : GS I (c.sortName sS) (Gen.toK c (.ctor kSig)) [] y := (hye y).mpr rfl
  -- the parameter's graph: `k() = ⊥`
  have hax := sat_dom hI (Or.inr (Or.inl ⟨kOf eof, [], k_mem, sorts_nil, rfl⟩))
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default) y
  have hsa : KoreAML.den (symApp c (kOf eof).sig.name (GroundTerm.koreList c [])) = den c (.ctor eof []) := by
    rw [show (kOf eof).sig.name = eof from rfl, symApp_noInst inst_none]; rfl
  rw [hsa, show (kOf eof).sig.name = eof from rfl, paramVal_nil] at hgr
  exact absurd (hgr.mp ((den_sig_gsW hI (k := kSig) rfl rfl KoreAML.val0 y).mpr hy)) (by simp [Pattern.interpret])

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `paramsPlain`'s raw
bound, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end RawBoundWitness

end Faithful

end KCore
