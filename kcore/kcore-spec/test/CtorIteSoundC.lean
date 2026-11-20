/-
  The first part of `namesNumbered` (no constructor is named like an instance of a sort-parametric
  symbol) is needed for soundness. Run from the package root:
  `lake env lean -j1 test/CtorIteSoundC.lean`.

  `c` has one constructor named like an instance, `Lblite{KCell} : Int → KCell`, and one rule,
  `<k> .K </k> <generatedCounter> 0 </generatedCounter> => Lblite{KCell}(1) <generatedCounter> 0 </generatedCounter>`.
  Kernel-checked here:
  - `meets_others`, `not_namesNumbered`: every condition of `coreOK` but `namesNumbered` holds
    (`itesApart` among them), and `FnHyp`; `namesNumbered` fails.
  - `step`: the rule gives the step from `<k> .K </k>` to the value `Lblite{KCell}(1)` in the top cell.
  - `consistent`: `Γc c` with the step's closure has a model.
  - `not_sound`: `SoundC c` fails. Its second conjunct asks `Γc c ⊧ (den y ⇒ famEx c r σ)`.
    `den y` applies the constructor under its own name, as a value and the constructor items write
    it (`GroundTerm.kore`, `toK`); `famEx` applies it as `Term.kore` writes it, the head `Lblite` at
    the sort `SortKCell`, and `Γc c` relates the two heads nowhere.
  The model `I`: `c2` is `c` with the constructor named `Lblfoo` and no rule. `c2` meets `coreOK` and
  `FnHyp`, so its value model `stdI c2` is a model of its theory (`model2`). `I` is `stdI c2` reading
  the name `Lblite{KCell}` as `Lblfoo` (`interp_ren`). Every axiom of `Γc c` but two is, under
  that renaming, an axiom of `Γc c2`: the items of the signature, the constructors, the functions
  and the collections are the same lists (kernel decisions: `sig_align`, `cons_align`, `fn_align`,
  `coll_align`), and the graphs of `ΓDomains` and `ΓFallback` are written through `den`, which the
  renaming maps from `c` to `c2` (`ren_den`); the fallback of a function holds of no value, since
  every sort predicate has a clause that matches every K (`not_allFail`). The two others are the
  constructor's arity item (`arity_sat`) and the rule's axiom (`satI_rule`), both about the head
  `Lblite` at `SortKCell`. In `stdI c2` no symbol is named as an instance, so `Lblite` applied to a
  sort and an argument denotes nothing (`iteApp_empty`); the arity item holds, the rule's premise
  `⌈rhs⌉` is empty, and `famEx` is empty (`famEx_empty`), while `den y` denotes an element.
  `I` has no step (`c2` has no rule), so the closure holds in it (`step_sat`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.CtorIteSoundC

open ML Model

/-! ## The definitions -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The constructor `Int → KCell`. -/
def fSig : CtorSig := ⟨nRegSyms + 4, [Srt.int], nRegSorts⟩

/-- The constructor under the plain name `Lblfoo`, and no rule. -/
def c2 : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblfoo"]
    userSorts := cellSorts
    ctors := cellCtors ++ [fSig]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- `<k> t </k> <generatedCounter> 0 </generatedCounter>`. -/
def cfg (t : Term) : Term :=
  .app topLabel [.app (nRegSyms + 2) [t], .app counterLabel [.dv Srt.int (.int 0)]]

/-- `<k> .K </k> … => Lblite{KCell}(1) …`. -/
def r : Rule :=
  { vars := [], lhs := cfg (.app dotk []), req := none,
    rhs := .app topLabel [.app fSig.name [.dv Srt.int (.int 1)], .app counterLabel [.dv Srt.int (.int 0)]],
    ens := none, prio := 50 }

/-- The constructor named `Lblite{KCell}`, and the rule. -/
def c : Semantics :=
  { c2 with symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblite{KCell}"],
            rules := [r] }

/-! ## The conditions -/

theorem sortedOK : c.sortedOK = true := by decide_cheap
theorem clausesPreTopC : c.clausesPreTop = true := by decide +kernel
theorem readsConfined : c.readsConfined = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined readsConfined, openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 2000000 in
/-- Every condition of `coreOK` but `namesNumbered` holds, `itesApart` among them, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧
    genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.collsNotCtors c = true ∧ Model.kindsApart c = true ∧
    Model.ctorsOnce c = true ∧ Model.fnsApart c = true ∧ Model.itesApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, fnHyp⟩

theorem ite_f : instDecode? (c.symName fSig.name) = some ("Lblite", ["KCell"]) := by decide +kernel

/-- `namesNumbered` fails: the constructor is named like `ite` at `KCell`. -/
theorem not_namesNumbered : namesNumbered c = false := by decide +kernel

theorem not_faithCoreOK : c.faithCoreOK = false := by decide +kernel

theorem c2_core : c2.coreOK = true := by decide_cheap
theorem c2_sortedOK : c2.sortedOK = true := by decide_cheap

theorem c2_fnHyp : FnHyp c2 :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

/-- The value model of `c2` is a model of its theory. -/
theorem model2 : stdI c2 ⊧ᴵP (Γc c2 ∪ Γstep c2) :=
  stdI_modelOpen c2 c2_core
    (hypModel_of_fn c2_core (fnModel_of_fnHyp c2_core c2_fnHyp).1 (fnModel_of_fnHyp c2_core c2_fnHyp).2)
    c2_fnHyp.2.2.2.2.2 (fun _ h => absurd h List.not_mem_nil)
    (satFnsGoal_decided
      (hypModel_of_fn c2_core (fnModel_of_fnHyp c2_core c2_fnHyp).1 (fnModel_of_fnHyp c2_core c2_fnHyp).2)
      (Semantics.fnsNoExs_of_all (by decide +kernel)) (clausePreDecided_of_fnHyp c2_core c2_fnHyp))

theorem inΓ2 {φ : KoreAML.P} (h : φ ∈ Γ c2) : stdI c2 ⊧ᴵ φ := model2 φ (Or.inl (Or.inl h))

/-! ## Renaming `Lblite{KCell}` to `Lblfoo` -/

def ρn (n : String) : String := if n = "Lblite{KCell}" then "Lblfoo" else n

def ρ : KoreAML.Sym → KoreAML.Sym
  | .symbol n => .symbol (ρn n)
  | s => s

def ren : KoreAML.P → KoreAML.P
  | .evar x => .evar x
  | .svar X => .svar X
  | .bottom => .bottom
  | .symbol s => .symbol (ρ s)
  | .application a b => .application (ren a) (ren b)
  | .implication a b => .implication (ren a) (ren b)
  | .existential x a => .existential x (ren a)
  | .mu X a => .mu X (ren a)

/-- `c2`'s value model, reading the name `Lblite{KCell}` as `Lblfoo`. -/
def I : Interpretation KoreAML.Sym Elem := ⟨fun s => evalSymb c2 (ρ s), evalApp_T c2 (StepM c2)⟩

theorem interp_ren : ∀ (φ : KoreAML.P) (e : Valuation Elem), φ.interpret I e = (ren φ).interpret (stdI c2) e
  | .evar _, _ => rfl
  | .svar _, _ => rfl
  | .bottom, _ => rfl
  | .symbol _, _ => rfl
  | .application a b, e => by
      funext m; simp only [ren, Pattern.interpret, interp_ren a e, interp_ren b e]; rfl
  | .implication a b, e => by
      funext m; simp only [ren, Pattern.interpret, interp_ren a e, interp_ren b e]
  | .existential x a, e => by
      funext m; simp only [ren, Pattern.interpret, interp_ren a]
  | .mu X a, e => by
      funext m; simp only [ren, Pattern.interpret, interp_ren a]

theorem sat_of_ren {φ : KoreAML.P} (h : stdI c2 ⊧ᴵ ren φ) : I ⊧ᴵ φ := fun e m => by
  rw [interp_ren]; exact h e m

/-! ## What the renaming does to names and values -/

theorem reg_not_ite : regSymNames.all (· != "Lblite{KCell}") = true := by decide +kernel

theorem regName_ne (f : Nat) : regSymNames.getD f "" ≠ "Lblite{KCell}" := by
  rw [List.getD_eq_getElem?_getD]
  cases h : regSymNames[f]? with
  | none => simp
  | some x =>
    have hx := List.mem_of_getElem? h
    have := List.all_eq_true.mp reg_not_ite x hx
    simpa using this

theorem ρn_symName (f : Sym) : ρn (c.symName f) = c2.symName f := by
  unfold Semantics.symName
  by_cases h : f < nRegSyms
  · simp only [h, ite_true, ρn, regName_ne, ite_false]
  · simp only [h, ite_false]
    generalize f - nRegSyms = i
    rcases i with _ | _ | _ | _ | _ | i <;> simp [c, c2, ρn]

theorem ren_sym (f : Sym) : ren (KoreAML.sym (.symbol (c.symName f))) = KoreAML.sym (.symbol (c2.symName f)) := by
  show ML.Pattern.symbol (KoreAML.Sym.symbol (ρn (c.symName f))) = _
  rw [ρn_symName]; rfl

mutual
theorem sortOf_eq : ∀ v : GroundTerm, c.sortOf v = c2.sortOf v
  | .ctor f ts => by rw [Semantics.sortOf, Semantics.sortOf, sortsOf_eq ts]; rfl
  | .inj a b t => by rw [Semantics.sortOf, Semantics.sortOf, sortOf_eq t]; rfl
  | .dv s lit => by rw [Semantics.sortOf, Semantics.sortOf]; rfl
  | .map s es => by simp only [Semantics.sortOf, entriesOK_eq _ _ es]; rfl
  | .set s es => by rw [Semantics.sortOf, Semantics.sortOf, sortsOf_eq es]; rfl
  | .list s es => by rw [Semantics.sortOf, Semantics.sortOf, sortsOf_eq es]; rfl
theorem sortsOf_eq : ∀ ts : List GroundTerm, c.sortsOf ts = c2.sortsOf ts
  | [] => by rw [Semantics.sortsOf, Semantics.sortsOf]
  | t :: ts => by rw [Semantics.sortsOf, Semantics.sortsOf, sortOf_eq t, sortsOf_eq ts]
theorem entriesOK_eq (ks vs : Srt) : ∀ es : List (GroundTerm × GroundTerm), c.entriesOK ks vs es = c2.entriesOK ks vs es
  | [] => by rw [Semantics.entriesOK, Semantics.entriesOK]
  | e :: es => by rw [Semantics.entriesOK, Semantics.entriesOK, entryOK_eq ks vs e, entriesOK_eq ks vs es]
theorem entryOK_eq (ks vs : Srt) : ∀ e : GroundTerm × GroundTerm, c.entryOK ks vs e = c2.entryOK ks vs e
  | (k, v) => by rw [Semantics.entryOK, Semantics.entryOK, sortOf_eq k, sortOf_eq v]
end

abbrev ctx0 : KoreAML.Ctx := ⟨[], []⟩

mutual
theorem ren_kore : ∀ v : GroundTerm, ren (KoreAML.tr ctx0 (v.kore c)) = KoreAML.tr ctx0 (v.kore c2)
  | .ctor f ts => by
      rw [GroundTerm.kore, GroundTerm.kore, KoreAML.tr_app0, KoreAML.tr_app0]
      exact ren_trArgs ts _ _ (ren_sym f)
  | .inj a b t => by
      rw [GroundTerm.kore, GroundTerm.kore, KoreAML.tr_injP, KoreAML.tr_injP]
      simp only [KoreAML.appList, KoreAML.Cons.sortP, KoreAML.sym]
      rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl, ren_kore t]; rfl
  | .dv s lit => by
      rw [GroundTerm.kore, GroundTerm.kore, KoreAML.tr_dv, KoreAML.tr_dv]; rfl
  | .map s es => by
      rw [GroundTerm.kore, GroundTerm.kore]; exact ren_entries _ es
  | .set s es => by
      rw [GroundTerm.kore, GroundTerm.kore]; exact ren_elems _ es
  | .list s es => by
      rw [GroundTerm.kore, GroundTerm.kore]; exact ren_elems _ es
theorem ren_trArgs : ∀ (ts : List GroundTerm) (acc acc' : KoreAML.P), ren acc = acc' →
    ren (KoreAML.trArgs ctx0 acc (GroundTerm.koreList c ts)) = KoreAML.trArgs ctx0 acc' (GroundTerm.koreList c2 ts)
  | [], _, _, h => by rw [GroundTerm.koreList, GroundTerm.koreList, KoreAML.trArgs, KoreAML.trArgs]; exact h
  | t :: ts, acc, acc', h => by
      rw [GroundTerm.koreList, GroundTerm.koreList, KoreAML.trArgs, KoreAML.trArgs]
      exact ren_trArgs ts _ _ (by
        rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl, h, ren_kore t])
theorem ren_entries (k : CollSig) : ∀ es : List (GroundTerm × GroundTerm),
    ren (KoreAML.tr ctx0 (GroundTerm.koreEntries c k es)) = KoreAML.tr ctx0 (GroundTerm.koreEntries c2 k es)
  | [] => by
      rw [GroundTerm.koreEntries, GroundTerm.koreEntries]; unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0, KoreAML.trArgs, KoreAML.trArgs]; exact ren_sym _
  | [e] => by rw [GroundTerm.koreEntries, GroundTerm.koreEntries]; exact ren_entry k e
  | e :: e' :: es => by
      rw [show GroundTerm.koreEntries c k (e :: e' :: es) = KoreAML.ap (c.symName k.concat)
            [GroundTerm.koreEntry c k e, GroundTerm.koreEntries c k (e' :: es)] from rfl,
        show GroundTerm.koreEntries c2 k (e :: e' :: es) = KoreAML.ap (c2.symName k.concat)
            [GroundTerm.koreEntry c2 k e, GroundTerm.koreEntries c2 k (e' :: es)] from rfl]
      unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0]
      simp only [KoreAML.trArgs]
      rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        ren_sym, ren_entry k e, ren_entries k (e' :: es)]
theorem ren_entry (k : CollSig) : ∀ e : GroundTerm × GroundTerm,
    ren (KoreAML.tr ctx0 (GroundTerm.koreEntry c k e)) = KoreAML.tr ctx0 (GroundTerm.koreEntry c2 k e)
  | (x, v) => by
      rw [GroundTerm.koreEntry, GroundTerm.koreEntry]; unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0]
      simp only [KoreAML.trArgs]
      rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        ren_sym, ren_kore x, ren_kore v]
theorem ren_elems (k : CollSig) : ∀ es : List GroundTerm,
    ren (KoreAML.tr ctx0 (GroundTerm.koreElems c k es)) = KoreAML.tr ctx0 (GroundTerm.koreElems c2 k es)
  | [] => by
      rw [GroundTerm.koreElems, GroundTerm.koreElems]; unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0, KoreAML.trArgs, KoreAML.trArgs]; exact ren_sym _
  | [e] => by
      rw [GroundTerm.koreElems, GroundTerm.koreElems]; unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0]
      simp only [KoreAML.trArgs]
      rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl, ren_sym, ren_kore e]
  | e :: e' :: es => by
      rw [show GroundTerm.koreElems c k (e :: e' :: es) = KoreAML.ap (c.symName k.concat)
            [KoreAML.ap (c.symName k.elem) [GroundTerm.kore c e], GroundTerm.koreElems c k (e' :: es)] from rfl,
        show GroundTerm.koreElems c2 k (e :: e' :: es) = KoreAML.ap (c2.symName k.concat)
            [KoreAML.ap (c2.symName k.elem) [GroundTerm.kore c2 e], GroundTerm.koreElems c2 k (e' :: es)] from rfl]
      unfold KoreAML.ap
      rw [KoreAML.tr_app0, KoreAML.tr_app0]
      simp only [KoreAML.trArgs]
      rw [KoreAML.tr_app0, KoreAML.tr_app0]
      simp only [KoreAML.trArgs]
      rw [show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        show ∀ p q : KoreAML.P, ren (p ⬝ q) = ren p ⬝ ren q from fun _ _ => rfl,
        ren_sym, ren_sym, ren_kore e, ren_elems k (e' :: es)]
end

theorem ren_den (v : GroundTerm) : ren (den c v) = den c2 v := ren_kore v

/-! ## `Lblite` applied to `SortKCell` and an argument denotes nothing -/

/-- No name of `c2` has a code holding `{`. -/
theorem instIdx2 : instIdx (symCodesCD c2) = [] := by rw [instIdx_symCodesCD]; decide +kernel

/-- No symbol of `c2` is an instance at the head `Lblite`. -/
theorem noInst2 : ∀ k ∈ kernelSyms c2, ∀ xs, instDecode? (c2.symName k.name) ≠ some ("Lblite", xs) := by
  intro k _ xs he
  have hm := mem_instIdx (symCodesCD_eq c2) (f := k.name) (by rw [he]; exact Option.some_ne_none _)
  rw [instIdx2] at hm
  exact List.not_mem_nil hm

theorem resolve_ite2 (s : Srt) (tail : List Elem) : resolve c2 "Lblite" (.srt s :: tail) = none :=
  resolve_lblite_noInst noInst2 s tail

theorem names2 : namesApartK c2 = true := by decide_cheap

theorem symAt_one {u x : Elem} (hr : resolve c2 "Lblite" [u] = none) (h : symAt c2 "Lblite" [u] x) :
    x = .app (.sym "Lblite") [u] :=
  symAt_none_app hr h

theorem symAt_two {u w x : Elem} (hr : resolve c2 "Lblite" [u, w] = none) : ¬ symAt c2 "Lblite" [u, w] x :=
  symAt_none_noInst hr noInst2 (by simp) x

theorem I_app_sym (n : String) (args : List Elem) (b x : Elem) :
    I.evalApp (.app (.sym n) args) b x ↔ symAt c2 n (args ++ [b]) x := Iff.rfl

theorem ρ_lblite : ρ (.symbol "Lblite") = .symbol "Lblite" := by
  show KoreAML.Sym.symbol (ρn "Lblite") = _
  rw [show ρn "Lblite" = "Lblite" by unfold ρn; rw [ite_eq_right_iff.mpr (by decide)]]

theorem I_lblite (x : Elem) : I.evalSymb (.symbol "Lblite") x ↔ x = .app (.sym "Lblite") [] := by
  show evalSymb c2 (ρ (.symbol "Lblite")) x ↔ _
  rw [ρ_lblite]
  exact evalSymb_lblite (namesApartK_spec names2) x

theorem I_sortK (x : Elem) (h : I.evalSymb (.sort "SortKCell") x) : ∃ s, x = .srt s := by
  obtain ⟨s, -, hs⟩ := h
  exact ⟨s, hs⟩

section
attribute [local irreducible] symAt resolve evalSymb

theorem iteApp_empty (e : Valuation Elem) (ψ : KoreAML.P) (m : Elem) :
    ¬ ((KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort "SortKCell")) ⬝ ψ).interpret I e m := by
  rintro ⟨a, b, ⟨a1, a2, h1, h2, h3⟩, -, hab⟩
  change I.evalSymb (.symbol "Lblite") a1 at h1
  rw [I_lblite] at h1
  change I.evalSymb (.sort "SortKCell") a2 at h2
  obtain ⟨s, rfl⟩ := I_sortK a2 h2
  subst h1
  rw [I_app_sym, List.nil_append] at h3
  have h3' := symAt_one (u := .srt s) (x := a) (resolve_ite2 s []) h3
  subst h3'
  rw [I_app_sym, List.cons_append, List.nil_append] at hab
  exact symAt_two (u := .srt s) (w := b) (x := m) (resolve_ite2 s [b]) hab

end

theorem defI : KoreAML.DefOK I :=
  KoreAML.defOK_of fun x => sat_of_ren
    (inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))))))))

/-! ## The signature -/

theorem arity_eq : (symArityItem c fSig).pat =
    (((KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort "SortKCell")) ⬝ KoreAML.inhOf (sortP "Int")) ⊆⊆
      KoreAML.inhOf (sortP "KCell")) := rfl

theorem arity_sat : I ⊧ᴵ (symArityItem c fSig).pat := by
  rw [arity_eq]; intro e m
  unfold included
  rw [KoreAML.interp_total defI]
  intro a ha
  exact absurd ha (iteApp_empty e _ a)

set_option maxHeartbeats 1000000 in
theorem sig_align : (sigItems c).map (fun it => if it.pat = (symArityItem c fSig).pat then (symArityItem c2 fSig).pat
    else ren it.pat) = (sigItems c2).map (·.pat) := by
  decide_map_blocks 25 20

theorem satI_sig {φ : KoreAML.P} (h : ΓSig c φ) : I ⊧ᴵ φ := by
  rcases h with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
  · by_cases hp : it.pat = (symArityItem c fSig).pat
    · rw [hp]; exact arity_sat
    · apply sat_of_ren
      have hm : ren it.pat ∈ (sigItems c2).map (·.pat) := by
        rw [← sig_align]; exact List.mem_map.mpr ⟨it, hit, by simp [hp]⟩
      obtain ⟨it2, hit2, he⟩ := List.mem_map.mp hm
      exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨it2, hit2, he⟩))))))))
  · exact sat_of_ren (inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))))))))
  · exact sat_of_ren (inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨lit, rfl⟩))))))))

/-! ## The constructors, the collections, the functions -/

theorem cons_align : (consItemsK c).map (fun it => ren it.pat) = (consItemsK c2).map (·.pat) := by
  decide +kernel

theorem satI_cons {φ : KoreAML.P} (h : ΓCons c φ) : I ⊧ᴵ φ := by
  apply sat_of_ren
  rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · have hm : ren it.pat ∈ (consItemsK c2).map (·.pat) := by
      rw [← cons_align]; exact List.mem_map.mpr ⟨it, hit, rfl⟩
    obtain ⟨it2, hit2, he⟩ := List.mem_map.mp hm
    exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨it2, hit2, he⟩)))))))
  · exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩)))))))

theorem fn_align : (fnItems c).map (fun it => ren it.pat) = (fnItems c2).map (·.pat) := by
  decide +kernel

theorem satI_fns {φ : KoreAML.P} (h : ΓFns c φ) : I ⊧ᴵ φ := by
  apply sat_of_ren
  rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · have hm : ren it.pat ∈ (fnItems c2).map (·.pat) := by
      rw [← fn_align]; exact List.mem_map.mpr ⟨it, hit, rfl⟩
    obtain ⟨it2, hit2, he⟩ := List.mem_map.mp hm
    exact inΓ2 (Or.inl (Or.inl (Or.inr (Or.inl ⟨it2, hit2, he⟩))))
  · exact inΓ2 (Or.inl (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩))))

theorem coll_align : c.allColls.all (fun k => (collAxioms c k).map ren == collAxioms c2 k &&
    ren (collNoJunk c k) == collNoJunk c2 k) = true := by
  decide +kernel

theorem coll_eqs {k : CollSig} (hk : k ∈ c.allColls) :
    (collAxioms c k).map ren = collAxioms c2 k ∧ ren (collNoJunk c k) = collNoJunk c2 k := by
  have := List.all_eq_true.mp coll_align k hk
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem satI_colls {φ : KoreAML.P} (h : ΓColls c φ) : I ⊧ᴵ φ := by
  obtain ⟨k, hk, hφ⟩ := h
  apply sat_of_ren
  have hm : ren φ ∈ collAxioms c2 k := by rw [← (coll_eqs hk).1]; exact List.mem_map.mpr ⟨φ, hφ, rfl⟩
  exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, hm⟩))))

/-! ## The domains and the fallback -/

theorem hooks_dec : hookSigs.all (fun k => decide (k.name < nRegSyms) &&
    (instDecode? (regSymNames.getD k.name "")).isNone) = true := by
  decide_cheap 20

theorem hook_names {k : CtorSig} (hk : k ∈ hookSigs) :
    instDecode? (c.symName k.name) = none ∧ instDecode? (c2.symName k.name) = none := by
  have h := List.all_eq_true.mp hooks_dec k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  simp only [Semantics.symName, h.1, ite_true]
  exact ⟨h.2, h.2⟩

theorem ren_symApp {f : Sym} (hf : instDecode? (c.symName f) = none) (hf2 : instDecode? (c2.symName f) = none)
    (vs : List GroundTerm) :
    ren (KoreAML.den (symApp c f (GroundTerm.koreList c vs))) = KoreAML.den (symApp c2 f (GroundTerm.koreList c2 vs)) := by
  rw [symApp_noInst hf, symApp_noInst hf2]
  unfold KoreAML.den
  rw [KoreAML.tr_app0, KoreAML.tr_app0]
  exact ren_trArgs vs _ _ (ren_sym f)

theorem ren_equal (φ ψ : KoreAML.P) : ren (φ ≡ ψ) = (ren φ ≡ ren ψ) := rfl

theorem ren_hookGraph {f : Sym} (hf : instDecode? (c.symName f) = none) (hf2 : instDecode? (c2.symName f) = none)
    (vs : List GroundTerm) (B B' : KoreAML.P) (hB : ren B = B') :
    ren (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ B) =
      (KoreAML.den (symApp c2 f (GroundTerm.koreList c2 vs)) ≡ B') := by
  rw [ren_equal, ren_symApp hf hf2, hB]

theorem satI_dom {φ : KoreAML.P} (h : ΓDomains c φ) : I ⊧ᴵ φ := by
  apply sat_of_ren
  rcases h with ⟨k, vs, rr, hk, hs, hh, hsil, rfl⟩ | ⟨k, vs, hk, -⟩ | ⟨v, s, hs, rfl⟩ | ⟨v, w, s, hd, hv, hw, hcmp, rfl⟩ |
      ⟨k, hk, rfl⟩
  · have hs' : c2.sortsOf vs = some k.args := by rw [← sortsOf_eq]; exact hs
    rcases rr with _ | v
    · show stdI c2 ⊧ᴵ ren (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ ⊥)
      rw [ren_hookGraph (hook_names hk).1 (hook_names hk).2 vs ⊥ ⊥ rfl]
      exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hs', hh, hsil, rfl⟩))))))
    · show stdI c2 ⊧ᴵ ren (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ den c v)
      rw [ren_hookGraph (hook_names hk).1 (hook_names hk).2 vs _ _ (ren_den v)]
      exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hs', hh, hsil, rfl⟩))))))
  · exact absurd hk List.not_mem_nil
  · rw [show ren (KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩)) =
        KoreAML.sExists ⟨1⟩ (sortP (c2.sortName s)) (ren (den c v) ≡ .evar ⟨1⟩) from rfl, ren_den]
    exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, by rw [← sortOf_eq]; exact hs, rfl⟩))))))))
  · rw [show ren (∼(den c v ⋀ den c w)) = ∼(ren (den c v) ⋀ ren (den c w)) from rfl, ren_den, ren_den]
    exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨v, w, s, hd, by rw [← sortOf_eq]; exact hv, by rw [← sortOf_eq]; exact hw, hcmp, rfl⟩)))))))))
  · rw [(coll_eqs hk).2]
    exact inΓ2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))))))))

def isVar0 : List Term → Bool
  | [.var 0] => true
  | _ => false

theorem isVar0_spec {ps : List Term} (h : isVar0 ps = true) : ps = [.var 0] := by
  unfold isVar0 at h; split at h <;> first | rfl | cases h

theorem sortsOf_single {d : Semantics} {vs : List GroundTerm} {s : Srt} (h : d.sortsOf vs = some [s]) :
    ∃ v, vs = [v] ∧ d.sortOf v = some s := by
  match vs, h with
  | [], h => rw [Semantics.sortsOf] at h; cases h
  | v :: ws, h =>
    rw [Semantics.sortsOf] at h
    cases hv : d.sortOf v with
    | none => simp only [hv] at h; cases h
    | some s' =>
      cases hw : d.sortsOf ws with
      | none => simp only [hv, hw] at h; cases h
      | some ss =>
        simp only [hv, hw, Option.some.injEq, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hws : ws = [] := by
          match ws, hw with
          | [], _ => rfl
          | w :: ws', hw => rw [Semantics.sortsOf] at hw; split at hw <;> simp at hw
        exact ⟨v, by rw [hws], hv⟩

theorem preds_var : c.allFns.all (fun fn => fn.args == [Srt.k] && fn.clauses.any (fun cl => cl.req.isNone &&
    cl.vars == [Srt.k] && isVar0 cl.pats)) = true := by
  decide +kernel

theorem not_allFail {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm} (hs : c.sortsOf vs = some fn.args) :
    ¬ ∀ cl ∈ fn.clauses, Fails c vs cl := by
  intro hall
  have h := List.all_eq_true.mp preds_var fn hfn
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨hargs, cl, hcl, ⟨hreq, hvars⟩, hpats⟩ := h
  rw [hargs] at hs
  obtain ⟨v, rfl, hv⟩ := sortsOf_single hs
  obtain ⟨hf⟩ := hall cl hcl
  have hws : c.WellSortedAt cl.vars cl.leftVars [(0, v)] := by
    intro i _ s hs'
    rw [hvars] at hs'
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hs'
      subst hs'; exact ⟨v, rfl, hv⟩
    · simp at hs'
  have hpv : PatVals c [(0, v)] cl.pats [v] := by
    rw [isVar0_spec hpats]; exact .cons (.var rfl) .nil
  rw [Option.isNone_iff_eq_none] at hreq
  cases hf [(0, v)] hws hpv with
  | intro ht _ _ => rw [hreq] at ht; cases ht
  | pre h =>
    rw [Semantics.allFns_preTop clausesPreTopC fn hfn cl hcl] at h
    cases h

theorem satI_fallback {φ : KoreAML.P} (h : ΓFallback c φ) : I ⊧ᴵ φ := by
  rcases h with ⟨k, vs, hk, hs, hh, hsil, rfl⟩ | ⟨fn, vs, hfn, hs, hall, rfl⟩
  · apply sat_of_ren
    have hs' : c2.sortsOf vs = some k.args := by rw [← sortsOf_eq]; exact hs
    rcases hfb : c.fallback k.name vs with _ | v
    · rw [ren_hookGraph (hook_names hk).1 (hook_names hk).2 vs ⊥ ⊥ rfl]
      exact inΓ2 (Or.inr (Or.inl ⟨k, vs, hk, hs', hh, hsil,
        by simp only [show c2.fallback k.name vs = none from hfb]⟩))
    · rw [ren_hookGraph (hook_names hk).1 (hook_names hk).2 vs _ _ (ren_den v)]
      exact inΓ2 (Or.inr (Or.inl ⟨k, vs, hk, hs', hh, hsil,
        by simp only [show c2.fallback k.name vs = some v from hfb]⟩))
  · exact absurd hall (not_allFail hfn hs)

/-! ## The rule -/

abbrev C : Kore.KSort := srtOf c topCellSort

theorem comps_nil : c.rules.filter (·.prio < r.prio) = [] := by decide +kernel

theorem prioRuleK_eq : prioRuleK c r = .rewrites C
    (.and C [Term.kore c (canonVars c r.vars) r.lhs, reqPat C none,
      .ceil C C (.and C [Term.kore c (canonVars c r.vars) r.rhs, .top C])])
    (.and C [Term.kore c (canonVars c r.vars) r.rhs, .top C]) := by
  unfold prioRuleK; dsimp only; rw [comps_nil]; rfl

theorem rhs_kore (vs : List KoreAML.Var) : Term.kore c vs r.rhs =
    .app ⟨⟨c.symName topLabel⟩⟩ []
      [.app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "KCell"] [Term.kore c vs (.dv Srt.int (.int 1))],
      Term.kore c vs (.app counterLabel [.dv Srt.int (.int 0)])] := rfl

theorem tr_ite (tb : KoreAML.VarTable) (p : Kore.Pattern) :
    KoreAML.tr ⟨tb, []⟩ (.app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "KCell"] [p]) =
      (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort "SortKCell")) ⬝ KoreAML.tr ⟨tb, []⟩ p := by
  rw [KoreAML.tr]; rfl

theorem rhs_empty (tb : KoreAML.VarTable) (vs : List KoreAML.Var) (e : Valuation Elem) (a : Elem) :
    ¬ (KoreAML.tr ⟨tb, []⟩ (Term.kore c vs r.rhs)).interpret I e a := by
  rw [rhs_kore]
  refine tr_app_strict rfl (List.mem_cons_self ..) (fun b => ?_) a
  rw [tr_ite]
  exact iteApp_empty e _ b

theorem ceil_empty (tb : KoreAML.VarTable) (e : Valuation Elem) (a : Elem) :
    ¬ (KoreAML.tr ⟨tb, []⟩ (.ceil C C (.and C [Term.kore c (canonVars c r.vars) r.rhs, .top C]))).interpret I e a := by
  rw [KoreAML.tr]
  unfold KoreAML.sCeil
  simp only [Pattern.interpret, KoreAML.sym]
  rintro ⟨-, b, -, hb, -⟩
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  exact rhs_empty tb _ e b hb.1

theorem satI_rule : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hs1 : KoreAML.sortOf [] (prioRuleK c r) = some C := by rw [prioRuleK_eq]; rfl
  simp only [hs1]
  rw [interpret_impl]
  intro _
  rw [KoreAML.interp_equal defI]
  intro a
  generalize KoreAML.tableOf [] (prioRuleK c r) = tb
  rw [prioRuleK_eq, KoreAML.tr]
  unfold KoreAML.sRewrites
  rw [KoreAML.interp_sImp]
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hL => ?_⟩⟩
  rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
  exact (ceil_empty tb e a hL.2.2).elim

theorem satI_rules {φ : KoreAML.P} (h : ΓRules c φ) : I ⊧ᴵ φ := by
  rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hit
    obtain rfl : r' = r := List.mem_singleton.mp hr'
    exact satI_rule
  · exact sat_of_ren (inΓ2 (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩))))

/-! ## `I` is a model of `Γc c` -/

theorem modelI : I ⊧ᴵP Γc c := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact satI_sig hφ
    · exact satI_cons hφ
    · exact satI_dom hφ
    · exact satI_colls hφ
    · exact satI_fns hφ
    · exact satI_rules hφ
    · exact satI_fallback hφ
  · exact absurd hφ.1 (by rw [readsConfined]; decide)

theorem modelIΓ : I ⊧ᴵP Γ c := fun φ h => modelI φ (Or.inl h)

/-! ## The step and its family -/

theorem famEx_eq : famEx c r [] =
    KoreAML.denB (.and C [.and C [Term.kore c (canonVars c r.vars) r.rhs, .top C]]) := rfl

theorem famEx_empty (e : Valuation Elem) (a : Elem) : ¬ (famEx c r []).interpret I e a := by
  rw [famEx_eq]; unfold KoreAML.denB
  generalize KoreAML.tableOf [] _ = tb
  rw [KoreAML.tr]
  simp only [KoreAML.trAndList]
  rw [tr_and2, KoreAML.interp_sAnd]
  exact fun h => rhs_empty tb _ e a h.1

def xv : GroundTerm := .ctor topLabel [.ctor (nRegSyms + 2) [.ctor dotk []], .ctor counterLabel [.dv Srt.int (.int 0)]]
def yv : GroundTerm :=
  .ctor topLabel [.ctor fSig.name [.dv Srt.int (.int 1)], .ctor counterLabel [.dv Srt.int (.int 0)]]

theorem hx : c.sortOf xv = some topCellSort := by decide +kernel
theorem hy : c.sortOf yv = some topCellSort := by decide +kernel
def x : Config c := ⟨xv, hx⟩
def y : Config c := ⟨yv, hy⟩

theorem ctor_top : c.isCtor topLabel = true := by decide +kernel
theorem ctor_k : c.isCtor (nRegSyms + 2) = true := by decide +kernel
theorem ctor_cnt : c.isCtor counterLabel = true := by decide +kernel
theorem ctor_dotk : c.isCtor dotk = true := by decide +kernel
theorem ctor_f : c.isCtor fSig.name = true := by decide +kernel

theorem eval_f : EvalTerm c [] (.app fSig.name [.dv Srt.int (.int 1)]) (some (.ctor fSig.name [.dv Srt.int (.int 1)])) :=
  EvalTerm.ctor ctor_f (.cons .dv .nil)

/-- The rule gives the step from `<k> .K </k>` to `Lblite{KCell}(1)` in the top cell. -/
theorem step : StepBy c r [] x y where
  mem := List.mem_singleton_self _
  hσ := fun i s h => absurd h (by simp [r])
  hmatch := .ctor ctor_top (.cons (.ctor ctor_k (.cons (.ctor ctor_dotk .nil) .nil)) (.cons (.ctor ctor_cnt (.cons .dv .nil)) .nil))
  hreq := fun _ h => nomatch h
  hpre := .top
  heval := EvalTerm.ctor ctor_top (.cons eval_f
    (.cons (EvalTerm.ctor ctor_cnt (.cons .dv .nil)) .nil))
  hens := fun _ h => nomatch h
  hpost := .top
  hprio := fun r' hr' hlt => by
    obtain rfl : r' = r := List.mem_singleton.mp hr'
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## The theory with the step's closure has a model -/

theorem step_sat : I ⊧ᴵ (stepClosureItem c).pat := by
  obtain ⟨y0, D, hpat⟩ : ∃ (y0 : EVar) (D : KoreAML.P),
      (stepClosureItem c).pat = ∀∀ y0 (KoreAML.sNext (.evar y0) ⊆⊆ D) := ⟨_, _, rfl⟩
  rw [hpat]
  intro e m
  unfold Pattern.universal
  rw [interpret_neg, interpret_exists]
  rintro ⟨a, ha⟩
  rw [interpret_neg] at ha
  apply ha
  unfold included
  rw [KoreAML.interp_total defI]
  intro b hb
  exfalso
  unfold KoreAML.sNext at hb
  obtain ⟨n, v, hn, -, happ⟩ := hb
  change evalSymb c2 .next n at hn
  simp only [evalSymb] at hn
  subst hn
  change StepE_T c2 (StepM c2) b v at happ
  cases b <;> cases v <;> simp only [StepE_T] at happ
  obtain ⟨-, -, r', hr', -⟩ := happ
  exact absurd hr' List.not_mem_nil

/-- **`c`'s theory with the step's closure has a model**: `I`. -/
theorem consistent : Consistent c :=
  ⟨Elem, inferInstance, I, fun φ hφ => by
    rcases hφ with hφ | hφ
    · exact modelI φ hφ
    · rw [hφ]; exact step_sat⟩

/-- **Soundness fails** of `c`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨-, hs⟩ := h
  have h2 : Γc c ⊧ (den c y.val ⇒ famEx c r []) := (hs x y r [] step).2
  let e : Valuation Elem := ⟨fun _ => default, fun _ _ => False⟩
  have hden := ((elemOf_spec (M := Elem) (I := I) modelIΓ hy e).1 (elemOf c I yv)).mpr rfl
  have h3 : I ⊧ᴵ (den c y.val ⇒ famEx c r []) := h2 modelI
  exact famEx_empty e _ (h3 e (elemOf c I yv) hden)

/-- info: 'KCore.Faithful.CtorIteSoundC.not_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_sound

/-- info: 'KCore.Faithful.CtorIteSoundC.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms consistent

end KCore.Faithful.CtorIteSoundC
