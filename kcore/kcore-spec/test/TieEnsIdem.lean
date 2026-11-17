/-
  The tie (C14) on `f2-examples/ens.kompile.kore` for set idempotence, sentence 61,
  `_Set_(K, K) = K`. Γ denies the sentence as written (`idem_refuted`, test/TieEns.lean): the graph
  of `_Set_` states `_Set_(S, S) = ⊥` at a set S with a member, a point that is not silent, so no
  interpretation of the hooks rescues it (G7, `KCore.Guards.setIdem_bot` in test/Guards.lean). Under the definedness of its left side,
  `⌈_Set_(K, K)⌉ → _Set_(K, K) = K` (`ax61g`), the sentence is entailed at values for every H
  (`idem_guarded`): at a set with a member the left side denotes nothing, at the empty set the
  graph gives the empty set.
  Run from the package root: `lake env lean test/TieEnsIdem.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)
def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩
noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")
theorem idem_pattern : U.ax61.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem set_numbered (H : HookParams) : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name (H : HookParams) : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem symApp_withHooks (H : HookParams) (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-! ## Set idempotence (61): the guarded sentence, at values -/

/-- An equation `l = r` under the definedness of its left side: `⌈l⌉ → l = r`. -/
def guardLeft : Kore.Pattern → Kore.Pattern
  | .equals s R l r => .implies R (.ceil s R l) (.equals s R l r)
  | p => p

/-- Sentence 61 under the definedness of its left side: `⌈_Set_(K, K)⌉ → _Set_(K, K) = K`. -/
noncomputable def ax61g : AxiomDecl :=
  ⟨U.ax61.index, U.ax61.module, ⟨U.ax61.ax.sortVars, guardLeft U.ax61.ax.pattern, U.ax61.ax.attributes⟩⟩

theorem idemg_pattern : ax61g.ax.pattern = .implies KoreAML.R
    (.ceil (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]))
    (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar) := by
  show guardLeft U.ax61.ax.pattern = _
  rw [idem_pattern]; rfl
theorem idemg_trS : (trS ax61g).pat = (trAxiom [] [] ax61g).pat := by decide +kernel
theorem idemg_free : (ax61g.ax.sortVars.map sortVarKey ++ freeOf [] ax61g.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idemg_K : VarKey.evar "K" (KoreAML.srt "Set") ∈ (freeOf [] ax61g.ax.pattern).eraseDups := by decide +kernel

/-- The one sort named `Set` is the registry's. -/
theorem set_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Set") : S = Srt.set := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Set" → S = Srt.set) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)

/-- `_Set_` at one set twice: no value at a set with a member, the empty set at the empty set. -/
theorem concat_self (es : List GroundTerm) :
    hook setConcat [.set Srt.set es, .set Srt.set es] = some none ∨
      (es = [] ∧ hook setConcat [.set Srt.set es, .set Srt.set es] = some (some (.set Srt.set es))) := by
  rw [hook_setConcat]
  cases es with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | cons x xs =>
    refine Or.inl ?_
    have hm : memS x (x :: xs) = true := (Set.memS_iff x (x :: xs)).mpr List.mem_cons_self
    have : concatS (x :: xs) (x :: xs) = none := by
      unfold concatS
      rw [List.all_cons, hm]
      rfl
    rw [this]; rfl

/-- **The guarded sentence is entailed at values**, for every H: at a set `K` with a member,
`_Set_(K, K)` denotes nothing (the hook's graph, no silent point), so the sentence holds for want
of its premise; at the empty set the graph gives the empty set. -/
theorem idem_guarded (H : HookParams) : EntailsAtValues (cH H) ax61g (trS ax61g).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "K" (KoreAML.srt "Set") idemg_K
  have hS' : S = Srt.set := set_of_name S hS
  subst hS'
  obtain ⟨es, rfl⟩ := shape_set shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  rw [idemg_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [idemg_free]
  generalize ht : tableOf ax61g.ax.sortVars ax61g.ax.pattern = t at hden ⊢
  rw [idemg_pattern, interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  rw [interp_equal hD]
  intro a
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  have hSs : ∀ b, (trSort t (srtOf c Srt.set)).interpret I e b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, -⟩ := elemOf_spec hI hv e
  have hK : ∀ b, (tr ⟨t, []⟩ kVar).interpret I e b ↔ (den (cH H) (.set Srt.set es)).interpret I e b := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar, hes b]
    show b = e.evalEvar (t.ev (.evar "K" (KoreAML.srt "Set"))) ↔ _
    rw [(hes _).mp hden]
  -- the application at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (symApp c setConcat [kVar, kVar])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [.set Srt.set es, .set Srt.set es]))).interpret I e b := by
    intro b
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.trArgs_cons, KoreAML.trArgs_cons,
      KoreAML.trArgs_nil]
    exact interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => hK m) m) (fun m => hK m) b
  have hargs : (cH H).sortsOf [.set Srt.set es, .set Srt.set es] = some [Srt.set, Srt.set] := by
    simp only [Semantics.sortsOf, hv]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  refine ⟨fun h => h.1, fun ha => ⟨ha, fun hceil => ?_⟩⟩
  rw [KoreAML.tr, interp_sCeil_raw] at hceil
  obtain ⟨-, -, x, -, -, hx, -⟩ := hceil
  rcases concat_self es with hn | ⟨rfl, hs⟩
  · have hgraph := sat_dom hI (Or.inl ⟨_, [.set Srt.set es, .set Srt.set es], none, concat_sig, hargs, hn,
      fun _ => silent_of_not_silentKey (by decide +kernel) _, rfl⟩)
    exact absurd ((hL x).mp hx) (fun h => ((KoreAML.interp_equal hD).mp (hgraph e default) x).mp h)
  · have hgraph := sat_dom hI (Or.inl ⟨_, [.set Srt.set [], .set Srt.set []], some (.set Srt.set []), concat_sig, hargs, hs,
      fun h => absurd h (by simp), rfl⟩)
    rw [KoreAML.tr, interp_sEquals hD hc hSs hRv hσS2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b _ => ?_⟩
    rw [hL b, (KoreAML.interp_equal hD).mp (hgraph e default) b, hK b]

end KCore.TieEns
#print axioms KCore.TieEns.idem_guarded
