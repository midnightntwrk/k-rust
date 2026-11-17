/-
  The tie (C14) of kimp's 79 rewrite rules (`examples/ref-kimp/RefKimp/definition.kore`, user
  module `IMP`, sentences 700 to 778, the account's rewrite-rule class), on the literals `kore` and
  `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean test/TieKimpRules.lean`.

  The j-th rule of `defn` and the j-th sentence of `ruleText` (sentence 700 + j) are read together
  (`ruleTieB`, decided by ranges of the rules and joined by `tieAll_range`): Γ's axiom of the rule
  (`prioRuleK`; no rule has a priority of its own, so it names no competitor) is
  `\rewrites{C}(\and{C}(l, t, ⌈r⌉), r)`, and the text's sentence is its translation without the
  conjunct `⌈r⌉` (`rules_text`).
  - W1 (`rules_entail`): the text's sentence entails Γ's item, for every H: a conjunct more on the
    left side of a rewrite gives a consequence.
  - The converse for `ruleItems` (`rules_from_text`): the j-th item is a consequence of
    `ruleText[j]`, for every H.
  - W2 (`rules_w2_all`, `rules_w2`): in a model of Γ, for every H, the text's sentence holds at each
    valuation at which its right side holds an element: there `⌈r⌉` holds of every configuration
    the left side holds (`tieRule_more`). The second conjunct `t` (the `requires`, an `\equals` of
    sort C, or `\top{C}()`) holds elements of the configuration sort only, and the right side is
    `\and{C}(term, \top{C}())`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"
user_axioms U from "examples/ref-kimp/RefKimp/definition.kore" module "IMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

/-- No overloading symbol, and irreflexive subsorts: what the readings of Γ's sort items ask. -/
theorem ovls_nil : c.ovls = [] := by decide +kernel
theorem subsorts_irrefl : c.subsorts.all (fun p => p.1 != p.2) = true := by decide +kernel
instance ovlOKH (H : HookParams) : OvlOK (cH H) := OvlOK.of_nil ovls_nil subsorts_irrefl

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- The text's sentences of the 79 rules, in the order of `defn`'s rules. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax700, U.ax701, U.ax702, U.ax703, U.ax704, U.ax705, U.ax706, U.ax707, U.ax708, U.ax709, U.ax710,
   U.ax711, U.ax712, U.ax713, U.ax714, U.ax715, U.ax716, U.ax717, U.ax718, U.ax719, U.ax720, U.ax721,
   U.ax722, U.ax723, U.ax724, U.ax725, U.ax726, U.ax727, U.ax728, U.ax729, U.ax730, U.ax731, U.ax732,
   U.ax733, U.ax734, U.ax735, U.ax736, U.ax737, U.ax738, U.ax739, U.ax740, U.ax741, U.ax742, U.ax743,
   U.ax744, U.ax745, U.ax746, U.ax747, U.ax748, U.ax749, U.ax750, U.ax751, U.ax752, U.ax753, U.ax754,
   U.ax755, U.ax756, U.ax757, U.ax758, U.ax759, U.ax760, U.ax761, U.ax762, U.ax763, U.ax764, U.ax765,
   U.ax766, U.ax767, U.ax768, U.ax769, U.ax770, U.ax771, U.ax772, U.ax773, U.ax774, U.ax775, U.ax776,
   U.ax777, U.ax778]

/-- **The rule sentences are the account's rewrite-rule class**, sentences 700 to 778, each once. -/
theorem rules_account : ruleText.map (·.index) = List.range' 700 79 := by decide +kernel

theorem rules_length : c.rules.length = 79 ∧ ruleText.length = 79 := by decide +kernel

/-! ## Γ's axiom of a rule and the text's sentence -/

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, \ceil{C,C}(r)), r)`, read as `C`, `l`, `t`, `r`. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and C' [l, t, .ceil C1 C2 r']) r =>
    if C' = C ∧ C1 = C ∧ C2 = C ∧ r' = r then some (C, l, t, r) else none
  | _ => none

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, r)) : p = .rewrites C (.and C [l, t, .ceil C C r]) r := by
  unfold ruleParts at h
  split at h
  · split at h
    · rename_i h'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      cases h; rfl
    · cases h
  · cases h

/-- The axiom without the left side's last conjunct. -/
def textOf (C : Kore.KSort) (l t r : Kore.Pattern) : Kore.Pattern := .rewrites C (.and C [l, t]) r

/-- The right side of a rewrite. -/
def rightOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ r => r
  | p => p

/-- The term of a right side `\and{C}(term, \top{C}())`. -/
def rightTerm : Kore.Pattern → Kore.Pattern
  | .and _ (t :: _) => t
  | p => p

/-- The conjunct `t` holds elements of the sort C only: `\top{C}()`, or an `\equals` of sort C
whose operands are of sort Bool. -/
noncomputable def inSortB (C : Kore.KSort) : Kore.Pattern → Bool
  | .top C' => decide (C' = C)
  | .equals S C' _ _ => decide (S = srtOf c Srt.bool) && decide (C' = C)
  | _ => false

/-- What W1 and W2 read of the rule `r` and the sentence `ad`: Γ's axiom has the parts `C`, `l`, `t`,
`r'`; it and the axiom without `⌈r'⌉` have one variable table and one list of free variables; the
sentence's translation is that axiom's; `C` is the configuration sort, `t` holds elements of C only,
`r'` is `\and{C}(term, \top{C}())`, and the sentence's right side translates as `r'`. -/
noncomputable def ruleTieB (r : Rule) (ad : AxiomDecl) : Bool :=
  match ruleParts (prioRuleK c r) with
  | some (C, l, t, rr) =>
    decide (tableOf [] (prioRuleK c r) = tableOf [] (textOf C l t rr)) &&
    decide ((freeOf [] (prioRuleK c r)).eraseDups = (freeOf [] (textOf C l t rr)).eraseDups) &&
    decide ((trS ad).pat = (trAxiom [] [] (kAx (textOf C l t rr))).pat) &&
    decide (C = srtOf c topCellSort) && inSortB C t && decide (rr = .and C [rightTerm rr, .top C]) &&
    decide (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, []⟩ (rightOf ad.ax.pattern) =
      tr ⟨tableOf [] (textOf C l t rr), []⟩ rr)
  | none => false

/-- The facts `ruleTieB` decides, as propositions. -/
structure RuleTie (r : Rule) (ad : AxiomDecl) (C : Kore.KSort) (l t rr : Kore.Pattern) : Prop where
  shape : prioRuleK c r = .rewrites C (.and C [l, t, .ceil C C rr]) rr
  table : tableOf [] (prioRuleK c r) = tableOf [] (textOf C l t rr)
  free : (freeOf [] (prioRuleK c r)).eraseDups = (freeOf [] (textOf C l t rr)).eraseDups
  text : (trS ad).pat = (trAxiom [] [] (kAx (textOf C l t rr))).pat
  top : C = srtOf c topCellSort
  inSort : inSortB C t = true
  right : rr = .and C [rightTerm rr, .top C]
  rightTr : tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, []⟩ (rightOf ad.ax.pattern) =
    tr ⟨tableOf [] (textOf C l t rr), []⟩ rr

theorem ruleTie_of {r : Rule} {ad : AxiomDecl} (h : ruleTieB r ad = true) :
    ∃ C l t rr, RuleTie r ad C l t rr := by
  unfold ruleTieB at h
  split at h
  · rename_i C l t rr hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    exact ⟨C, l, t, rr, ruleParts_eq hp, h1, h2, h3, h4, h5, h6, h7⟩
  · cases h

/-! ## The rules, decided by ranges -/

/-- Each rule with its sentence. -/
noncomputable def rulePairs : List (Rule × AxiomDecl) := c.rules.zip ruleText

noncomputable def ruleTieP (p : Rule × AxiomDecl) : Bool := ruleTieB p.1 p.2

theorem rules_0 : ((rulePairs.drop 0).take 20).all ruleTieP = true := by decide +kernel
theorem rules_20 : ((rulePairs.drop 20).take 20).all ruleTieP = true := by decide +kernel
theorem rules_40 : ((rulePairs.drop 40).take 20).all ruleTieP = true := by decide +kernel
theorem rules_60 : (rulePairs.drop 60).all ruleTieP = true := by decide +kernel

/-- Each rule of `defn` and its sentence are read as `ruleTieB` says. -/
theorem rules_tied : rulePairs.all ruleTieP = true :=
  tieAll_whole (p := ruleTieP) <|
    tieAll_range (a := 0) (n := 20) rules_0 <|
    tieAll_range (a := 20) (n := 20) rules_20 <|
    tieAll_range (a := 40) (n := 20) rules_40 <|
    rules_60

theorem rulePairs_tie {p : Rule × AxiomDecl} (h : p ∈ rulePairs) : ∃ C l t rr, RuleTie p.1 p.2 C l t rr :=
  ruleTie_of (List.all_eq_true.mp rules_tied p h)

/-- The rule at place `j` and the sentence at place `j` are a pair of `rulePairs`. -/
theorem rulePairs_at {j : Nat} {r : Rule} {ad : AxiomDecl} (hr : c.rules[j]? = some r)
    (had : ruleText[j]? = some ad) : (r, ad) ∈ rulePairs :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hr, had⟩)

/-- Each sentence of `ruleText` is paired with a rule. -/
theorem ruleText_paired {ad : AxiomDecl} (h : ad ∈ ruleText) : ∃ r, (r, ad) ∈ rulePairs := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  have hj' : j < c.rules.length := by rw [rules_length.1]; rw [rules_length.2] at hj; exact hj
  exact ⟨c.rules[j], rulePairs_at (List.getElem?_eq_getElem hj') (List.getElem?_eq_getElem hj)⟩

/-! ## W1, and the converse for `ruleItems` -/

/-- **A conjunct more on a rule's left side gives a consequence**: in a model of definedness, the
rule axiom with the left side `l ∧ t` entails the one with the left side `l ∧ t ∧ ⌈r⌉`, where the
two have one variable table and one list of free variables. -/
theorem rewrite_weaken {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    {P : Kore.Pattern} {C : Kore.KSort} {l t rr : Kore.Pattern}
    (hP : P = .rewrites C (.and C [l, t, .ceil C C rr]) rr)
    (ht : tableOf [] P = tableOf [] (textOf C l t rr))
    (hf : (freeOf [] P).eraseDups = (freeOf [] (textOf C l t rr)).eraseDups)
    (h : I ⊧ᴵ (trAxiom [] [] (kAx (textOf C l t rr))).pat) : I ⊧ᴵ (trAxiom [] [] (kAx P)).pat := by
  intro e m
  have h1 := h e m
  simp only [trAxiom, kAx, List.map_nil, List.nil_append] at h1 ⊢
  rw [ht, hf]
  subst hP
  unfold textOf at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩

/-- **W1 for the 79 rules**: the text's sentence entails Γ's axiom of its rule, for every H (Γ's
axiom does not read H). -/
theorem rules_entail : ∀ p ∈ rulePairs, itemsPremises [trS p.2] ⊧ (trAxiom [] [] (kAx (prioRuleK c p.1))).pat := by
  intro p hp M _ I hI
  obtain ⟨C, l, t, rr, rt⟩ := rulePairs_tie hp
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  refine rewrite_weaken hD rt.shape rt.table rt.free ?_
  rw [← rt.text]
  exact hI _ (Or.inl ⟨trS p.2, List.mem_singleton_self _, rfl⟩)

/-- **The text's sentence is Γ's axiom without the premise it adds**: for each rule, Γ's axiom is
`\rewrites{C}(\and{C}(l, t, ⌈r⌉), r)` and the sentence translates as `\rewrites{C}(\and{C}(l, t), r)`. -/
theorem rules_text : ∀ p ∈ rulePairs, ∃ C l t rr,
    prioRuleK c p.1 = .rewrites C (.and C [l, t, .ceil C C rr]) rr ∧
    (trS p.2).pat = (trAxiom [] [] (kAx (.rewrites C (.and C [l, t]) rr))).pat := by
  intro p hp
  obtain ⟨C, l, t, rr, rt⟩ := rulePairs_tie hp
  exact ⟨C, l, t, rr, rt.shape, rt.text⟩

/-- **The converse for `ruleItems`**: the j-th item is a consequence of the j-th sentence of
`ruleText`, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [ruleItems_withHooks] at hj
  unfold ruleItems at hj
  rw [List.getElem?_map] at hj
  cases hr : c.rules[j]? with
  | none => rw [hr] at hj; cases hj
  | some r =>
    rw [hr] at hj
    have hit := (Option.some.inj hj).symm
    have hjr : j < c.rules.length := (List.getElem?_eq_some_iff.mp hr).1
    have hjt : j < ruleText.length := by rw [rules_length.2]; rw [rules_length.1] at hjr; exact hjr
    refine ⟨ruleText[j], List.getElem?_eq_getElem hjt, ?_⟩
    subst hit
    exact rules_entail _ (rulePairs_at hr (List.getElem?_eq_getElem hjt))

/-! ## W2 -/

theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
theorem bool_numbered (H : HookParams) : Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.bool < nRegSorts + c.sortNames.length)

/-- The right side of the sentence holds an element at the valuation `e`. -/
def RightDefined (ad : AxiomDecl) {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) : Prop :=
  ∃ b, (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, []⟩ (rightOf ad.ax.pattern)).interpret I e b

/-- **W2 for the 79 rules, at every valuation**: in a model of Γ, for every H, each rule sentence
holds at each valuation at which its right side holds an element. Γ's axiom is the sentence with
the definedness of the right side on its left side, which holds there of every configuration the
left side holds. -/
theorem rules_w2_all (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : ∀ ad ∈ ruleText, ∀ e, RightDefined ad I e → ∀ m, (trS ad).pat.interpret I e m := by
  intro ad had e hdef m
  obtain ⟨r, hp⟩ := ruleText_paired had
  obtain ⟨C, l, t, rr, rt⟩ := rulePairs_tie hp
  rw [rt.text]
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (top_numbered H)
  have hdef' : ∃ b, (tr ⟨tableOf [] (textOf C l t rr), []⟩ rr).interpret I e b := by
    rw [← rt.rightTr]; exact hdef
  generalize hT : tableOf [] (textOf C l t rr) = T at hdef'
  have hS : ∀ b, (trSort T C).interpret I e b ↔ b = σ := fun b => by
    rw [rt.top]; unfold srtOf; rw [trSort_srt]; exact hσ1 b
  have htop : ∀ a, (tr ⟨T, []⟩ (.top C)).interpret I e a → Inh I σ a := fun a ha => by
    rw [KoreAML.tr, interp_sTop hD (by rw [rt.top]; unfold srtOf; rw [trSort_srt]; rfl), interp_inhOf_of hS] at ha
    exact ha
  have htIn : ∀ a, (tr ⟨T, []⟩ t).interpret I e a → Inh I σ a := by
    have hin := rt.inSort
    cases t with
    | top C' =>
      simp only [inSortB, decide_eq_true_eq] at hin
      subst hin; exact htop
    | equals S C' φ ψ =>
      simp only [inSortB, Bool.and_eq_true, decide_eq_true_eq] at hin
      obtain ⟨rfl, rfl⟩ := hin
      intro a ha
      rw [KoreAML.tr] at ha
      obtain ⟨σB, hB1, hB2⟩ := sortSing hI (bool_numbered H)
      have hSB : ∀ b, (trSort T (srtOf c Srt.bool)).interpret I e b ↔ b = σB := fun b => by
        unfold srtOf; rw [trSort_srt]; exact hB1 b
      exact ((interp_sEquals hD hc hSB hS hB2 hσ2 a).mp ha).1
    | _ => simp [inSortB] at hin
  have hg : I ⊧ᴵ (trAxiom [] [] (kAx (prioRuleK c r))).pat :=
    hI _ (mem_Γ_rules (Or.inl ⟨_, by
      rw [ruleItems_withHooks]
      exact List.mem_map.mpr ⟨r, List.of_mem_zip hp |>.1, rfl⟩, rfl⟩))
  refine tieRule_more hD (g := kAx (prioRuleK c r)) (t := kAx (textOf C l t rr)) (ls := [l, t])
    (xs := [.ceil C C rr]) (List.cons_ne_nil _ _) rt.shape rfl rt.table rt.free hg e (fun x hx a hls => ?_) m
  rw [List.mem_singleton.mp hx]
  show (tr ⟨tableOf [] (textOf C l t rr), []⟩ (.ceil C C rr)).interpret I e a
  have hls' : ∀ p ∈ [l, t], (tr ⟨tableOf [] (textOf C l t rr), []⟩ p).interpret I e a := hls
  rw [hT] at hls' ⊢
  rw [KoreAML.tr]
  refine (interp_sCeil hD hc hS hS hσ2 hσ2 (fun b hb => ?_) a).mpr ⟨hdef', htIn a (hls' t (by simp))⟩
  rw [rt.right] at hb
  exact htop b ((interp_and (List.cons_ne_nil _ _)).mp hb _ (by simp))

/-- **W2 for the 79 rules** (`AtValues` with the guard): in a model of Γ, for every H, each rule
sentence holds at each valuation that sends its variables to values and at which its right side
holds an element. No rule has a rule of a smaller priority, so the guard has no second part. -/
theorem rules_w2 (H : HookParams) : ∀ ad ∈ ruleText, ∀ (M : Type) (_ : Inhabited M)
    (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) → ∀ e, AtValues (cH H) I e ad.ax →
      RightDefined ad I e → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had _ _ _ hI e _ hdef m => rules_w2_all H hI ad had e hdef m

end KCore.TieKimp

#check @KCore.TieKimp.rules_from_text
#check @KCore.TieKimp.rules_entail
#check @KCore.TieKimp.rules_text
#check @KCore.TieKimp.rules_w2
#print axioms KCore.TieKimp.rules_account
#print axioms KCore.TieKimp.rules_from_text
#print axioms KCore.TieKimp.rules_text
#print axioms KCore.TieKimp.rules_w2
