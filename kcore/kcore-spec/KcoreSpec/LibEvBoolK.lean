/-
  KCore, checked layer: `_==K_` at two K sequences of one injected item, rewritten to the equality
  symbol of the items' sort, is entailed at values (`EntailsAtValues`), for every semantics meeting
  `coreOK` in which the sort is below KItem and its values have their shapes (`shapesOK`).

  The sentences are those kompile writes for domains.md 2338 (K 7.1.337, Bool) and 1404 (Int),
  `\implies{R}(\top{R}(), \equals{SortBool, R}(==K(kseq(inj{s, KItem}(X1), dotk()),
  kseq(inj{s, KItem}(X2), dotk())), \and{SortBool}(f(X1, X2), \top{SortBool}())))`.
  - `LibEv.KSeqEq`: such an equation, `s` the sort of the variables and `f` the right side's
    symbol; `KSeqEq.patR` its pattern over the registry's names.
  - `LibEv.kseqItem_den`: the translated `kseq(inj{s, KItem}(x), dotk())`, where `x` denotes the
    element of a value `v` of the sort `s`, denotes the element of `v` as a value of K (`wrapK`).
  - `LibEv.KSeqEq.entailed`: where `f` is `true` at two values of `s` exactly where they are equal,
    the equation is entailed at values: `==K` is equality of values of K (`eqK_den`), and two
    values of `s` wrapped as values of K are equal exactly where they are (`wrapK_inj`).
  - `LibEv.boolKEq_ev`, `LibEv.intKEq_ev`: the two sentences.
-/
import KcoreSpec.LibEvPred

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- `kseq(inj{s, KItem}(x), dotk())` with the registry's names: a term `x` of the sort `s` as a
K sequence of one item. -/
def kseqItemR (s : Srt) (x : Kore.Pattern) : Kore.Pattern :=
  KoreAML.kseq1 (KoreAML.injP (regSortNames.getD s "") (regSortNames.getD Srt.kitem "") x)

/-- The equation `kseq(inj{s, KItem}(X1), dotk()) ==K kseq(inj{s, KItem}(X2), dotk()) => f(X1, X2)`
over the variables `x1`, `x2` of the sort `s`. -/
structure KSeqEq where
  x1 : String
  x2 : String
  s : Srt
  f : Sym

namespace KSeqEq

/-- The variables `x1`, `x2`, both of the sort `s`. -/
def vars (E : KSeqEq) : Vars := [(E.x1, E.s), (E.x2, E.s)]

/-- The right side `f(X1, X2)`. -/
def rhs (E : KSeqEq) : Term := .app E.f [.var 0, .var 1]

/-- The pattern of the equation's axiom with the registry's names, over the sort variable `R`. -/
def patR (E : KSeqEq) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals (regSrtK Srt.bool) KoreAML.R
      (.app ⟨⟨regSymNames.getD kEq ""⟩⟩ []
        [kseqItemR E.s (koreR E.vars (.var 0)), kseqItemR E.s (koreR E.vars (.var 1))])
      (.and (regSrtK Srt.bool) [koreR E.vars E.rhs, .top (regSrtK Srt.bool)]))

end KSeqEq

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- **A K sequence of one injected item denotes the item's value as a value of K.** Where `x`
denotes the element of a value `v` of a sort `s` below KItem (and neither K nor KItem), the
translated `kseq(inj{s, KItem}(x), dotk())` denotes the element of `wrapK s v`. -/
theorem kseqItem_den (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hsr : s < nRegSorts) (hsK : s ∈ c.sortsBelowKItem) (hk : s ≠ Srt.k) (hki : s ≠ Srt.kitem)
    {tbl : KoreAML.VarTable} {e : Valuation M} {x : Kore.Pattern} {v : GroundTerm} (hv : c.sortOf v = some s)
    (hx : ∀ m, (KoreAML.tr ⟨tbl, []⟩ x).interpret I e m ↔ m = elemOf c I v) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (kseqItemR s x)).interpret I e m ↔ (den c (wrapK s v)).interpret I e m := by
  have hw : wrapK s v = .ctor kseq [injNormal s Srt.kitem v, .ctor dotk []] := by
    unfold wrapK; simp only [hk, hki, ↓reduceIte]
  have hsn : c.sortName s = regSortNames.getD s "" := by unfold Semantics.sortName; simp only [hsr, ↓reduceIte]
  have hkseq : c.symName kseq = "kseq" := symName_reg c (by decide)
  have hkn : c.sortName Srt.kitem = regSortNames.getD Srt.kitem "" := rfl
  rw [hw, den_ctor, hkseq]
  unfold kseqItemR KoreAML.kseq1 KoreAML.ap
  rw [KoreAML.tr_app0]
  simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => ?_))
    (fun m => ?_) m
  · show _ ↔ (den c (injNormal s Srt.kitem v)).interpret I e m
    rw [den_injNormal_gs hI htr (kitem_sub hsK) hv, KoreAML.tr_injP, interp_injApp, hsn, hkn]
    constructor
    · rintro ⟨y, hy, hm⟩
      rw [hx] at hy
      rw [← hy]
      exact hm
    · intro hm
      exact ⟨_, (hx _).mpr rfl, hm⟩
  · show _ ↔ (KoreAML.tr ⟨[], []⟩ (GroundTerm.kore c (.ctor dotk []))).interpret I e m
    rw [GroundTerm.kore, KoreAML.tr_app0, KoreAML.tr_app0]
    rfl

/-- **`==K` of two K sequences of one injected item.** Where `x`, `y` denote the elements of values
`v`, `w` of a sort `s` below KItem, the translated `kseq(inj{s, KItem}(x), dotk()) ==K
kseq(inj{s, KItem}(y), dotk())` denotes the element of the Bool value `wrapK s v = wrapK s w`. -/
theorem kEqSeq_den (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hsr : s < nRegSorts) (hsK : s ∈ c.sortsBelowKItem) (hk : s ≠ Srt.k) (hki : s ≠ Srt.kitem)
    {tbl : KoreAML.VarTable} {e : Valuation M} {x y : Kore.Pattern} {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (hx : ∀ m, (KoreAML.tr ⟨tbl, []⟩ x).interpret I e m ↔ m = elemOf c I v)
    (hy : ∀ m, (KoreAML.tr ⟨tbl, []⟩ y).interpret I e m ↔ m = elemOf c I w) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (.app ⟨⟨regSymNames.getD kEq ""⟩⟩ [] [kseqItemR s x, kseqItemR s y])).interpret I e m ↔
      (den c (bool (GroundTerm.cmp (wrapK s v) (wrapK s w) == .eq))).interpret I e m := by
  have hb : BelowK c s := Or.inr (Or.inr hsK)
  rw [← eqK_den hI (sortOf_wrapK htr hb hv) (sortOf_wrapK htr hb hw) e m]
  unfold KoreAML.den
  rw [tr_symApp, KoreAML.tr_app0]
  have hh : symHead c kEq = KoreAML.sym (.symbol (regSymNames.getD kEq "")) := by
    have hn : c.symName kEq = regSymNames.getD kEq "" := symName_reg c (by decide)
    have hi : instDecode? (regSymNames.getD kEq "") = none := by decide
    rw [symHead_noInst (by rw [hn]; exact hi), hn]
  rw [hh]
  simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  exact KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl)
    (kseqItem_den hI htr hsr hsK hk hki hv hx)) (kseqItem_den hI htr hsr hsK hk hki hw hy) m

end

/-- **`==K` at two K sequences of one injected item is the equality of the items.** For a
semantics meeting `coreOK`, a registry sort `s` below KItem (neither K nor KItem), and a symbol `f`
of two arguments of the sort `s` whose value at two values of `s` is the Bool `true` exactly where
they are equal: the translation of any axiom declaration whose pattern is `E.patR`, over the one
sort variable `R`, holds in every model of `Γ c` at every valuation that sends the axiom's free
element variables to values. -/
theorem KSeqEq.entailed {c : Semantics} (h : c.coreOK = true) (E : KSeqEq)
    (hsr : E.s < nRegSorts) (hsK : E.s ∈ c.sortsBelowKItem) (hk : E.s ≠ Srt.k) (hki : E.s ≠ Srt.kitem)
    (hrs : srt? c E.vars E.rhs = some Srt.bool) (hrr : reg E.rhs = true)
    (hfree : E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2))) = true)
    (hf : ∀ v w, c.sortOf v = some E.s → c.sortOf w = some E.s →
      ∃ r : Bool, c.hv E.f [v, w] = some (bool r) ∧ (r = true ↔ v = w))
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -⟩ := faithCoreOK_parts hfa
  have htr := NamesApart.subsorts_trans_of hids hok
  have hvR : ∀ p ∈ E.vars, p.2 < nRegSorts := by
    intro p hp'
    simp only [KSeqEq.vars, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> exact hsr
  have hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern := by
    intro i hi
    have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    have := (List.all_eq_true.mp hfree) _ hmem
    rw [hp]
    unfold vkey
    rw [srtOf_reg c (hvR _ hmem)]
    exact List.mem_of_elem_eq_true this
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValues h hI hat E.vars hvR hfv
  obtain ⟨v, hv0, hvs⟩ := hσ 0 (E.x1, E.s) rfl
  obtain ⟨w, hw0, hws⟩ := hσ 1 (E.x2, E.s) rfl
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hag : ∀ i v, i < E.vars.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.vars i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨h1, h2⟩ := hel i v hi hv
    rw [(elemOf_spec hI h1 e).1 m', h2]
  -- the variables denote the elements of their values
  have hvar : ∀ i u, i < E.vars.length → σ.lookup i = some u → c.sortOf u = some E.s →
      ∀ m, (KoreAML.tr ⟨t, []⟩ (koreR E.vars (.var i))).interpret I e m ↔ m = elemOf c I u := by
    intro i u hi hu hus m'
    rw [← kore_reg c hvR (.var i) rfl, kore, KoreAML.tr]
    show m' = e.evalEvar (t.ev (vkey c E.vars i)) ↔ _
    rw [hag i u hi hu m', (elemOf_spec hI hus e).1 m']
  have hlhs := kEqSeq_den hI htr hsr hsK hk hki (tbl := t) (e := e) hvs hws
    (hvar 0 v (show 0 < 2 by decide) hv0 hvs) (hvar 1 w (show 1 < 2 by decide) hw0 hws)
  -- the right side
  have hDV := den_val (tbl := t) (e := e) h hI hσ hag E.rhs hrs
  obtain ⟨r, hr, hriff⟩ := hf v w hvs hws
  have hval : val c σ E.rhs = some (bool r) := by
    show (allSome [σ.lookup 0, σ.lookup 1]).bind (c.hv E.f) = _
    rw [hv0, hw0]
    exact hr
  have hcmp : (GroundTerm.cmp (wrapK E.s v) (wrapK E.s w) == .eq) = r := by
    refine Bool.eq_iff_iff.mpr ?_
    rw [beq_iff_eq, KCore.cmp_eq_iff, hriff]
    exact ⟨wrapK_inj hg hvs hws, fun he => by rw [he]⟩
  -- the equation
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (Nat.lt_of_lt_of_le (show Srt.bool < nRegSorts by decide)
    (Nat.le_add_right _ _))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hbs : regSrtK Srt.bool = srtOf c Srt.bool := (srtOf_reg c (by decide)).symm
  rw [hp]
  unfold KSeqEq.patR
  rw [hbs, ← kore_reg c hvR E.rhs hrr]
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hlhs b, hcmp, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c Srt.bool)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c Srt.bool)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c Srt.bool)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e),
      hDV.1 b, hval]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩

/-! ## The two sentences -/

/-- `==Bool` at two Bool values. -/
theorem boolEq_graphK {c : Semantics} (hs : c.shapesOK = true) (v w : GroundTerm)
    (hv : c.sortOf v = some Srt.bool) (hw : c.sortOf w = some Srt.bool) :
    ∃ r : Bool, c.hv boolEq [v, w] = some (bool r) ∧ (r = true ↔ v = w) := by
  obtain ⟨x, rfl⟩ := shape_bool hs hv
  obtain ⟨y, rfl⟩ := shape_bool hs hw
  refine ⟨x == y, hv_of_value rfl, ?_⟩
  have hxy : bool x = bool y ↔ x = y :=
    ⟨fun hh => by unfold bool at hh; injection hh with _ hh; injection hh, fun hh => by rw [hh]⟩
  rw [hxy, beq_iff_eq]

/-- domains.md 2338: `inj{Bool, KItem}(K1) ==K inj{Bool, KItem}(K2) => K1 ==Bool K2`. -/
def boolKEq : KSeqEq := ⟨"VarK1", "VarK2", Srt.bool, boolEq⟩

/-- domains.md 1404: `inj{Int, KItem}(I1) ==K inj{Int, KItem}(I2) => I1 ==Int I2`. -/
def intKEq : KSeqEq := ⟨"VarI1", "VarI2", Srt.int, intEq⟩

/-- **domains.md 2338** is entailed at values. -/
theorem boolKEq_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (hsK : Srt.bool ∈ c.sortsBelowKItem) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = boolKEq.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  KSeqEq.entailed h boolKEq (by decide) hsK (by decide) (by decide) rfl (by decide) (by decide)
    (boolEq_graphK hs) ad hp hsv

/-- **domains.md 1404** is entailed at values. -/
theorem intKEq_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (hsK : Srt.int ∈ c.sortsBelowKItem) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = intKEq.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  KSeqEq.entailed h intKEq (by decide) hsK (by decide) (by decide) rfl (by decide) (by decide)
    (fun v w hv hw => by
      obtain ⟨r, hr, hiff⟩ := intEq_graph hs false v w hv hw
      exact ⟨r, hr, by simpa using hiff⟩) ad hp hsv

end LibEv

end KCore
