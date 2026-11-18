/-
  The parameter hooks of K-IO, FFI, K-REFLECTION, TIMER, UNIFICATION and JSON on the construct
  fixtures e6-param-io, e6-param-ffi, e6-param-kreflection, e6-param-timer, e6-param-unification and
  e6-param-json (`f2-examples/e6-param-*.kompile.kore`, each the text its fixture's kompile.txt
  hashes, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory relative
  to the tree). Each text applies every hooked function of its module that no registry hook
  interprets once, in a rule's right side (`go(N, …)`); the reader reads each as a parameter symbol
  no hook implements (`impl = none`, `raw = false`; the fixture's params.txt): its value at an
  argument list is the interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the
  interpretation gives none. The hooked functions of FFI, TIMER and UNIFICATION are sentences of K
  builtin files no library text states, read as the definition's own (`Parse.isOwnBuiltin`).

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undeterminedPS`). The pair of models: under `HookParams.none` the
  application is ⊥ in every model of Γ, under `constHPS v` it is `v` in every model, and both
  theories have models (`sound_hyp`). An instance reads its facts of the text as one decided test
  (`okPS`: the parameter named, looked up by its number, no hook implementing it, the point's
  arguments values of its argument sorts and the given value one of its result sort).

  `FnHyp` under every H: JSON's text has no function (`fnHyp_of_fnsNilPS`). The other five have
  K's `append` (a parameter giving a K is appended to the rest of the cell), declared total, which
  the totality decider does not confirm: its cover check splits only the definition's own sorts,
  and K is the registry's (FFI's text also has the function `#ffiCall` of six arguments, which owes
  no fact). `fnHyp_appendPS` shows `append` total from facts decided on the text (`appendOKPS`):
  the values of K are `kseq` and `dotk` terms (`kValue_invPS`), so one of `append`'s rows
  `kseq(X, Y), Z` and `.K, Z` matches every argument list (`rows_appendPS`), its self call
  decreases in the first argument, and its right sides are total over itself (`total_of_rowsPS`, by
  induction on the decreasing argument's size); the other facts `FnHyp` asks are the deciders'.

  The points are values of the argument sorts (`1`, `"a"`, `b"a"`, `1` as a KItem, the empty K,
  `ListItem(1)`, `#ffi_sint`) and the given values one of the result sort (an IOInt, an IOString,
  `#tempFile("a", 1)`, `SetItem(1)`, `null`, ...). Whatever value the K prose would name there,
  none is entailed: the text states no sentence of these symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamE6Sys.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE6Sys

open KCore ML Faithful

/-! ## The schema, at a parameter no hook implements -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev appPS (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts. -/
theorem gamma_paramPS (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (appPS c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- The interpretation that gives `v` everywhere. -/
def constHPS (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a parameter no hook implements and no open generator, the value under H is H's answer,
kept where it has the result sort. -/
theorem paramVal_implNonePS (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    (vs : List GroundTerm) :
    (c.withHooks H).paramVal k.sig.name vs = (H.app k.sig.name vs).filter
      fun v => c.sortOf v == some k.sig.result := by
  have hk : k ∈ c.params := by
    rw [Semantics.lookupParam_eq] at hlk; exact List.mem_of_find?_eq_some hlk
  have hl : (c.withHooks H).lookupParam k.sig.name = some k := hlk
  unfold Semantics.paramVal
  rw [hl]
  simp only [hi, hr k hk, Bool.false_eq_true, ite_false, Semantics.sortOf_withHooks c H hr]
  rfl

/-- **The `param_undetermined` shape** at a parameter no hook implements. Over all
interpretations, Γ entails neither that the application has no value nor that it is `v`: under
`HookParams.none` it is ⊥ in every model, under `constHPS v` it is `v` in every model, and both
theories have models (`sound_hyp`). -/
theorem param_undeterminedPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constHPS v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPS (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks (constHPS v)).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNonePS c hr _ hlk hi]
    simp [constHPS, Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNonePS c hr _ hlk hi]; rfl
  constructor
  · -- under `constHPS v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constHPS v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constHPS v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPS (c.withHooks (constHPS v)) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall (constHPS v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constHPS v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPS (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## An instance, decided on the text -/

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
def paramPS (c : Semantics) (n : String) : ParamSig :=
  (c.params.find? fun k => c.symName k.sig.name == n).getD default

/-- What an instance asks of the text, as one decided test: the parameter named `n` is the one
`lookupParam` finds by its number, no hook implements it, `vs` are values of its argument sorts and
`v` a value of its result sort. -/
def okPS (c : Semantics) (n : String) (vs : List GroundTerm) (v : GroundTerm) : Bool :=
  c.symName (paramPS c n).sig.name == n && c.lookupParam (paramPS c n).sig.name == some (paramPS c n) &&
    (paramPS c n).impl == none && c.sortsOf vs == some (paramPS c n).sig.args &&
    c.sortOf v == some (paramPS c n).sig.result

/-- `param_undeterminedPS` at the parameter named `n`, from the decided test `okPS`. -/
theorem undetermined_of_okPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hfn : ∀ H : HookParams, FnHyp (c.withHooks H)) {n : String} {vs : List GroundTerm} {v : GroundTerm}
    (h : okPS c n vs v = true) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPS (c.withHooks H) (paramPS c n).sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c n).sig.name vs ≡ den (c.withHooks H) v)) := by
  simp only [okPS, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hl⟩, hi⟩, hvs⟩, hv⟩ := h
  exact param_undeterminedPS c hok hr hl hi hvs hv (hfn _) (hfn _)

/-- With no function and no condition reading an open generator, `FnHyp` holds under every
interpretation. -/
theorem fnHyp_of_fnsNilPS (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (hfns : c.fns = [])
    (hrc : c.readsConfined = false) (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := hfns
  have hrcH : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans hrc
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrcH, openLaws_of_plain (c := c.withHooks H) hr⟩ <;>
    intro fn hfn <;> rw [h] at hfn <;> exact absurd hfn List.not_mem_nil

/-! ## The points -/

def strV : GroundTerm := .dv Srt.string (.tok "a")
/-- The Float `0.0` of double precision. -/
def floatV : GroundTerm := .dv Srt.float (.float 53 11 0)
def bytesV : GroundTerm := .dv Srt.bytes (.tok "a")
def idV : GroundTerm := .dv Srt.ident (.tok "x")
def mapV : GroundTerm := .map Srt.map [(kint 1, kint 7)]
def setV : GroundTerm := .set Srt.set [kint 1]
def listV : GroundTerm := .list Srt.list [kint 1]
/-- The empty K. -/
def kDot : GroundTerm := .ctor dotk []
def ioIntV : GroundTerm := .inj Srt.int Srt.ioInt (int 1)
def ioStrV : GroundTerm := .inj Srt.string Srt.ioString strV
/-- The symbol named `n`, by number. -/
def symPS (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0
/-- `#tempFile("a", 1)`. -/
def ioFileV (c : Semantics) : GroundTerm := .ctor (symPS c "Lbl'Hash'tempFile") [strV, int 1]
/-- `#ffi_sint`. -/
def ffiTypeV (c : Semantics) : GroundTerm := .ctor (symPS c "Lbl'Hash'ffi'Unds'sint") []
/-- JSON's `null`. -/
def jsonV (c : Semantics) : GroundTerm := .ctor (symPS c "LblJSONnull") []


/-! ## `append` is total -/

/-- The values of sort K are built by `kseq` and `dotk` alone, as decided on the data. -/
def kShapePS (c : Semantics) : Bool :=
  (c.ctorSigs.all fun k => k.result != Srt.k || (k.name == kseq && k.args == [Srt.kitem, Srt.k]) ||
      (k.name == dotk && k.args == [])) &&
    c.ovls.isEmpty && (c.subsorts.all fun p => p.2 != Srt.k) && (c.collOf Srt.k).isNone &&
    c.lib.carrier Srt.k == Srt.k && !(c.lib.tokenSorts.contains Srt.k || c.lib.byteSorts.contains Srt.k)

/-- The values of sort K are `.K` and `KItem ~> K`: the only constructors of result K are `kseq`
of `[KItem, K]` and `dotk` of no argument, no overloading symbol, no open generator, no subsort
of K, no literal of K, no collection sort K. -/
theorem kValue_invPS (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false)
    (hk : kShapePS c = true) :
    ∀ v, c.sortOf v = some Srt.k →
      (∃ x w, v = .ctor kseq [x, w]) ∨ v = .ctor dotk [] := by
  simp only [kShapePS, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, Option.isNone_iff_eq_none, List.isEmpty_iff, Bool.not_eq_true',
    Bool.or_eq_false_iff] at hk
  obtain ⟨⟨⟨⟨⟨hctor, hovl⟩, hsub⟩, hcoll⟩, hcar⟩, htok, hbyte⟩ := hk
  intro v hv
  cases v with
  | ctor f ts =>
    obtain ⟨k, hl, hts, hres⟩ := (c.sortOf_ctor_of_none hovl hr).mp hv
    rw [lookupSig_eq] at hl
    have hmem := List.mem_of_find?_eq_some hl
    have hname : k.name = f := by simpa using List.find?_some hl
    have hlen := Faithful.sortsOf_length hts
    rcases hctor k hmem with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · exact absurd hres.symm h
    · subst hname; rw [h1]; rw [h2] at hlen
      match ts, hlen with
      | [x, w], _ => exact Or.inl ⟨x, w, rfl⟩
    · subst hname; rw [h1]; rw [h2] at hlen
      match ts, hlen with
      | [], _ => exact Or.inr rfl
  | inj a b t =>
    unfold Semantics.sortOf at hv
    split at hv
    · rename_i hc
      injection hv with hb
      subst hb
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      exact absurd rfl (hsub _ hc.1.1)
    · cases hv
  | dv s lit =>
    unfold Semantics.sortOf at hv
    split at hv
    · rename_i hd
      injection hv with hs
      subst hs
      cases lit with
      | int i => simp [dvOK, hcar] at hd
      | bool b => simp [dvOK, hcar] at hd
      | float p e b => simp [dvOK, hcar] at hd
      | tok t =>
        have ht' : Srt.k ∉ c.lib.tokenSorts := fun h => by rw [List.contains_iff_mem.mpr h] at htok; cases htok
        have hb' : Srt.k ∉ c.lib.byteSorts := fun h => by rw [List.contains_iff_mem.mpr h] at hbyte; cases hbyte
        simp [dvOK, hcar, ht', hb'] at hd
    · cases hv
  | map s es =>
    obtain ⟨k, vs, hc, -, -, -, hs⟩ := c.sortOf_map_inv hv
    subst hs; rw [hcoll] at hc; cases hc
  | set s es =>
    obtain ⟨k, -, hc, -⟩ := KK.sortOf_set_inv_kkc hv
    have hs : s = Srt.k := by
      unfold Semantics.sortOf at hv; rw [hc] at hv
      split at hv <;> (try split at hv) <;> (try cases hv) <;> rfl
    subst hs; rw [hcoll] at hc; cases hc
  | list s es =>
    obtain ⟨k, -, hc, -⟩ := KK.sortOf_list_inv_kkc hv
    have hs : s = Srt.k := by
      unfold Semantics.sortOf at hv; rw [hc] at hv
      split at hv <;> (try split at hv) <;> (try cases hv) <;> rfl
    subst hs; rw [hcoll] at hc; cases hc

/-- A function is total when some covering row matches each argument list of its sorts (in place
of the decider `covers`), its right-hand sides are total over `tot`, whose functions but itself are
total, its self calls decrease and it has no `ensures`: `total_of_totalOK`'s argument, by induction
on the size of the decreasing argument. -/
theorem total_of_rowsPS {c : Semantics} (hpreTop : c.clausesPreTop = true) (hok : c.sortedOK = true)
    (hsr : c.srReady = true) (hov : c.OvlCase) (hrh : c.RightHeld)
    (hterm : ∀ g, Terminates c g) {fn : Fn} (hfnc : fn ∈ c.fns) (hs : c.shapesOK = true)
    {dec : Option Nat} (hdec : decreasingOK c fn dec = true)
    (hrows : ∀ vs, c.sortsOf vs = some fn.args → ∃ r ∈ Semantics.coverRows fn, RowMatches c r vs)
    {tot : List Sym} (hrhs : ∀ cl ∈ fn.clauses, c.totalTerm tot cl.rhs = true)
    (hnoens : ∀ cl ∈ fn.clauses, cl.ens = none)
    (htot : ∀ g ∈ tot, g ≠ fn.label → Total c g) : Total c fn.label := by
  have hcA := evalCtx_of_all (hpreTop := hpreTop) hok hsr hov hrh
  have hc := hcA.toN
  have hfn : fn ∈ c.allFns := List.mem_append_left _ hfnc
  have hb : c.HeldFn fn := hcA.binds fn hfn
  have hclk : ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ cl.pre = .top := by
    intro cl hcl
    have hfok : ∀ cl ∈ fn.clauses, c.clauseSorted fn (c.fns.map Fn.sig) cl = true := by
      have hok' := Semantics.sortedOK_sorted hok
      simp only [Bool.and_eq_true, List.all_eq_true] at hok'
      exact hok'.1.2 fn hfnc
    have := hfok cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact ⟨sortsOfTerms_all_of_nf this.1.1.1.1.1, Semantics.clausesPreTop_spec hpreTop hfnc hcl⟩
  have hlook := lookupFn_of_memN hc hfn
  obtain ⟨L, hL, hrs⟩ := hc.sort.fns fn hfn
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ m vs, c.sortsOf vs = some fn.args → decMeasure dec vs < m →
      ∃ v, Eval c fn.label vs (some v) from h _ vs hvs (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro vs hvs hlt
    refine eval_defined hlook (hc.plain fn hfn) hb (fun cl hcl σ hσ _ => ⟨fun t ht => req_resultN hc hterm hfn hcl hσ ht, true,
        Clause.holds_preTop (hclk cl hcl).2 σ⟩)
      (fun cl hcl σ ha => ?_) ?_ hnoens
    · refine evalTerm_defined hc.sort hs hL ((wellSortedAt_univ (hc.plain fn hfn cl hcl).1).mp ha.1) cl.rhs (hrs cl hcl) (hrhs cl hcl)
        fun g ts hts hgt gfn hg vs' hts' hsrt => ?_
      by_cases hgl : g = fn.label
      · subst hgl
        rw [hlook] at hg
        cases hg
        obtain ⟨i, j, p, rfl, hti, hpi, hsi⟩ := decreasingOK_clause hdec hcl (Or.inl rfl) hts
        obtain ⟨v, hvi, hpv⟩ := patVals_get ha.2.1 hpi
        obtain ⟨w, hw, hwv⟩ := strictlyIn_size p hpv hsi
        have hvi' : vs'[i]? = some w := (evalTerms_var hts' hti (allSome_map_some vs')).trans hw
        refine ih vs' hsrt ?_
        have h1 : decMeasure (some i) vs' = w.size := by simp [decMeasure, hvi']
        have h2 : decMeasure (some i) vs = v.size := by simp [decMeasure, hvi]
        omega
      · exact htot g (List.contains_iff_mem.mp hgt) hgl gfn hg vs' hsrt
    · obtain ⟨r, hr, hm⟩ := hrows vs hvs
      obtain ⟨cl, hcl, hreq, hnd, rfl⟩ := mem_coverRows hr
      exact ⟨cl, hcl, hreq, applies_of_rowRH (hb cl hcl) (hclk cl hcl).1 hreq (hclk cl hcl).2 hnd hvs hm⟩

/-- A covering row `kseq(X, Y), Z`. -/
def rowKseqPS : List Term → Bool
  | [.app f [.var _, .var _], .var _] => f == kseq
  | _ => false

/-- A covering row `.K, Z`. -/
def rowDotkPS : List Term → Bool
  | [.app f [], .var _] => f == dotk
  | _ => false

theorem rowKseq_eqPS : ∀ {r : List Term}, rowKseqPS r = true →
    ∃ i j l, r = [.app kseq [.var i, .var j], .var l]
  | [.app f [.var i, .var j], .var l], h => by
    simp only [rowKseqPS, beq_iff_eq] at h; subst h; exact ⟨i, j, l, rfl⟩
  | [], h | [_], h | _ :: _ :: _ :: _, h => by simp [rowKseqPS] at h
  | [.var _, _], h | [.inj _ _ _, _], h | [.as _ _, _], h | [.dv _ _, _], h => by simp [rowKseqPS] at h
  | [.app _ _, .app _ _], h | [.app _ _, .inj _ _ _], h | [.app _ _, .as _ _], h
  | [.app _ _, .dv _ _], h => by simp [rowKseqPS] at h
  | [.app _ [], .var _], h | [.app _ [_], .var _], h | [.app _ (_ :: _ :: _ :: _), .var _], h => by
    simp [rowKseqPS] at h
  | [.app _ [.app _ _, _], .var _], h | [.app _ [.inj _ _ _, _], .var _], h
  | [.app _ [.as _ _, _], .var _], h | [.app _ [.dv _ _, _], .var _], h => by simp [rowKseqPS] at h
  | [.app _ [.var _, .app _ _], .var _], h | [.app _ [.var _, .inj _ _ _], .var _], h
  | [.app _ [.var _, .as _ _], .var _], h | [.app _ [.var _, .dv _ _], .var _], h => by
    simp [rowKseqPS] at h

theorem rowDotk_eqPS : ∀ {r : List Term}, rowDotkPS r = true → ∃ l, r = [.app dotk [], .var l]
  | [.app f [], .var l], h => by
    simp only [rowDotkPS, beq_iff_eq] at h; subst h; exact ⟨l, rfl⟩
  | [], h | [_], h | _ :: _ :: _ :: _, h => by simp [rowDotkPS] at h
  | [.var _, _], h | [.inj _ _ _, _], h | [.as _ _, _], h | [.dv _ _, _], h => by simp [rowDotkPS] at h
  | [.app _ _, .app _ _], h | [.app _ _, .inj _ _ _], h | [.app _ _, .as _ _], h
  | [.app _ _, .dv _ _], h => by simp [rowDotkPS] at h
  | [.app _ (_ :: _), .var _], h => by simp [rowDotkPS] at h

/-- Some covering row of a function of two K arguments matches each argument list of its sorts,
where its rows hold `kseq(X, Y), Z` and `.K, Z` and the values of K are `kseq` and `dotk` terms. -/
theorem rows_appendPS {c : Semantics} (hr : ∀ k ∈ c.params, k.raw = false) (hk : kShapePS c = true)
    (hks : c.isCtor kseq = true) (hdk : c.isCtor dotk = true) {fn : Fn} (hargs : fn.args = [Srt.k, Srt.k])
    (h1 : (Semantics.coverRows fn).any rowKseqPS = true) (h2 : (Semantics.coverRows fn).any rowDotkPS = true) :
    ∀ vs, c.sortsOf vs = some fn.args → ∃ r ∈ Semantics.coverRows fn, RowMatches c r vs := by
  intro vs hvs
  rw [hargs] at hvs
  have hlen := Faithful.sortsOf_length hvs
  match vs, hlen with
  | [v₁, v₂], _ =>
    obtain ⟨s₁, ss, hv₁, -, he⟩ := sortsOf_cons.mp hvs
    injection he with hs₁
    rcases kValue_invPS c hr hk v₁ (hs₁ ▸ hv₁) with ⟨x, w, rfl⟩ | rfl
    · obtain ⟨r, hr, hrk⟩ := List.any_eq_true.mp h1
      obtain ⟨i, j, l, rfl⟩ := rowKseq_eqPS hrk
      exact ⟨_, hr, .cons (.ctor hks (.cons .var (.cons .var .nil))) (.cons .var .nil)⟩
    · obtain ⟨r, hr, hrk⟩ := List.any_eq_true.mp h2
      obtain ⟨l, rfl⟩ := rowDotk_eqPS hrk
      exact ⟨_, hr, .cons (.ctor hdk .nil) (.cons .var .nil)⟩

kernel_rfl totalTerm_withHooksPS : ∀ (c : Semantics) (H : HookParams) (tot : List Sym) (t : Term),
  (c.withHooks H).totalTerm tot t = c.totalTerm tot t

/-- What `append`'s totality asks of the text, as one decided test: the function numbered `a` takes
two K arguments, its covering rows hold `kseq(X, Y), Z` and `.K, Z`, its self calls decrease in
the first argument, its right-hand sides are total over itself, it has no `ensures`, and the values
of K are `kseq` and `dotk` terms. -/
def appendOKPS (c : Semantics) (a : Sym) : Bool :=
  match c.fns.find? (·.label == a) with
  | some fn => fn.args == [Srt.k, Srt.k] && (Semantics.coverRows fn).any rowKseqPS &&
      (Semantics.coverRows fn).any rowDotkPS && decreasingOK c fn (some 0) &&
      fn.clauses.all (fun cl => c.totalTerm [a] cl.rhs) && fn.clauses.all (·.ens.isNone) &&
      kShapePS c && c.isCtor kseq && c.isCtor dotk && c.shapesOK
  | none => false

/-- **`FnHyp` under every interpretation, with `append`'s totality shown here**: the deciders name
no fact but the totality of `append` (`totalObligationsRP = [a]`), which `total_of_rowsPS` gives from
`appendOKPS`, every function terminating by the deciders' rank. -/
theorem fnHyp_appendPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hrv : c.rightValued = true) (hpre : c.clausesPreTop = true) (hplain : c.plain = true)
    {a : Sym} {ord : List Sym} (h1 : c.rankObligations ord ++ c.decObligationsL = [])
    (h2 : c.totalObligationsRP ord [] = [a]) (h3 : c.agreeObligationsI = [])
    (h4 : c.matchObligationsL = ([] : List (Nat × Nat))) (happ : appendOKPS c a = true)
    (H : HookParams) : FnHyp (c.withHooks H) := by
  have h1' : (c.withHooks H).rankObligations ord ++ (c.withHooks H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1
  have h2' : (c.withHooks H).totalObligationsRP ord [] = [a] :=
    (Semantics.totalObligationsRP_withHooks _ H _ _).trans h2
  have hokH : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c H).trans hok
  have hpreH : (c.withHooks H).clausesPreTop = true := by
    rw [Semantics.clausesPreTop_withHooks]; exact hpre
  obtain ⟨hsorted, -, hha, hp, hids⟩ := Semantics.coreOK_parts hokH
  have hsr := NamesApart.srReady_of hp hids hsorted
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts hokH).2.1) (Semantics.coreOK_ovls hokH)
  have hrh : (c.withHooks H).RightHeld := Semantics.rightHeld_withHooks_of_valued hrv H
  have hterm : ∀ g, Terminates (c.withHooks H) g :=
    terminates_of_rankLN (hpreTop := hpreH) hsorted hsr (Semantics.ovlCase_of_core hokH) ord
      (fun f _ => hrh.heldOwed f) (fun f hf => by rw [h1'] at hf; exact absurd hf List.not_mem_nil)
  have htotA : Total (c.withHooks H) a := by
    unfold appendOKPS at happ
    split at happ
    · rename_i fn hfind
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Option.isNone_iff_eq_none] at happ
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hargs, hk1⟩, hk2⟩, hdec⟩, hrhs⟩, hens⟩, hks⟩, hc1⟩, hc2⟩, hsh⟩ := happ
      have hfn : fn ∈ (c.withHooks H).fns := List.mem_of_find?_eq_some hfind
      have hlab : fn.label = a := by simpa using List.find?_some hfind
      rw [← hlab]
      exact total_of_rowsPS hpreH hsorted hsr (Semantics.ovlCase_of_core hokH) hrh hterm hfn hsh
        (dec := some 0) (show decreasingOK (c.withHooks H) fn (some 0) = true from hdec)
        (rows_appendPS (c := c.withHooks H) hr hks hc1 hc2 hargs hk1 hk2) (tot := [a]) (fun cl hcl => (totalTerm_withHooksPS c H [a] cl.rhs).trans (hrhs cl hcl)) hens
        (fun g hg hne => by
          rw [List.mem_singleton] at hg; exact absurd (hg.trans hlab.symm) hne)
    · cases happ
  have hob : FnObligations (c.withHooks H) ord [] := by
    have h5 : (c.withHooks H).plain = true := (Semantics.plain_withHooks c H).trans hplain
    refine ⟨fun f hf => by rw [h1'] at hf; exact absurd hf List.not_mem_nil,
      fun f hf => by rw [h2', List.mem_singleton] at hf; subst hf; exact htotA,
      fun f hf => by rw [(Det.Semantics.agreeObligationsI_withHooks _ H).trans h3] at hf; exact absurd hf List.not_mem_nil,
      fun p hp => by rw [(Det.Semantics.matchObligationsL_withHooks _ H).trans h4] at hp; exact absurd hp List.not_mem_nil,
      openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts h5).1 r hr))
        (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts h5).2.1 fn hfn cl hcl)),
      openLaws_of_plain (Semantics.plain_parts h5).2.2⟩
  exact fnHyp_withHooks hok (Semantics.rightHeld_of_valued hrv) H ParamsTotal.nil hob hr hpre
/-! ## e6-param-io: K-IO -/

namespace IO6

definition_of defn from "f2-examples/e6-param-io.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's one function owing a fact is `append` (number 385), declared total, which
`fnHyp_appendPS` shows total: `FnHyp` under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_appendPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (a := 385) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem accept_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem close_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem getc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem lock_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'log` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem log_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'log").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'log").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'logToFile` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is the empty K. -/
theorem logToFile_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'logToFile").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'logToFile").sig.name [strV, strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is #tempFile("a", 1). -/
theorem mkstemp_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (ioFileV c))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is 1 (an IOInt). -/
theorem open_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String").sig.name [strV, strV] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem putc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is "a" (an IOString). -/
theorem read_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (ioStrV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem remove_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem seek_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem seekEnd_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem shutdownWrite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1 (a KItem). -/
theorem system_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem tell_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is 1. -/
theorem time_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int").sig.name [] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'trace` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem)) nor that it is the empty K. -/
theorem trace_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'trace").sig.name [kint 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'trace").sig.name [kint 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'traceK` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is the empty K. -/
theorem traceK_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'traceK").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'traceK").sig.name [kDot] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem unlock_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, "a") nor that it is the empty K. -/
theorem write_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String").sig.name [int 1, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String").sig.name [int 1, strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end IO6

/-! ## e6-param-ffi: FFI -/

namespace FFI6

definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's one function owing a fact is `append` (number 412), declared total, which
`fnHyp_appendPS` shows total: `FnHyp` under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_appendPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (a := 412) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is 1. -/
theorem bytesAddress_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem), 1, 1) nor that it is b"a". -/
theorem alloc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int").sig.name [kint 1, int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int").sig.name [kint 1, int 1, int 1] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, ListItem(1), ListItem(1), ListItem(1), #ffi_sint) nor that it is b"a". -/
theorem ffiCallVariadic_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, listV, ffiTypeV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, listV, ffiTypeV c] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, ListItem(1), ListItem(1), #ffi_sint) nor that it is b"a". -/
theorem ffiCall_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, ffiTypeV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, ffiTypeV c] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem)) nor that it is the empty K. -/
theorem free_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem").sig.name [kint 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem").sig.name [kint 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1. -/
theorem functionAddress_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, b"a") nor that it is the empty K. -/
theorem nativeRead_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, b"a") nor that it is the empty K. -/
theorem nativeWrite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end FFI6

/-! ## e6-param-kreflection: K-REFLECTION -/

namespace KReflection6

definition_of defn from "f2-examples/e6-param-kreflection.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's one function owing a fact is `append` (number 386), declared total, which
`fnHyp_appendPS` shows total: `FnHyp` under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_appendPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (a := 386) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is ListItem(1). -/
theorem argv_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List").sig.name [] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem configuration_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1 (a KItem). -/
theorem fresh_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem getenv_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is "a". -/
theorem kompiledDirectory_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String").sig.name [] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is "a". -/
theorem sort_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is 1 (a KItem). -/
theorem getsymbol_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end KReflection6

/-! ## e6-param-timer: TIMER -/

namespace Timer6

definition_of defn from "f2-examples/e6-param-timer.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's one function owing a fact is `append` (number 385), declared total, which
`fnHyp_appendPS` shows total: `FnHyp` under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_appendPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (a := 385) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) H

/-- **`LbltimerStart'LParRParUnds'TIMER'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem timerStart_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStart'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStart'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbltimerStop'LParRParUnds'TIMER'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem timerStop_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStop'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStop'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end Timer6

/-! ## e6-param-unification: UNIFICATION -/

namespace Unification6

definition_of defn from "f2-examples/e6-param-unification.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's one function owing a fact is `append` (number 386), declared total, which
`fnHyp_appendPS` shows total: `FnHyp` under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_appendPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (a := 386) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is SetItem(1). -/
theorem metaKVariables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is the empty K. -/
theorem renameVariables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K, the empty K) nor that it is true. -/
theorem unifiable_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K").sig.name [kDot, kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K").sig.name [kDot, kDot] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is SetItem(1). -/
theorem variables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is 1 (a KItem). -/
theorem variablesMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end Unification6

/-! ## e6-param-json: JSON -/

namespace JSON6

definition_of defn from "f2-examples/e6-param-json.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPS c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblJSON2String` is not determined by the text**: over all H, Γ entails neither that it has
no value at (null) nor that it is "a". -/
theorem jSON2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblJSON2String").sig.name [jsonV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblJSON2String").sig.name [jsonV c] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2JSON` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is null. -/
theorem string2JSON_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblString2JSON").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblString2JSON").sig.name [strV] ≡ den (c.withHooks H) (jsonV c))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end JSON6

end KCore.ParamE6Sys

/-- info: 'KCore.ParamE6Sys.IO6.accept_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.accept_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.close_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.close_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.getc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.getc_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.lock_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.lock_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.log_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.log_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.logToFile_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.logToFile_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.mkstemp_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.mkstemp_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.open_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.open_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.putc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.putc_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.read_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.read_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.remove_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.remove_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.seek_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.seek_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.seekEnd_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.seekEnd_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.shutdownWrite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.shutdownWrite_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.system_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.system_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.tell_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.tell_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.time_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.time_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.trace_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.trace_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.traceK_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.traceK_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.unlock_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.unlock_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.write_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.write_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.bytesAddress_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.bytesAddress_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.alloc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.alloc_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.ffiCallVariadic_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.ffiCallVariadic_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.ffiCall_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.ffiCall_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.free_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.free_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.functionAddress_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.functionAddress_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.nativeRead_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.nativeRead_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.nativeWrite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.nativeWrite_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.argv_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.argv_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.configuration_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.configuration_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.fresh_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.fresh_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.getenv_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.getenv_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.kompiledDirectory_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.kompiledDirectory_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.sort_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.sort_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.getsymbol_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.getsymbol_undetermined
/-- info: 'KCore.ParamE6Sys.Timer6.timerStart_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Timer6.timerStart_undetermined
/-- info: 'KCore.ParamE6Sys.Timer6.timerStop_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Timer6.timerStop_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.metaKVariables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.metaKVariables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.renameVariables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.renameVariables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.unifiable_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.unifiable_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.variables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.variables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.variablesMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.variablesMap_undetermined
/-- info: 'KCore.ParamE6Sys.JSON6.jSON2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.JSON6.jSON2String_undetermined
/-- info: 'KCore.ParamE6Sys.JSON6.string2JSON_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.JSON6.string2JSON_undetermined
