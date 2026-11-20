/-
  KCore, checked layer: the interpretations of the parameter symbols that are total where the text
  declares them total.

  A parameter symbol that no registry hook implements (`ParamSig.impl = none`) means what the
  interpretation H says (`Semantics.hooks`, `paramVal`). Under `HookParams.none` it has no value
  anywhere, so a `[total]` function that calls it is not total there. The text declares some of
  these symbols `total` (or `functional`): K's `_&Int_`, `lengthBytes`, `.Bytes`. The statements
  of a definition with parameters are about the interpretations that give each of those a value
  of its result sort at every argument list of its argument sorts (`ParamsTotal`); a parameter the
  text does not declare total may be undefined anywhere, and a function through it stays named.

  - `Definition.totalParams d`: the parameter symbols no registry hook implements that the text
    declares total: the imported modules' (`BModule.totals`, the symbols kompile writes a
    functional axiom for) and the definition's own (`ParamPres.total`, read from the
    `total`/`functional` attribute), but the open generators (`ParamSig.raw`), whose totality is
    the obligation `OpenTotal`.
  - `ParamsTotal c tp H`: H gives each parameter of `c` named in `tp` that no registry hook
    implements a value of its result sort at every argument list of its argument sorts.
  - `totalParam c tp f`: f is such a parameter named in `tp`; `paramVal_of_total`: its value under
    an interpretation total on it. TotalsG.lean admits these in the right-hand sides of `[total]`
    functions (`totalOKP`, `totals_of_rankP`).
  - `FallbackTotal c H`: H gives the interpreted symbols the text declares total a value at their
    silent points; `RestTotal c H`: H gives each `[total]` function a value of its result sort at
    every argument list of its sorts, its rest where every clause fails (`eval_rest_of_restTotal`;
    a `[total]` function with no equation is then total, `total_of_restTotal_nil`).
  - `Semantics.silentTotal c`: the interpretation gives a value at every silent point of an
    interpreted symbol the text declares `total` (`totalSilentKeys`); the interpretations the text
    admits meet it. `HookParams.totals` does in every semantics (`silentTotal_totals`), and under it
    such a symbol has a value at every argument list of its sorts (`total_hook_value`).
  - `Semantics.floatShapeOK c`: every value of sort Float is a Float literal (`shape_float`); then
    `isNaN`, `precisionFloat` and `exponentBitsFloat` (`floatLitTotal`) have a value at every Float
    (`fmt_total`), the third case of `total_hook_value`.
-/
import KcoreSpec.CallRank

set_option autoImplicit false

namespace KCore

/-- The parameter symbols no registry hook implements that the text declares total (`total` or
`functional`): the imported modules' (the symbols kompile writes a functional axiom for) and the
definition's own, in the order of `params`; the open generators (`raw`) left out: their
`functional` sentence is `OpenTotal`, which reads the sort at the interpretation's values. -/
def Definition.totalParams (d : Definition) : List Sym :=
  let declared := ((importsOf d.pres.imports).flatMap (·.totals)).map (·.name) ++
    ((withPres (d.sem.params.filter fun k => decide (nRegSyms ≤ k.sig.name)) d.pres.params).filter
      (·.2.total)).map (·.1.sig.name)
  (d.sem.params.filter fun k => k.impl.isNone && !k.raw && declared.contains k.sig.name).map (·.sig.name)

/-- **H is total on the parameters `tp`**: each parameter symbol of `c` named in `tp` that no
registry hook implements has, under H, a value of its declared result sort at every argument list
of its declared argument sorts. -/
def ParamsTotal (c : Semantics) (tp : List Sym) (H : HookParams) : Prop :=
  ∀ k ∈ c.params, k.impl = none → k.sig.name ∈ tp → ∀ vs, c.sortsOf vs = some k.sig.args →
    ∃ v, H.app k.sig.name vs = some v ∧ c.sortOf v = some k.sig.result

theorem ParamsTotal.nil {c : Semantics} {H : HookParams} : ParamsTotal c [] H :=
  fun _ _ _ h => absurd h List.not_mem_nil

/-- The sorts of a list of values are the same under every interpretation where no parameter is an
open generator (`raw`): there they are the tables' (`sortsOfT_tables`), which hold no
interpretation. -/
theorem Semantics.sortsOf_withHooks :
  ∀ (c : Semantics) (H : HookParams) (_hr : ∀ k ∈ c.params, k.raw = false),
    (c.withHooks H).sortsOf = c.sortsOf := fun c H hr =>
  funext fun ts =>
    (sortsOfT_tables (c.withHooks H) ts (Semantics.rawFreeList_of_noRaw (c := c.withHooks H) hr ts)).symm.trans
      ((congrArg (fun T => sortsOfT T c.lib ts) (tables_withHooks c H)).trans
        (sortsOfT_tables c ts (Semantics.rawFreeList_of_noRaw hr ts)))

/-- The hypothesis on H, read for `c.withHooks H` (whose interpretation is H), where no parameter is
an open generator: H's answers are arbitrary values, whose sort is then the same under H. Without
`hr` the statement is false (test/WithHooksRaw.lean, `paramsTotal_withHooks_needs_hr`). -/
theorem ParamsTotal.withHooks {c : Semantics} {tp : List Sym} {H : HookParams} (h : ParamsTotal c tp H)
    (hr : ∀ k ∈ c.params, k.raw = false) :
    ParamsTotal (c.withHooks H) tp (c.withHooks H).hooks := by
  intro k hk hi hn vs hvs
  rw [Semantics.sortsOf_withHooks c H hr] at hvs
  obtain ⟨v, hv, hs⟩ := h k hk hi hn vs hvs
  exact ⟨v, hv, by rw [Semantics.sortOf_withHooks c H hr]; exact hs⟩

namespace Semantics
variable (c : Semantics)

/-- f is a parameter symbol named in `tp` that no registry hook implements (and no interpreted
symbol: those have their meaning). -/
def totalParam (tp : List Sym) (f : Sym) : Bool :=
  !hookSigs.any (·.name == f) && tp.contains f &&
    match c.lookupParam f with
    | some k => k.impl.isNone
    | none => false

end Semantics

variable {c : Semantics}

theorem paramVal_of_total {f : Sym} {k : ParamSig} (hk : c.lookupParam f = some k) (hi : k.impl = none)
    {vs : List GroundTerm} {v : GroundTerm} (hv : c.hooks.app f vs = some v)
    (hs : c.sortOf v = some k.sig.result) : c.paramVal f vs = some v := by
  unfold Semantics.paramVal
  rw [hk]
  simp [hi, hv, Option.filter, hs]

/-! ## The interpreted symbols declared total that have silent points -/

/-- The interpreted symbols the text declares `total` whose value it leaves open somewhere
(`silentTable`): `substrString` (domains.md 1758), `Bytes2Int` (2082), `Int2Bytes` (2083). -/
def totalSilent : List Sym := [stringSubstr, bytes2Int, int2Bytes]

/-- **H gives the symbols declared total a value where the text gives none**: at every silent point
of a symbol of `totalSilent` whose arguments have its argument sorts, H has a value of its result
sort (`Semantics.fallback`). The text's `total` for these symbols, as a condition on the
interpretation; Γ does not state it. -/
def FallbackTotal (c : Semantics) (H : HookParams) : Prop :=
  ∀ f ∈ totalSilent, ∀ k vs, lookupSig hookSigs f = some k → c.sortsOf vs = some k.args →
    hook f vs = some none → silent f vs = true → ∃ v, (c.withHooks H).fallback f vs = some v

/-- Whether `hook` knows `f` does not depend on the arguments. -/
theorem hook_isSome_args (f : Sym) (vs : List GroundTerm) : (hook f vs).isSome = (hook f []).isSome := by
  unfold hook; cases hookTrie.find f <;> rfl

/-- Every point of a symbol of `totalSilent` is silent. -/
theorem totalSilent_silent : ∀ f ∈ totalSilent, ∀ vs, silent f vs = true := by
  intro f hf vs
  simp only [totalSilent, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

theorem totalSilent_hook : ∀ f ∈ totalSilent, (hook f []).isSome = true := by decide +kernel

/-- **Under `FallbackTotal`, a symbol of `totalSilent` has a value at every argument list of its
argument sorts**: `hook`'s, or at a silent point H's. -/
theorem hookRes_of_fallbackTotal {c : Semantics} {H : HookParams} (h : FallbackTotal c H) {f : Sym}
    (hf : f ∈ totalSilent) {k : CtorSig} (hk : lookupSig hookSigs f = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) : ∃ v, (c.withHooks H).hookRes f vs = some (some v) := by
  have hs := totalSilent_silent f hf vs
  have hh := totalSilent_hook f hf
  rw [← hook_isSome_args f vs] at hh
  cases he : hook f vs with
  | none => rw [he] at hh; cases hh
  | some r =>
    cases r with
    | some v => exact ⟨v, Semantics.hookRes_of_value he⟩
    | none =>
      obtain ⟨v, hv⟩ := h f hf k vs hk hvs he hs
      exact ⟨v, by rw [Semantics.hookRes_of_silent he hs, hv]⟩

/-! ## The functions declared total, where no clause applies -/

/-- **H gives the functions declared total a value where their equations give none**: every
`[total]` function of `c` has, under H, a value of its result sort at every argument list of its
argument sorts, which is its rest (`Semantics.fnRest`) wherever every clause fails. The text's
`total` for a function, as a condition on the interpretation, as `FallbackTotal` is for the
interpreted symbols; Γ does not state it. -/
def RestTotal (c : Semantics) (H : HookParams) : Prop :=
  ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args →
    ∃ v, H.app fn.label vs = some v ∧ c.sortOf v = some fn.result

kernel_rfl Semantics.lookupFn_withHooks :
  ∀ (c : Semantics) (H : HookParams) (f : Sym), (c.withHooks H).lookupFn f = c.lookupFn f

/-- **Under `RestTotal`, a function declared total has a rest at every argument list of its
argument sorts**, where no parameter is an open generator (H's answer then has its sort under H). -/
theorem fnRest_of_restTotal {c : Semantics} {H : HookParams} (h : RestTotal c H) {fn : Fn} (hfn : fn ∈ c.fns)
    (ht : fn.total = true) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    (hr : ∀ k ∈ c.params, k.raw = false) :
    ∃ v, (c.withHooks H).fnRest fn vs = some v := by
  obtain ⟨v, hv, hs⟩ := h fn hfn ht vs hvs
  refine ⟨v, ?_⟩
  unfold Semantics.fnRest
  show (H.app fn.label vs).filter _ = some v
  rw [hv]
  simp [Option.filter, Semantics.sortsOf_withHooks c H hr, Semantics.sortOf_withHooks c H hr, hvs, hs]

/-- **Under `RestTotal`, a function declared total has a value wherever every clause fails**, where
no parameter is an open generator. -/
theorem eval_rest_of_restTotal {c : Semantics} {H : HookParams} (h : RestTotal c H) {fn : Fn}
    (hfn : fn ∈ c.fns) (ht : fn.total = true) (hlook : c.lookupFn fn.label = some fn)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    (hnone : ∀ cl ∈ fn.clauses, Fails (c.withHooks H) vs cl) (hr : ∀ k ∈ c.params, k.raw = false) :
    ∃ v, Eval (c.withHooks H) fn.label vs (some v) := by
  obtain ⟨v, hv⟩ := fnRest_of_restTotal h hfn ht hvs hr
  refine ⟨v, ?_⟩
  rw [← hv]
  exact .rest (by rw [Semantics.lookupFn_withHooks]; exact hlook) hnone

/-- **A function declared total with no equation is total under `RestTotal`**: every argument list
of its sorts is a point where every clause fails, so its value there is its rest. The named fact
`Total c f` of such a function (no decider confirms it: it has no row) holds at every
interpretation satisfying `RestTotal`, where no parameter is an open generator. -/
theorem total_of_restTotal_nil {c : Semantics} {H : HookParams} (h : RestTotal c H) {fn : Fn}
    (hfn : fn ∈ c.fns) (ht : fn.total = true) (hlook : c.lookupFn fn.label = some fn)
    (hnil : fn.clauses = []) (hr : ∀ k ∈ c.params, k.raw = false) : Total (c.withHooks H) fn.label := by
  intro fn' hlook' vs hvs
  rw [Semantics.lookupFn_withHooks, hlook] at hlook'
  cases hlook'
  rw [Semantics.sortsOf_withHooks c H hr] at hvs
  exact eval_rest_of_restTotal h hfn ht hlook hvs (fun cl hcl => by rw [hnil] at hcl; cases hcl) hr

/-! ## The interpretations the text admits: a value at the silent points of a `total` symbol -/

/-- The interpreted symbols with silent points that the builtin text declares `total`: at a silent
point of one, the text states that a value of the result sort exists and not which. domains.md
(K 7.1.337): `substrString` 1758, `Bytes2Int` 2082, `Int2Bytes` 2083, `isInfinite`
1545, `--Float` 1562, `absFloat` 1608, `floorFloat` 1610, `ceilFloat` 1611, `truncFloat` 1612,
`replaceAll` 1852, `countAllOccurrences` 1855
(checked against the builtin text by test/SilentTotal.lean). -/
def totalSilentKeys : List Sym :=
  [stringSubstr, bytes2Int, int2Bytes, floatIsInfinite, floatNeg, floatAbs,
   floatFloor, floatCeil, floatTrunc, stringCountAll, stringReplaceAll]

theorem totalSilentKeys_silent : ∀ f ∈ totalSilentKeys, silentKey f = true := by decide +kernel

theorem totalSilentKeys_hook : ∀ f ∈ totalSilentKeys, (hook f []).isSome = true := by decide +kernel

/-- Every point of a symbol of `totalSilentKeys` is silent (its key is `fun _ => true`). -/
theorem totalSilentKeys_everywhere : ∀ f ∈ totalSilentKeys, ∀ vs, silent f vs = true := by
  intro f hf vs
  simp only [totalSilentKeys, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `totalSilent`'s symbols are among them. -/
theorem totalSilent_sub : ∀ f ∈ totalSilent, f ∈ totalSilentKeys := by decide

/-- **The interpretation gives a value at every silent point of a `total` symbol**: at a silent
point of a symbol of `totalSilentKeys` whose arguments have its argument sorts, `fallback` has a
value (of the result sort). The interpretations the text admits meet it and the library's other
sentences (`Semantics.libAdmitted`, LibAdmitted.lean). Γ does not state it; the statements over Γ
hold for every interpretation, meeting it or not. -/
def Semantics.silentTotal (c : Semantics) : Prop :=
  ∀ k ∈ hookSigs, k.name ∈ totalSilentKeys → ∀ vs, c.sortsOf vs = some k.args →
    hook k.name vs = some none → silent k.name vs = true → (c.fallback k.name vs).isSome = true

/-- `silentTotal` gives `FallbackTotal`, where no parameter is an open generator. -/
theorem fallbackTotal_of_silentTotal {c : Semantics} {H : HookParams} (h : (c.withHooks H).silentTotal)
    (hr : ∀ k ∈ c.params, k.raw = false) : FallbackTotal c H := by
  intro f hf k vs hk hvs hh hs
  obtain ⟨hmem, hname⟩ := lookupSig_spec hk
  subst hname
  have := h k hmem (totalSilent_sub _ hf) vs (by rw [Semantics.sortsOf_withHooks c H hr]; exact hvs) hh hs
  exact Option.isSome_iff_exists.mp this

/-- A value of the result sort of each symbol of `totalSilentKeys`: the argument for a Float result
(each such symbol has one argument, of sort Float), and `false`, `0`, `""`, the empty Bytes for
Bool, Int, String, Bytes. -/
def totalsVal (f : Sym) (vs : List GroundTerm) : Option GroundTerm :=
  match lookupSig hookSigs f with
  | some k =>
    if k.result == Srt.float then vs.head?
    else if k.result == Srt.bool then some (bool false)
    else if k.result == Srt.int then some (int 0)
    else if k.result == Srt.string then some (strV [])
    else if k.result == Srt.bytes then some (bytesV [])
    else none
  | none => none

/-- The interpretation giving each symbol of `totalSilentKeys` the value `totalsVal`, and nothing
elsewhere (`HookParams.none`'s value off those symbols). -/
def HookParams.totals : HookParams :=
  ⟨fun f vs => if totalSilentKeys.contains f then totalsVal f vs else Option.none⟩

/-- The signatures `totalsVal` reads: a Float result of one Float argument, or a Bool, Int, String
or Bytes result. -/
def totalsShape (k : CtorSig) : Bool :=
  (k.result == Srt.float && k.args == [Srt.float]) ||
    [Srt.bool, Srt.int, Srt.string, Srt.bytes].contains k.result

theorem totalSilentKeys_shape : ∀ f ∈ totalSilentKeys, (lookupSig hookSigs f).all totalsShape = true := by
  decide +kernel

theorem totalsVal_sort (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) (hkey : k.name ∈ totalSilentKeys)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args) :
    ∃ v, totalsVal k.name vs = some v ∧ c.sortOf v = some k.result := by
  have hl := hookSigs_lookup k hk
  have hsh := totalSilentKeys_shape _ hkey
  rw [hl] at hsh
  simp only [Option.all_some, totalsShape, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hsh
  unfold totalsVal; rw [hl]
  rcases hsh with ⟨hr, ha⟩ | hr
  · rw [ha] at hvs
    obtain ⟨v, rfl, h1⟩ := sortsOf_one hvs
    exact ⟨v, by simp [hr], by rw [hr]; exact h1⟩
  · simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr <;> rw [hr]
    · exact ⟨bool false, by simp +decide [hr], rfl⟩
    · exact ⟨int 0, by simp +decide [hr], rfl⟩
    · exact ⟨strV [], by simp +decide [hr], rfl⟩
    · refine ⟨bytesV [], by simp +decide [hr], ?_⟩
      show (if dvOK c.lib Srt.bytes (.tok (String.ofList [])) then some Srt.bytes else Option.none) = _
      simp [dvOK]

/-- **`HookParams.totals` meets `silentTotal`**, in every semantics. It is no interpretation the text
admits where the text holds `isInfinite`'s equation (`HookParams.lib`, LibAdmitted.lean, is). -/
theorem silentTotal_totals (c : Semantics) : (c.withHooks HookParams.totals).silentTotal := by
  intro k hk hkey vs hvs _ _
  obtain ⟨v, hv, hs⟩ := totalsVal_sort (c.withHooks HookParams.totals) hk hkey hvs
  unfold Semantics.fallback
  rw [hookSigs_lookup k hk]
  show ((if totalSilentKeys.contains k.name then totalsVal k.name vs else Option.none).filter _).isSome = true
  rw [ite_eq_left_iff.mpr (fun h => absurd (List.contains_iff_mem.mpr hkey) h), hv]
  simp [Option.filter, hs]

/-! ## Float values are Float literals where no other value has sort Float -/

/-- **Every value of sort Float is a Float literal**: no constructor, injection, collection sort of
the definition's own, overloading symbol, token or byte sort, nor raw parameter has Float as its
sort. Then
`precisionFloat` and `exponentBitsFloat`, which read a literal's format, and `isNaN`, which reads
its datum, have a value at every Float (`fmt_total`). -/
def Semantics.floatShapeOK (c : Semantics) : Bool :=
  c.ctorSigs.all (·.result != Srt.float) && c.subsorts.all (·.2 != Srt.float) &&
  !(c.lib.tokenSorts ++ c.lib.byteSorts).contains Srt.float &&
  c.colls.all (·.sort != Srt.float) && c.ovlSigs.all (·.result != Srt.float) &&
  c.params.all (fun k => !(k.raw && k.sig.result == Srt.float))

/-- Float is no collection sort where none of the definition's own has it as its sort. -/
theorem collOf_float {c : Semantics} (hcoll : ∀ k ∈ c.colls, (k.sort != Srt.float) = true) {k : CollSig}
    (h : c.collOf Srt.float = some k) : False := by
  unfold Semantics.collOf Semantics.allColls at h
  rw [List.find?_append] at h
  have hb : builtinColls.find? (·.sort == Srt.float) = none := rfl
  rw [hb, Option.none_or] at h
  have hk := List.mem_of_find?_eq_some h
  have he : k.sort = Srt.float := by simpa using List.find?_some h
  have := hcoll k hk
  rw [he] at this
  exact absurd this (by decide)

/-- **Under `floatShapeOK`, a value of sort Float is a Float literal** (`KFloat.ok`). -/
theorem shape_float {c : Semantics} (h : c.floatShapeOK = true) {v : GroundTerm}
    (hv : c.sortOf v = some Srt.float) : ∃ p e b, v = .dv Srt.float (.float p e b) ∧ KFloat.ok p e b = true := by
  unfold Semantics.floatShapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hctor, hsub⟩, htok⟩, hcoll⟩, hovl⟩, hraw⟩ := h
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, _, he⟩ | ⟨-, o, ho, _, _, he⟩ | ⟨-, -, k, hk, _, _, he⟩
    rotate_right
    · obtain ⟨hm, hr, -, -⟩ := c.lookupOpen_spec hk
      have := hraw k hm
      simp [hr, ← he] at this
    · have := hctor k (lookupSig_spec hk).1
      simp only [bne_iff_ne, ne_eq] at this; exact (this (by first | exact he | exact he.symm)).elim
    · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some ho
      have := hovl _ (List.mem_map_of_mem (f := (·.sig)) hom)
      simp only [bne_iff_ne, ne_eq] at this; exact (this (by first | exact he | exact he.symm)).elim
  | inj a b t =>
    obtain ⟨hab, _, _, he⟩ := sortOf_inj.mp hv
    have := hsub _ hab
    simp only [bne_iff_ne, ne_eq] at this; exact (this (by first | exact he | exact he.symm)).elim
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    cases lit with
    | float p e b =>
      simp only [dvOK, Lib.carrier_int, Lib.carrier_bool, Lib.carrier_float, Lib.carrier_string, Lib.carrier_bytes, Lib.carrier_kconfigVar, Bool.and_eq_true, beq_iff_eq] at hok
      exact ⟨p, e, b, rfl, hok.2⟩
    | tok t =>
      simp only [dvOK, Lib.carrier_int, Lib.carrier_bool, Lib.carrier_float, Lib.carrier_string, Lib.carrier_bytes, Lib.carrier_kconfigVar, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [List.contains_append, Bool.or_eq_false_iff] at htok
      rcases hok with ((h1 | h1) | h1) | ⟨h1 | h1, -⟩
      · exact absurd h1 (by decide)
      · exact absurd h1 (by decide)
      · rw [htok.1] at h1; cases h1
      · exact absurd h1 (by decide)
      · rw [htok.2] at h1; cases h1
    | int i => simp only [dvOK, Lib.carrier_int, Lib.carrier_bool, Lib.carrier_float, Lib.carrier_string, Lib.carrier_bytes, Lib.carrier_kconfigVar, beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, Lib.carrier_int, Lib.carrier_bool, Lib.carrier_float, Lib.carrier_string, Lib.carrier_bytes, Lib.carrier_kconfigVar, beq_iff_eq] at hok; exact absurd hok (by decide)
  | map s' es =>
    obtain ⟨k, _, hk, _, _, _, _, rfl⟩ := sortOf_mapS_fwd hv
    exact (collOf_float hcoll hk).elim
  | set s' es =>
    obtain ⟨k, hk, _, _, _, rfl⟩ := sortOf_setS.mp hv
    exact (collOf_float hcoll hk).elim
  | list s' es =>
    obtain ⟨k, hk, _, _, rfl⟩ := sortOf_listS.mp hv
    exact (collOf_float hcoll hk).elim

/-- A Float literal's format has a positive precision and exponent width. -/
theorem KFloat.ok_pos {p e b : Nat} (h : KFloat.ok p e b = true) : 1 ≤ p ∧ 1 ≤ e := by
  by_cases hpe : 2 ≤ p ∧ 2 ≤ e
  · omega
  · have hs : KFloat.spec? p e = none := by unfold KFloat.spec?; simp [hpe]
    unfold KFloat.ok at h
    rw [hs] at h
    unfold KFloat.thinOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega

/-- **A value of sort Float has a datum, under `floatShapeOK`**: it is a Float literal, of a format
with a model or with a field of 1 (`asDatum`). -/
theorem asDatum_sorted {c : Semantics} (hf : c.floatShapeOK = true) {v : GroundTerm}
    (hv : c.sortOf v = some Srt.float) : ∃ u, asDatum v = some u := by
  obtain ⟨p, e, b, rfl, hok⟩ := shape_float hf hv
  obtain ⟨hp, he⟩ := KFloat.ok_pos hok
  have ht : KFloat.spec? p e = none → KFloat.tnFormat p e = true := by
    intro hs; unfold KFloat.spec? at hs; split at hs
    · cases hs
    · rename_i h; simp only [KFloat.tnFormat, decide_eq_true_eq]; omega
  cases hs : KFloat.spec? p e with
  | some sp => exact ⟨KFloat.unpackBits sp b, by simp [asDatum, hs]⟩
  | none => exact ⟨KFloat.tnUnpack p e b, by simp [asDatum, hs, ht hs]⟩

/-- FLOAT's symbols of one Float that the text declares `total` (domains.md 1544, 1511, 1519) and
that are no key of `silentTable`: `isNaN`, `precisionFloat` and `exponentBitsFloat`. `hook` gives
each a value at every Float literal, and none at a value of sort Float that is no literal, which a
semantics with `floatShapeOK` does not have. -/
def floatLitTotal : List Sym := floatIsNaN :: floatResInt

/-- `isNaN`, `precisionFloat` and `exponentBitsFloat` take one Float. -/
theorem floatLitTotal_args : ∀ k ∈ hookSigs, floatLitTotal.contains k.name = true → k.args = [Srt.float] := by
  decide +kernel

theorem floatLitTotal_notKey : ∀ f ∈ floatLitTotal, silentKey f = false := by decide +kernel

theorem hook_floatPrecision (vs : List GroundTerm) :
    hook floatPrecision vs = some (flFmt (fun (p _ : Nat) => (p : Int)) vs) := rfl

theorem hook_floatExponentBits (vs : List GroundTerm) :
    hook floatExponentBits vs = some (flFmt (fun (_ e : Nat) => (e : Int)) vs) := rfl

/-- **`isNaN`, `precisionFloat` and `exponentBitsFloat` have a value at every Float, under
`floatShapeOK`**: `hook`'s, whether the literal's datum is Not-a-Number, and the literal's precision
or exponent width. -/
theorem fmt_total {c : Semantics} (h : c.floatShapeOK = true) {f : Sym} (hf : f ∈ floatLitTotal)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some [Srt.float]) : ∃ w, hook f vs = some (some w) := by
  obtain ⟨v, rfl, hv⟩ := sortsOf_one hvs
  simp only [floatLitTotal, floatResInt, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · obtain ⟨u, hu⟩ := asDatum_sorted h hv
    have hh : hook floatIsNaN [v] = some (flTest KFloat.isNaN [v]) := rfl
    exact ⟨bool (KFloat.isNaN u), by rw [hh]; simp [flTest, hu]⟩
  · obtain ⟨p, e, b, rfl, hok⟩ := shape_float h hv
    have hpe := KFloat.ok_pos hok
    exact ⟨int p, by rw [hook_floatPrecision]; simp [flFmt, hpe.1, hpe.2]⟩
  · obtain ⟨p, e, b, rfl, hok⟩ := shape_float h hv
    have hpe := KFloat.ok_pos hok
    exact ⟨int e, by rw [hook_floatExponentBits]; simp [flFmt, hpe.1, hpe.2]⟩

/-- **A symbol the text declares `total` has a value at every argument list of its sorts, under an
interpretation the text admits**: off `partialHooks` `hook`'s (`hook_total`, where the sorts
interpreted symbols read have their shapes), on `totalSilentKeys` `hook`'s or, at a silent point,
the interpretation's, and `isNaN`, `precisionFloat`, `exponentBitsFloat` (`floatLitTotal`) `hook`'s where every
Float value is a Float literal (`fmt_total`). Every interpreted symbol the text declares `total` is
one of the three (test/SilentTotal.lean). -/
theorem total_hook_value {c : Semantics} (hs : c.shapesOK = true) (ht : c.silentTotal) {k : CtorSig}
    (hk : k ∈ hookSigs) (hkind : partialHooks.contains k.name = false ∨ k.name ∈ totalSilentKeys ∨
      (k.name ∈ floatLitTotal ∧ c.floatShapeOK = true))
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args) :
    ∃ v, c.hookRes k.name vs = some (some v) := by
  rcases hkind with hp | hkey | ⟨hf, hfs⟩
  · obtain ⟨v, hv⟩ := hook_total hs k hk hp vs hvs
    exact ⟨v, Semantics.hookRes_of_value hv⟩
  · have hh := totalSilentKeys_hook _ hkey
    rw [← hook_isSome_args k.name vs] at hh
    have hsil := totalSilentKeys_everywhere _ hkey vs
    cases he : hook k.name vs with
    | none => rw [he] at hh; cases hh
    | some r =>
      cases r with
      | some v => exact ⟨v, Semantics.hookRes_of_value he⟩
      | none =>
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht k hk hkey vs hvs he hsil)
        exact ⟨v, by rw [Semantics.hookRes_of_silent he hsil, hv]⟩
  · rw [floatLitTotal_args k hk (List.contains_iff_mem.mpr hf)] at hvs
    obtain ⟨w, hw⟩ := fmt_total hfs hf hvs
    exact ⟨w, Semantics.hookRes_of_value hw⟩

end KCore
