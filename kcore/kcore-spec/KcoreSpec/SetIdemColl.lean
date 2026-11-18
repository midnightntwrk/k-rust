/-
  KCore. The idempotence sentence of a set collection, `\equals{S, R}(concat(K, K), K)`, has no
  model with `Γ` where the collection's key sort has a value.

  Take a value `w` of the key sort and the one-member set `{w}`, and let `x` be its element. `Γ`
  gives `x` as `elem(⟦w⟧)` (`ΓDomains`: a value's KORE denotes one element, and the one-member
  set's KORE is `elem` applied to its member's). The sentence at `K = x` says `concat(x, x)` holds
  `x`. Then `x` is in both `elem(⟦w⟧)` and `concat(elem(⟦w⟧), x)`, so `setElemAtomAx` (`ΓColls`)
  makes `x` the unit's element, which `setElemNotUnitAx` (`ΓColls`) denies of an element. The
  sorts and definedness the sentence's translation is read with are `ΓSig`'s. Nothing here reads
  a hook's graph: the collection may be the library's `Set` or a definition's own set collection,
  whose symbols are parameters (`setColl_idem_false`). The sentence as the text writes it,
  translated, is read by `setColl_idem_refuted`; `setColl_idem_refuted_text` takes its shape and
  the collection's facts as one decision (`setIdemTextOK`), for every interpretation of the
  parameters.

  The key value is needed: where the key sort has no element, the sort of the collection may hold
  the unit's element alone, with `concat(unit, unit) = unit`, and the sentence holds.
-/
import KcoreSpec.FaithfulCollPat
import KcoreSpec.Inhabited

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A set collection's concatenation is not idempotent in a model of `Γ`** at the element of a
one-member set: with `x` the element of `{w}`, for `w` a value of the key sort, `concat(x, x)` does
not hold `x`. -/
theorem setColl_idem_false [OvlOK c] (hI : I ⊧ᴵP Γ c) {k : CollSig} (hk : k ∈ c.allColls)
    (hkind : k.kind = .set) (hco : c.collOf k.sort = some k) {w : GroundTerm} (hw : c.sortOf w = some k.key)
    (hidem : SymE I (c.symName k.concat) [elemOf c I (.set k.sort [w]), elemOf c I (.set k.sort [w])]
      (elemOf c I (.set k.sort [w]))) : False := by
  have hD := defOK hI
  have hC : I ⊧ᴵP ΓColls c := sat_colls hI
  have h1 : c.sortOf (.set k.sort [w]) = some k.sort :=
    (sortOf_setK hco hkind).mpr ⟨rfl, fun e he => by rw [mem_one he]; exact hw⟩
  have hxe : SymE I (c.symName k.elem) [elemOf c I w] (elemOf c I (.set k.sort [w])) := by
    have hx := (den_sing hI h1 KoreAML.val0 _).mpr rfl
    rw [den_setOneK_eq hco] at hx
    exact (interp_symList _ _ [elemOf c I w] (.cons (den_sing hI hw _) .nil) _).mp hx
  have ha : InS I (c.sortName k.key) (elemOf c I w) := (elemOf_spec hI hw KoreAML.val0).2
  have hx : InS I (c.sortName k.sort) (elemOf c I (.set k.sort [w])) := (elemOf_spec hI h1 KoreAML.val0).2
  obtain ⟨-, hu⟩ := axS_elemAtom hD hC hk hkind ha ha hx hxe ⟨_, hxe, hidem⟩
  exact axS_elemNotUnit hD hC hk hkind ha hu hxe

/-- The variable `n:S` of a set collection's idempotence sentence, `S` the collection's sort. -/
def setIdemVar (c : Semantics) (k : CollSig) (n : String) : Kore.Pattern :=
  KoreAML.ev n (KoreAML.srt (c.sortName k.sort))

/-- The idempotence sentence's pattern, `\equals{S, R}(concat(n, n), n)`, the concatenation applied
as the translation of a term applies it (`symApp`). -/
def setIdemPat (c : Semantics) (k : CollSig) (n : String) : Kore.Pattern :=
  .equals (srtOf c k.sort) KoreAML.R (symApp c k.concat [setIdemVar c k n, setIdemVar c k n]) (setIdemVar c k n)

/-- **The idempotence sentence of a set collection, translated as written, has no model with `Γ`**
where the key sort has a value `w`: the sentence at the element of `{w}` gives `concat(x, x) ∋ x`,
which `setColl_idem_false` refutes. The sentence's shape (`hpat`), its variables (`hvars`), its
sort (`hsort`) and the translation's table (`hR`, `hK`) are the tie's kernel decisions. -/
theorem setColl_idem_refuted [OvlOK c] (hI : I ⊧ᴵP Γ c) {k : CollSig} (hk : k ∈ c.allColls)
    (hkind : k.kind = .set) (hco : c.collOf k.sort = some k) {w : GroundTerm} (hw : c.sortOf w = some k.key)
    (hnum : k.sort < nRegSorts + c.sortNames.length) (hite : iteSort? (c.symName k.concat) = none)
    {ad : KoreAML.AxiomDecl} {n : String}
    (hpat : ad.ax.pattern = setIdemPat c k n)
    (hvars : (ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups =
      [.sortVar "R", .evar n (KoreAML.srt (c.sortName k.sort))])
    (hsort : KoreAML.sortOf [] ad.ax.pattern = some KoreAML.R)
    (hR : KoreAML.VarKey.sortVar "R" ∈ KoreAML.tableOf ad.ax.sortVars ad.ax.pattern)
    (hK : KoreAML.VarKey.evar n (KoreAML.srt (c.sortName k.sort)) ∈ KoreAML.tableOf ad.ax.sortVars ad.ax.pattern)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) : False := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have h1 : c.sortOf (.set k.sort [w]) = some k.sort :=
    (sortOf_setK hco hkind).mpr ⟨rfl, fun e he => by rw [mem_one he]; exact hw⟩
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI hnum
  have hesort := (elemOf_spec hI h1 KoreAML.val0).2
  let x := elemOf c I (.set k.sort [w])
  have hx : KoreAML.Inh I σS x := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf ad.ax.sortVars ad.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => x
  let e' : Valuation M := valOf tbl val
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hR]
  have hKv : e'.evalEvar (tbl.ev (.evar n (KoreAML.srt (c.sortName k.sort)))) = x := valOf_ev hK
  have hg : ∀ v ∈ (ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl v).interpret I e' m := by
    intro v hv m
    rw [hvars] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hR]
      exact hσS2
    · rw [List.mem_singleton.mp hv, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg x).mpr (by
    rw [hsort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' x
    rw [KoreAML.interp_inhOf_of hRv]; exact hx)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (setIdemPat c k n)).interpret I e' x := by
    have := hP; simp only [tbl] at this ⊢; rw [hpat] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c k.sort)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [trSort_srt]; exact hσS1 b
  unfold setIdemPat at hP
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hKx : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (setIdemVar c k n)).interpret I e' b ↔ b = x := fun b => by
    unfold setIdemVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar n (KoreAML.srt (c.sortName k.sort)))) ↔ b = x
    rw [hKv]
  have happ := (hall x hx).mpr ((hKx x).mpr rfl)
  have hhead : symHead c k.concat = KoreAML.sym (.symbol (c.symName k.concat)) := by
    unfold symHead; rw [hite]
  rw [tr_symApp, trArgs_appList, hhead] at happ
  exact setColl_idem_false hI hk hkind hco hw
    ((interp_symList _ _ [x, x] (.cons hKx (.cons hKx .nil)) x).mp happ)

end

/-- The set collection of `c` whose concatenation symbol is named `f`. -/
def setCollOfConcat? (c : Semantics) (f : String) : Option CollSig :=
  c.allColls.find? fun k => decide (k.kind = .set) && c.symName k.concat == f

/-- What `setColl_idem_refuted` asks of the sentence `ad` and the set collection `k`, as one
decision: `k` is a set collection of `c`, the search exhibits a value of its key sort
(`Parse.exhibit?`), its sort is numbered and its concatenation applied plainly, and `ad` is the
idempotence sentence of `k` over the variable `n`, with its variables, sort and table. -/
def setIdemOK (c : Semantics) (k : CollSig) (n : String) (ad : KoreAML.AxiomDecl) : Bool :=
  decide (k ∈ c.allColls) && decide (k.kind = .set) && decide (c.collOf k.sort = some k) &&
  (Parse.exhibit? c k.key).isSome && decide (k.sort < nRegSorts + c.sortNames.length) &&
  decide (iteSort? (c.symName k.concat) = none) && decide (ad.ax.pattern = setIdemPat c k n) &&
  decide ((ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups =
    [.sortVar "R", .evar n (KoreAML.srt (c.sortName k.sort))]) &&
  decide (KoreAML.sortOf [] ad.ax.pattern = some KoreAML.R) &&
  decide (KoreAML.VarKey.sortVar "R" ∈ KoreAML.tableOf ad.ax.sortVars ad.ax.pattern) &&
  decide (KoreAML.VarKey.evar n (KoreAML.srt (c.sortName k.sort)) ∈ KoreAML.tableOf ad.ax.sortVars ad.ax.pattern)

/-- `setIdemOK` at the set collection whose concatenation is named `f`. -/
def setIdemTextOK (c : Semantics) (f n : String) (ad : KoreAML.AxiomDecl) : Bool :=
  match setCollOfConcat? c f with
  | some k => setIdemOK c k n ad
  | none => false

/-- **The idempotence sentence `ad` of a set collection of `c`, translated, has no model with `Γ`,
for every interpretation of the parameters** where `setIdemTextOK` decides its shape: the
exhibited key value is a value at every interpretation (`sortOf_withHooks_of_exhibit`), and the
collections, names and sorts `setIdemOK` reads are those of `c.withHooks H`. -/
theorem setColl_idem_refuted_text (c : Semantics) (H : HookParams) [OvlOK (c.withHooks H)] {f n : String}
    {ad : KoreAML.AxiomDecl} (hok : setIdemTextOK c f n ad = true) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (c.withHooks H) → ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := by
  intro M _ I hI hax
  unfold setIdemTextOK at hok
  split at hok
  · rename_i k _
    simp only [setIdemOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hkind⟩, hco⟩, hex⟩, hnum⟩, hite⟩, hpat⟩, hvars⟩, hsort⟩, hR⟩, hK⟩ := hok
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hex
    exact setColl_idem_refuted (c := c.withHooks H) hI hk hkind hco (sortOf_withHooks_of_exhibit hw H) hnum
      hite hpat hvars hsort hR hK hax
  · exact absurd hok (by simp)

end Faithful

end KCore
