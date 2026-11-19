/-
  `GenEqs.freeB` by the names of the theory: `freeB c ks` holds exactly where no symbol of `ks` has
  one of the names `freeBlockNames c` (`freeB_iff_blockNames`). Those names are computed from `c`
  alone, so a check of `freeB` at many symbol lists of one semantics reads them once
  (`freeBIdx`, `freeBIdx_eq`): one look-up per symbol, whatever the size of the theory.

  The names are, conjunct by conjunct of `freeB` (at no sort, every sort check holds):
  - the symbols of the patterns `listsB` reads (`listNamesFB`): the signature's items, the
    constructor, function and rule items, the step's closure, the collections' no-junk items and
    axioms, `boolClosed`. A signature item may be the arity of a hook of `ks` (`regSig`), but no
    hook has the name of a symbol of `ks` where the last conjunct holds, so that exception never
    applies;
  - the symbols that build values (`valuesB`): constructors, overloading symbols, parameter
    symbols, the collections' unit, element and concatenation, and the injection;
  - the head `symApp` writes for a symbol applied at values (`graphsB`, `appOK`: `Lblite` for an
    `ite` instance, the symbol's own name otherwise), for the hooks, parameters and functions;
  - the names of the interpreted hooked symbols (the last conjunct).
-/
import Std.Data.HashSet
import KcoreSpec.DetachedB

set_option autoImplicit false

namespace KCore

open ML Faithful DetachedB

namespace GenEqs

/-- The names of the symbols among `σs`. -/
def symNamesFB (σs : List KoreAML.Sym) : List String :=
  σs.filterMap fun σ => match σ with
    | .symbol n => some n
    | _ => none

/-- The names of the symbols of the patterns `listsB` reads. -/
def listNamesFB (c : Semantics) : List String :=
  (sigItems c).flatMap (fun it => symNamesFB (psyms it.pat)) ++
  (consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).flatMap
    (fun it => symNamesFB (psyms it.pat)) ++
  c.allColls.flatMap (fun k => symNamesFB (psyms (collNoJunk c k)) ++
    (collAxioms c k).flatMap (fun φ => symNamesFB (psyms φ))) ++
  symNamesFB (psyms (boolClosed c))

/-- The names of the symbols that build values (`valuesB`). -/
def valueNamesFB (c : Semantics) : List String :=
  (c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)).flatMap (fun k => [c.symName k.name]) ++
  c.allColls.flatMap (fun k => [c.symName k.unit, c.symName k.elem, c.symName k.concat]) ++
  ["inj"]

/-- The name of the head `symApp` writes for `f` (`appOK`). -/
def appNameFB (c : Semantics) (f : Sym) : String :=
  match symApp c f [] with
  | .app σ _ _ => σ.ident.name
  | _ => c.symName f

/-- `appNameFB` is the head `symApp` writes. -/
theorem appNameFB_of_symApp {c : Semantics} {f : Sym} {h : String} {xs : List String}
    (hw : ∀ ps, symApp c f ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps) : appNameFB c f = h := by
  unfold appNameFB; rw [hw]

/-- The names of the heads of the symbols applied at values (`graphsB`). -/
def graphNamesFB (c : Semantics) : List String :=
  hookSigs.flatMap (fun k => [appNameFB c k.name]) ++
  c.params.flatMap (fun k => [appNameFB c k.sig.name]) ++
  c.allFns.flatMap (fun f => [appNameFB c f.label])

/-- The names of the interpreted hooked symbols. -/
def hookNamesFB (c : Semantics) : List String :=
  hookSigs.flatMap (fun k => [c.symName k.name])

/-- The names a symbol free of the theory does not have (`freeB_iff_blockNames`). -/
def freeBlockNames (c : Semantics) : List String :=
  listNamesFB c ++ valueNamesFB c ++ graphNamesFB c ++ hookNamesFB c

/-- `freeB` read from a set of names: no symbol of `ks` has a name of `A`. -/
def freeBIdx (A : Std.HashSet String) (c : Semantics) (ks : List Sym) : Bool :=
  ks.all fun k => !A.contains (c.symName k)

variable {c : Semantics} {ks : List Sym}

/-- No symbol of `ks` has a name of `A ++ B`: none of `A` and none of `B`. -/
theorem notMem_append_FB (A B : List String) :
    (∀ k ∈ ks, c.symName k ∉ A ++ B) ↔ (∀ k ∈ ks, c.symName k ∉ A) ∧ (∀ k ∈ ks, c.symName k ∉ B) := by
  simp only [List.mem_append, not_or]
  exact ⟨fun h => ⟨fun k hk => (h k hk).1, fun k hk => (h k hk).2⟩,
    fun h k hk => ⟨h.1 k hk, h.2 k hk⟩⟩

/-- A check of every element, each one's by names, is by the names of all of them. -/
theorem all_FB {α : Type} (xs : List α) (P : α → Bool) (f : α → List String)
    (h : ∀ x ∈ xs, P x = true ↔ ∀ k ∈ ks, c.symName k ∉ f x) :
    xs.all P = true ↔ ∀ k ∈ ks, c.symName k ∉ xs.flatMap f := by
  simp only [List.all_eq_true, List.mem_flatMap, not_exists, not_and]
  constructor
  · intro hp k hk x hx hm
    exact (h x hx).mp (hp x hx) k hk hm
  · intro hn x hx
    exact (h x hx).mpr fun k hk hm => hn k hk x hx hm

theorem isName_nil_FB {σ : KoreAML.Sym} :
    isName c [] ks σ = true ↔ ∃ k ∈ ks, σ = .symbol (c.symName k) := by
  cases σ with
  | symbol n =>
    simp only [isName, List.any_eq_true, beq_iff_eq, KoreAML.Sym.symbol.injEq]
    exact ⟨fun ⟨k, hk, he⟩ => ⟨k, hk, he.symm⟩, fun ⟨k, hk, he⟩ => ⟨k, hk, he.symm⟩⟩
  | sort n => simp [isName]
  | _ => simp [isName]

theorem clean_nil_FB (φ : KoreAML.P) :
    clean c [] ks φ = true ↔ ∀ k ∈ ks, c.symName k ∉ symNamesFB (psyms φ) := by
  unfold clean
  simp only [List.all_eq_true, Bool.not_eq_true', symNamesFB, List.mem_filterMap]
  constructor
  · rintro h k hk ⟨σ, hσ, he⟩
    cases σ <;> simp only [reduceCtorEq, Option.some.injEq] at he
    subst he
    have := h _ hσ
    rw [← Bool.not_eq_true, isName_nil_FB] at this
    exact this ⟨k, hk, rfl⟩
  · intro h σ hσ
    rw [← Bool.not_eq_true, isName_nil_FB]
    rintro ⟨k, hk, rfl⟩
    exact h k hk ⟨_, hσ, rfl⟩

theorem sOK_nil_FB (s : Srt) : sOK c [] ks s = true := by
  simp [sOK, isName]

theorem allSOK_FB (l : List Srt) : l.all (sOK c [] ks) = true :=
  List.all_eq_true.mpr fun _ _ => sOK_nil_FB _

theorem optAllSOK_FB (o : Option Srt) : o.all (sOK c [] ks) = true := by
  cases o <;> simp [sOK_nil_FB]

theorem kOK_nil_FB (f : Sym) : kOK c [] ks f = true ↔ ∀ k ∈ ks, c.symName k ∉ [c.symName f] := by
  simp [kOK, isName]

theorem appOK_nil_FB (f : Sym) : appOK c [] ks f = true ↔ ∀ k ∈ ks, c.symName k ∉ [appNameFB c f] := by
  obtain ⟨h, xs, -, hw⟩ := symApp_head c f
  rw [appOK_of_symApp (hw := hw), appNameFB_of_symApp hw]
  simp [isName]

theorem regSig_nil_FB (hH : ∀ k ∈ ks, c.symName k ∉ hookNamesFB c) (φ : KoreAML.P) :
    regSig c [] ks φ = false := by
  simp only [regSig, List.any_nil, Bool.false_or, List.any_eq_false, Bool.and_eq_true,
    List.contains_iff_mem, not_and]
  intro h hh hk
  exact (hH h.name hk (List.mem_flatMap.mpr ⟨h, hh, List.mem_singleton_self _⟩)).elim

theorem listsB_nil_FB (hH : ∀ k ∈ ks, c.symName k ∉ hookNamesFB c) :
    listsB c [] ks = true ↔ ∀ k ∈ ks, c.symName k ∉ listNamesFB c := by
  unfold listsB listNamesFB
  simp only [Bool.and_eq_true, notMem_append_FB]
  refine and_congr (and_congr (and_congr ?_ ?_) ?_) (clean_nil_FB _)
  · refine all_FB _ _ _ fun it _ => ?_
    rw [regSig_nil_FB hH, Bool.or_false, clean_nil_FB]
  · exact all_FB _ _ _ fun it _ => clean_nil_FB _
  · refine all_FB _ _ _ fun k _ => ?_
    simp only [List.contains_nil, Bool.false_eq_true, and_false, ↓reduceIte,
      Bool.and_eq_true, notMem_append_FB]
    exact and_congr (clean_nil_FB _) (all_FB _ _ _ fun φ _ => clean_nil_FB _)

theorem valuesB_nil_FB : valuesB c [] ks = true ↔ ∀ k ∈ ks, c.symName k ∉ valueNamesFB c := by
  have hA : ((c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)).all
      fun k => kOK c [] ks k.name && k.args.all (sOK c [] ks)) = true ↔
      ∀ k ∈ ks, c.symName k ∉ (c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)).flatMap
        (fun k => [c.symName k.name]) :=
    all_FB _ _ _ fun k _ => by rw [allSOK_FB, Bool.and_true, kOK_nil_FB]
  have hS : (c.subsorts.all fun p => sOK c [] ks p.1 && sOK c [] ks p.2) = true ↔ True := by
    simp [sOK_nil_FB]
  have hC : (c.allColls.all fun k => !sOK c [] ks k.sort ||
      (kOK c [] ks k.unit && kOK c [] ks k.elem && kOK c [] ks k.concat && sOK c [] ks k.key &&
        k.val.all (sOK c [] ks))) = true ↔
      ∀ k ∈ ks, c.symName k ∉ c.allColls.flatMap
        (fun k => [c.symName k.unit, c.symName k.elem, c.symName k.concat]) := by
    refine all_FB _ _ _ fun k _ => ?_
    rw [sOK_nil_FB, sOK_nil_FB, optAllSOK_FB, Bool.not_true, Bool.false_or, Bool.and_true,
      Bool.and_true, Bool.and_eq_true, Bool.and_eq_true, kOK_nil_FB, kOK_nil_FB, kOK_nil_FB]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun ⟨⟨a, b⟩, d⟩ k hk => ⟨a k hk, b k hk, d k hk⟩,
      fun h => ⟨⟨fun k hk => (h k hk).1, fun k hk => (h k hk).2.1⟩, fun k hk => (h k hk).2.2⟩⟩
  have hI : (!isName c [] ks (.symbol "inj")) = true ↔ ∀ k ∈ ks, c.symName k ∉ ["inj"] := by
    simp only [Bool.not_eq_true', isName, List.any_eq_false, beq_iff_eq, List.mem_singleton]
  unfold valuesB
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, hA, hS, hC, hI, valueNamesFB,
    notMem_append_FB, notMem_append_FB, and_true]

theorem graphsB_nil_FB (hH : ∀ k ∈ ks, c.symName k ∉ hookNamesFB c) :
    graphsB c [] ks = true ↔ ∀ k ∈ ks, c.symName k ∉ graphNamesFB c := by
  unfold graphsB graphNamesFB
  simp only [Bool.and_eq_true, notMem_append_FB]
  refine and_congr (and_congr ?_ ?_) ?_
  · refine all_FB _ _ _ fun k hk => ?_
    have hk' : kOK c [] ks k.name = true :=
      (kOK_nil_FB _).mpr fun k' hk' hm => hH k' hk' (List.mem_flatMap.mpr ⟨k, hk, hm⟩)
    rw [hk', Bool.not_true, Bool.false_or, allSOK_FB, Bool.and_true, appOK_nil_FB]
  · refine all_FB _ _ _ fun k _ => ?_
    rw [allSOK_FB, Bool.and_true, appOK_nil_FB]
  · refine all_FB _ _ _ fun f _ => ?_
    rw [allSOK_FB, Bool.and_true, appOK_nil_FB]

theorem hooks_nil_FB :
    hookSigs.all (fun k => kOK c [] ks k.name) = true ↔ ∀ k ∈ ks, c.symName k ∉ hookNamesFB c :=
  all_FB _ _ _ fun _ _ => kOK_nil_FB _

/-- **`freeB` by names**: no premise names the symbols `ks` exactly where none of them has a name
of `freeBlockNames c`. -/
theorem freeB_iff_blockNames :
    freeB c ks = true ↔ ∀ k ∈ ks, c.symName k ∉ freeBlockNames c := by
  unfold freeB freeBlockNames
  simp only [Bool.and_eq_true, notMem_append_FB, hooks_nil_FB]
  constructor
  · rintro ⟨⟨⟨l, v⟩, g⟩, h⟩
    exact ⟨⟨⟨(listsB_nil_FB h).mp l, valuesB_nil_FB.mp v⟩, (graphsB_nil_FB h).mp g⟩, h⟩
  · rintro ⟨⟨⟨l, v⟩, g⟩, h⟩
    exact ⟨⟨⟨(listsB_nil_FB h).mpr l, valuesB_nil_FB.mpr v⟩, (graphsB_nil_FB h).mpr g⟩, h⟩

/-- **`freeB` read from the names, once**: at the set of `freeBlockNames c`, `freeBIdx` is `freeB`. -/
theorem freeBIdx_eq (c : Semantics) (ks : List Sym) :
    freeBIdx (Std.HashSet.ofList (freeBlockNames c)) c ks = freeB c ks := by
  rw [Bool.eq_iff_iff, freeB_iff_blockNames]
  simp only [freeBIdx, List.all_eq_true, Bool.not_eq_true', Std.HashSet.contains_ofList]
  refine forall₂_congr fun k _ => ?_
  rw [← Bool.not_eq_true, List.contains_iff_mem]

end GenEqs

end KCore
