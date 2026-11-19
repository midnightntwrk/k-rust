/-
  The heads a sentence applies, each a symbol name with its sort arguments (`appHeadsOf`), and the
  heads at which Γ applies its symbols (`gammaHeads`). A KORE symbol with sort parameters is one
  symbol at each instance: `Lblite{SortK{}}` and `Lblite{SortKItem{}}` are applications of different
  symbols of the translation (`KoreAML.tr` applies the symbol to its sort arguments), so whether Γ
  has the symbol a sentence applies is a question about the head with its sort arguments, not about
  the name alone (`symbolsOf`).
-/
import KcoreSpec.TieDefs

set_option autoImplicit false

namespace KCore

open Faithful

mutual
  /-- The heads of the applications of a pattern, in order of occurrence, with repetitions: each
  the symbol's name and the sort arguments it is applied at (the injection `inj` among them). -/
  def appHeadsOf : Kore.Pattern → List (String × List Kore.KSort)
    | .app h ss ps | .leftAssoc h ss ps | .rightAssoc h ss ps => (h.ident.name, ss) :: appHeadsOfList ps
    | .var _ | .string _ | .top _ | .bottom _ | .dv _ _ => []
    | .not _ p | .next _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p
    | .floor _ _ p => appHeadsOf p
    | .and _ ps | .or _ ps => appHeadsOfList ps
    | .implies _ p q | .iff _ p q | .rewrites _ p q | .equals _ _ p q | .in _ _ p q =>
      appHeadsOf p ++ appHeadsOf q
    termination_by structural p => p
  def appHeadsOfList : List Kore.Pattern → List (String × List Kore.KSort)
    | [] => []
    | p :: ps => appHeadsOf p ++ appHeadsOfList ps
    termination_by structural ps => ps
end

/-- The names of the heads are the names `symbolsOf` lists. -/
theorem appHeadsOf_names : ∀ p, (appHeadsOf p).map (·.1) = symbolsOf p
  | .app h ss ps | .leftAssoc h ss ps | .rightAssoc h ss ps => by
    simp only [appHeadsOf, symbolsOf, List.map_cons, appHeadsOfList_names ps]
  | .var _ | .string _ | .top _ | .bottom _ | .dv _ _ => rfl
  | .not _ p | .next _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p
  | .floor _ _ p => by simp only [appHeadsOf, symbolsOf, appHeadsOf_names p]
  | .and _ ps | .or _ ps => by simp only [appHeadsOf, symbolsOf, appHeadsOfList_names ps]
  | .implies _ p q | .iff _ p q | .rewrites _ p q | .equals _ _ p q | .in _ _ p q => by
    simp only [appHeadsOf, symbolsOf, List.map_append, appHeadsOf_names p, appHeadsOf_names q]
where
  appHeadsOfList_names : ∀ ps, (appHeadsOfList ps).map (·.1) = symbolsOfList ps
    | [] => rfl
    | p :: ps => by
      simp only [appHeadsOfList, symbolsOfList, List.map_append, appHeadsOf_names p,
        appHeadsOfList_names ps]

/-- The head at which Γ applies its symbol `f`, the one `symApp` writes: `Lblite` at the sort `SortX`
for a symbol named `ite{X}`, the symbol's name with no sort argument otherwise (the registry's
`kIte`, named `Lblite`, among them: Γ applies it at no sort). -/
def gammaHead (c : Semantics) (f : Sym) : String × List Kore.KSort :=
  match iteSort? (c.symName f) with
  | some X => ("Lblite", [KoreAML.srt X])
  | none => (c.symName f, [])

/-- `symApp` applies `f` at its head `gammaHead`. -/
theorem symApp_gammaHead (c : Semantics) (f : Sym) (args : List Kore.Pattern) :
    symApp c f args = .app ⟨⟨(gammaHead c f).1⟩⟩ (gammaHead c f).2 args := by
  unfold symApp gammaHead
  cases iteSort? (c.symName f) <;> rfl

/-- `gammaHead` is the head `symApp` writes, with its sorts. -/
theorem gammaHead_of_symApp {c : Semantics} {f : Sym} {h : String} {xs : List String}
    (hw : ∀ ps, Faithful.symApp c f ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps) :
    gammaHead c f = (h, xs.map KoreAML.srt) := by
  have he := (hw []).symm.trans (symApp_gammaHead c f [])
  simp only [Kore.Pattern.app.injEq] at he
  obtain ⟨h1, h2, -⟩ := he
  exact Prod.ext (by simpa using h1.symm) h2.symm

/-- A symbol whose name the decoder reads as no instance is Γ's at its name, at no sort. -/
theorem gammaHead_noInst {c : Semantics} {f : Sym} (h : instDecode? (c.symName f) = none) :
    gammaHead c f = (c.symName f, []) := by
  unfold gammaHead; rw [iteSort?_none_of_instDecode h]

/-- The heads at which Γ applies its symbols: the head of each of its symbols (`kernelSyms`) and the
injection `inj` at each pair of `subsorts`, the order over which Γ's constructor items state the
injections of a sort's generators and the coherence triangles (`inj` is no member of `kernelSyms`;
Γ's items apply it at pairs of that order only). -/
def gammaHeads (c : Semantics) : List (String × List Kore.KSort) :=
  (kernelSyms c).map (fun k => gammaHead c k.name) ++
    c.subsorts.map fun (a, b) => ("inj", [KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)])

/-- The head `h` is one of Γ's (`gammaHeads`). -/
def gammaHasHead (c : Semantics) (h : String × List Kore.KSort) : Bool :=
  (gammaHeads c).any fun g => decide (g = h)

/-- `gammaHasHead` where the decoder reads no name of Γ's symbols as an instance
(`gammaHasHead_eq_plain_irs`): a head with no sort argument whose name is a name of Γ's symbols, or
`inj` at a pair of `subsorts`. It reads no name with the decoder. -/
def gammaHasHeadPlain (c : Semantics) (h : String × List Kore.KSort) : Bool :=
  (h.2.isEmpty && (kernelSyms c).any fun k => c.symName k.name == h.1) ||
    (h.1 == "inj" && c.subsorts.any fun (a, b) =>
      decide ([KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)] = h.2))

/-- Where no symbol of Γ has a name `iteSort?` reads as an instance of `ite`, each of Γ's symbols
is applied at its name with no sort argument, and `gammaHasHead` is `gammaHasHeadPlain`. -/
theorem gammaHasHead_eq_plain {c : Semantics}
    (hno : (kernelSyms c).all (fun k => (iteSort? (c.symName k.name)).isNone) = true) :
    gammaHasHead c = gammaHasHeadPlain c := by
  funext h
  obtain ⟨n, ss⟩ := h
  have hg : ∀ k ∈ kernelSyms c, gammaHead c k.name = (c.symName k.name, []) := by
    intro k hk
    have h1 := List.all_eq_true.mp hno k hk
    unfold gammaHead
    cases hX : iteSort? (c.symName k.name) with
    | none => rfl
    | some X => rw [hX] at h1; exact absurd h1 Bool.false_ne_true
  simp only [gammaHasHead, gammaHeads, gammaHasHeadPlain, List.any_append, List.any_map]
  congr 1
  · apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, beq_iff_eq,
      Function.comp_apply]
    constructor
    · rintro ⟨k, hk, he⟩
      rw [hg k hk, Prod.mk.injEq] at he
      exact ⟨he.2.symm, k, hk, he.1⟩
    · rintro ⟨hs, k, hk, he⟩
      exact ⟨k, hk, by rw [hg k hk, he, hs]⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Function.comp_apply,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, hab, h1, h2⟩
      exact ⟨h1.symm, a, b, hab, h2⟩
    · rintro ⟨h1, a, b, hab, h2⟩
      exact ⟨a, b, hab, h1.symm, h2⟩

/-- `gammaHasHead` where the decoder reads no name of Γ's symbols as an instance: each of Γ's
symbols is applied at its name with no sort argument, and `gammaHasHead` is `gammaHasHeadPlain`. -/
theorem gammaHasHead_eq_plain_irs {c : Semantics}
    (hno : (kernelSyms c).all (fun k => (instDecode? (c.symName k.name)).isNone) = true) :
    gammaHasHead c = gammaHasHeadPlain c := by
  funext h
  obtain ⟨n, ss⟩ := h
  have hg : ∀ k ∈ kernelSyms c, gammaHead c k.name = (c.symName k.name, []) := fun k hk =>
    gammaHead_noInst (Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hno k hk))
  simp only [gammaHasHead, gammaHeads, gammaHasHeadPlain, List.any_append, List.any_map]
  congr 1
  · apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, beq_iff_eq,
      Function.comp_apply]
    constructor
    · rintro ⟨k, hk, he⟩
      rw [hg k hk, Prod.mk.injEq] at he
      exact ⟨he.2.symm, k, hk, he.1⟩
    · rintro ⟨hs, k, hk, he⟩
      exact ⟨k, hk, by rw [hg k hk, he, hs]⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Function.comp_apply,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, hab, h1, h2⟩
      exact ⟨h1.symm, a, b, hab, h2⟩
    · rintro ⟨h1, a, b, hab, h2⟩
      exact ⟨a, b, hab, h1.symm, h2⟩

/-- A list's `all` from that of its first `n` elements and of the rest: a kernel decision over a
long list, in parts. -/
theorem all_of_take_drop_heads {α : Type} (l : List α) (p : α → Bool) (n : Nat)
    (h1 : (l.take n).all p = true) (h2 : (l.drop n).all p = true) : l.all p = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]; rfl

end KCore
