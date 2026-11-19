/-
  Γ's heads read on codes (`KoreAML.Distinct.strCode`), for the tie's absent section, and the
  bridges between a membership of names and the same membership of their codes.

  `gammaHasHead c h` (TieHeads.lean) builds `gammaHeads c`: the head `gammaHead` gives each of Γ's
  symbols (its name read by the decoder `instDecode?`) and `inj` at each subsort pair, each sort
  written by `KoreAML.srt`. A kernel decision of it over a large text computes that list, and
  compares each head of a sentence with it by strings. Here the same question is asked of two lists
  of numbers, each tied to `c` by one equation:

  - `symCodesOf c`: the code of the name of each of Γ's symbols (`kernelSyms`);
  - `injCodesOf c`: each subsort pair, each sort as the code of the identifier `KoreAML.srt` writes
    for it (`Sort` followed by the sort's name).

  `hasHeadCoded sc ic h` reads `h` against them: a head without sort arguments is Γ's where its
  name's code is in `sc`, and `inj` at two sort constructors without arguments is Γ's where the pair
  of their identifiers' codes is in `ic`. Its sort arguments are read by their identifiers' codes
  only, never as strings.

  That is `gammaHasHead c` exactly where no name of Γ's symbols is one the decoder reads as an
  instance (`gammaHasHead_eq_plain_irs`). That condition is decided on the codes too: a name the
  decoder reads holds the byte of `{` (`Faithful.instCoded_of_instDecode`), so a list of codes none
  of which has that byte (`instCoded`) gives it (`noInst_of_codes`). This is the only point where
  the head `gammaHead` writes is read, and it is read through `instDecode?` and the library's
  `gammaHasHead_eq_plain_irs`; nothing here mentions `iteSort?`.

  `gammaHasHead_coded`: `gammaHasHead c = hasHeadCoded sc ic` from `symCodesOf c = sc`,
  `injCodesOf c = ic` and `sc.all (!instCoded ·)`.
-/
import KcoreSpec.TieHeads
import KcoreSpec.NameCodes

set_option autoImplicit false

namespace KCore

open Faithful KoreAML.Distinct

/-! ## The literals' sources -/

/-- Γ's symbols' names, each as its code, in the order of `kernelSyms`. -/
def symCodesOf (c : Semantics) : List Nat :=
  (kernelSyms c).map fun k => strCode (c.symName k.name)

/-- Γ's subsort pairs, in the order of `subsorts`, each sort as the code of the identifier
`KoreAML.srt` writes for it: `Sort` followed by the sort's name. -/
def injCodesOf (c : Semantics) : List (Nat × Nat) :=
  c.subsorts.map fun (a, b) => (strCode ("Sort" ++ c.sortName a), strCode ("Sort" ++ c.sortName b))

/-! ## The coded membership -/

/-- The code of a sort written as a sort constructor without arguments: the code of its
identifier. Any other sort has none. -/
def sortCode? : Kore.KSort → Option Nat
  | .ctor i [] => some (strCode i.ident.name)
  | _ => none

/-- The head `h` is one of Γ's, read on the codes `sc` (of Γ's symbols' names) and `ic` (of its
subsort pairs, as `KoreAML.srt` writes the sorts): a head without sort arguments whose name's code
is in `sc`, or `inj` at two sort constructors without arguments whose identifiers' codes are a
pair of `ic`. -/
def hasHeadCoded (sc : List Nat) (ic : List (Nat × Nat)) (h : String × List Kore.KSort) : Bool :=
  match h.2 with
  | [] => sc.contains (strCode h.1)
  | [s, t] =>
    h.1 == "inj" &&
      match sortCode? s, sortCode? t with
      | some x, some y => ic.any fun p => p.1 == x && p.2 == y
      | _, _ => false
  | _ => false

/-! ## Bridges: names and their codes -/

/-- Two names are equal exactly where their codes are (`strCode_inj`). -/
theorem symCode_beq_tc (a b : String) : (strCode a == strCode b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => strCode_inj h, fun h => h ▸ rfl⟩

/-- A list of names holds `n` exactly where its codes hold `n`'s. -/
theorem contains_strCode (l : List String) (n : String) :
    l.contains n = (l.map strCode).contains (strCode n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  exact ⟨fun h => ⟨n, h, rfl⟩, fun ⟨m, hm, he⟩ => strCode_inj he ▸ hm⟩

/-- Two heads are equal exactly where their names' codes and their sort arguments are
(`strCode_inj`). -/
theorem headCode_eq_tc (g h : String × List Kore.KSort) :
    (strCode g.1 == strCode h.1 && decide (g.2 = h.2)) = decide (g = h) := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  by_cases e : g1 = h1
  · subst e; simp
  · have hc : strCode g1 ≠ strCode h1 := fun hc => e (strCode_inj hc)
    simp [hc, e]

/-- Γ has a symbol under the name `n` exactly where `n`'s code is one of `symCodesOf c`. -/
theorem anySym_codes_tc {c : Semantics} {sc : List Nat} (hs : symCodesOf c = sc) (n : String) :
    (kernelSyms c).any (fun k => c.symName k.name == n) = sc.contains (strCode n) := by
  subst hs
  apply Bool.eq_iff_iff.mpr
  simp only [symCodesOf, List.any_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨k, hk, he⟩ => ⟨k, hk, by rw [he]⟩, fun ⟨k, hk, he⟩ => ⟨k, hk, strCode_inj he⟩⟩

/-- `anySym_codes_tc` in the form tiegen's `hasSymL` reads: `sc.any (· == strCode n)`. -/
theorem hasSymL_codes_tc {c : Semantics} {sc : List Nat} (hs : symCodesOf c = sc) (n : String) :
    sc.any (· == strCode n) = (kernelSyms c).any (fun k => c.symName k.name == n) := by
  subst hs
  simp only [symCodesOf, List.any_map, Function.comp_def, symCode_beq_tc]

/-! ## No name of Γ is an instance, on the codes -/

/-- Where no code of Γ's names holds the byte of `{`, the decoder reads none of Γ's names as an
instance. -/
theorem noInst_of_codes {c : Semantics} {sc : List Nat} (hs : symCodesOf c = sc)
    (hno : sc.all (fun x => !instCoded x) = true) :
    (kernelSyms c).all (fun k => (instDecode? (c.symName k.name)).isNone) = true := by
  subst hs
  rw [List.all_eq_true]
  intro k hk
  have h1 := List.all_eq_true.mp hno _ (List.mem_map_of_mem (f := fun k => strCode (c.symName k.name)) hk)
  cases hd : instDecode? (c.symName k.name) with
  | none => rfl
  | some _ =>
    rw [instCoded_of_instDecode (by rw [hd]; exact Option.some_ne_none _)] at h1
    cases h1

/-! ## Γ's heads on the codes -/

/-- A sort is `KoreAML.srt x` exactly where its code is that of `Sort` followed by `x`. -/
theorem srt_eq_iff_code (x : String) (s : Kore.KSort) :
    KoreAML.srt x = s ↔ sortCode? s = some (strCode ("Sort" ++ x)) := by
  cases s with
  | var v => simp [KoreAML.srt, sortCode?]
  | ctor i args =>
    cases args with
    | cons a as => simp [KoreAML.srt, sortCode?]
    | nil =>
      obtain ⟨⟨m⟩⟩ := i
      simp only [KoreAML.srt, sortCode?, Option.some.injEq, Kore.KSort.ctor.injEq, and_true]
      constructor
      · intro h; cases h; rfl
      · intro h; cases strCode_inj h; rfl

/-- `gammaHasHeadPlain` read on the codes. -/
theorem gammaHasHeadPlain_coded {c : Semantics} {sc : List Nat} {ic : List (Nat × Nat)}
    (hs : symCodesOf c = sc) (hi : injCodesOf c = ic) :
    gammaHasHeadPlain c = hasHeadCoded sc ic := by
  funext h
  obtain ⟨n, ss⟩ := h
  have hinj : ∀ s t : Kore.KSort, (c.subsorts.any fun (a, b) =>
      decide ([KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)] = [s, t])) =
      (match sortCode? s, sortCode? t with
        | some x, some y => ic.any fun p => p.1 == x && p.2 == y
        | _, _ => false) := by
    intro s t
    subst hi
    cases hx : sortCode? s with
    | none =>
      simp only [List.any_eq_false, decide_eq_true_eq, List.cons.injEq, and_true, not_and, Prod.forall]
      intro a b _ ha
      rw [srt_eq_iff_code, hx] at ha; cases ha
    | some x =>
      cases hy : sortCode? t with
      | none =>
        simp only [List.any_eq_false, decide_eq_true_eq, List.cons.injEq, and_true, not_and, Prod.forall]
        intro a b _ _ hb
        rw [srt_eq_iff_code, hy] at hb; cases hb
      | some y =>
        simp only [injCodesOf, List.any_map]
        congr 1
        funext ⟨a, b⟩
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, decide_eq_true_eq, List.cons.injEq, and_true, Bool.and_eq_true,
          beq_iff_eq, srt_eq_iff_code, hx, hy, Option.some.injEq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  match ss with
  | [] =>
    simp only [gammaHasHeadPlain, hasHeadCoded, List.isEmpty_nil, Bool.true_and, anySym_codes_tc hs]
    simp
  | [s] =>
    simp [gammaHasHeadPlain, hasHeadCoded]
  | [s, t] =>
    simp only [gammaHasHeadPlain, hasHeadCoded, List.isEmpty_cons, Bool.false_and, Bool.false_or]
    rw [hinj s t]
  | s :: t :: u :: r =>
    simp [gammaHasHeadPlain, hasHeadCoded]

/-- **Γ's heads on the codes.** Where `sc` and `ic` are the codes of Γ's symbols' names and of its
subsort pairs, and no code of `sc` holds the byte of `{` (so the decoder reads no name of Γ as an
instance), `gammaHasHead c` is `hasHeadCoded sc ic`. -/
theorem gammaHasHead_coded {c : Semantics} {sc : List Nat} {ic : List (Nat × Nat)}
    (hs : symCodesOf c = sc) (hi : injCodesOf c = ic) (hno : sc.all (fun x => !instCoded x) = true) :
    gammaHasHead c = hasHeadCoded sc ic := by
  rw [gammaHasHead_eq_plain_irs (noInst_of_codes hs hno)]
  exact gammaHasHeadPlain_coded hs hi

end KCore
