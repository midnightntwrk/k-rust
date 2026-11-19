/-
  KCore, checked layer: the three conjuncts of `faithCoreOK` that read symbol and sort names
  (`namesNumbered`, `itesApart`, `namesApartK`), decided on the names' codes.

  A kernel decision that reads a string pays for each of its bytes, whichever operation reads it,
  so a check that reads a large signature's names once per comparison exceeds memory. Here each
  name is encoded once (`strCode`, Distinct.lean: its UTF-8 bytes in base 256 behind a leading 1)
  into a list of numbers tied to the numbered names by one fact (`(allSymNames c).map strCode =
  sym`, proved in blocks of rows: `codeRows`), and the checks read only those numbers:

  - a name the decoder reads as an instance (`instDecode?`) holds `{`, so its code has the byte 123
    among its digits (`instCoded_of_instDecode`); the symbols whose codes do are listed once
    (`instIdx`), and `namesNumbered` and `itesApart` decode only those; an instance's head is
    compared with the names of the symbols of no arguments by its code;
  - names are distinct when their codes are, which the sorted codes decide (`nodup_of_ascending`);
    `namesApartK` then follows from distinct symbol numbers in `kernelSyms`, distinct codes of
    their names (picked from the table in one pass, `pick`) and of all numbered sorts' names, and
    no entry's code equal to `"inj"`'s.

  Each decider is proved to give the conjunct it stands for (`namesNumbered_of_codes`,
  `itesApart_of_codes`, `namesApartK_of_codes`); `faithCoreOK_of_partsK` joins the conjuncts.
  None of the conjuncts is changed.
-/
import KcoreSpec.CoreChecked

set_option autoImplicit false

namespace KCore

open KoreAML.Distinct

namespace Faithful

/-! ## The numbered names -/

/-- The names of the numbered symbols: the registry's, then the definition's own. -/
def allSymNames (c : Semantics) : List String := regSymNames ++ c.symNames

/-- The names of the numbered sorts: the registry's, then the definition's own. -/
def allSortNames (c : Semantics) : List String := regSortNames ++ c.sortNames

theorem regSymNames_length : regSymNames.length = nRegSyms := by decide +kernel

theorem regSortNames_length : regSortNames.length = nRegSorts := by decide +kernel

theorem symName_eq_getD (c : Semantics) (f : Sym) : c.symName f = (allSymNames c).getD f "" := by
  unfold Semantics.symName allSymNames
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : f < nRegSyms
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_append_left (by rw [regSymNames_length]; exact h)]
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_append_right (by rw [regSymNames_length]; exact Nat.le_of_not_lt h), regSymNames_length]

theorem sortName_eq_getD (c : Semantics) (s : Srt) : c.sortName s = (allSortNames c).getD s "" := by
  unfold Semantics.sortName allSortNames
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : s < nRegSorts
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_append_left (by rw [regSortNames_length]; exact h)]
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_append_right (by rw [regSortNames_length]; exact Nat.le_of_not_lt h), regSortNames_length]

theorem allSymNames_length (c : Semantics) : (allSymNames c).length = nRegSyms + c.symNames.length := by
  simp [allSymNames, regSymNames_length]

theorem allSortNames_length (c : Semantics) : (allSortNames c).length = nRegSorts + c.sortNames.length := by
  simp [allSortNames, regSortNames_length]

/-! ## The codes, by rows -/

/-- Rows lo, …, lo + len - 1 of `l`, encoded, are those of `m`. -/
def codeRows (l : List String) (m : List Nat) (lo len : Nat) : Bool :=
  ((l.drop lo).take len).map strCode == (m.drop lo).take len

theorem codeRows_join {l : List String} {m : List Nat} {a k b n : Nat} (h1 : codeRows l m 0 a = true)
    (h2 : codeRows l m k b = true) (hk : a = k) (hn : a + b = n) : codeRows l m 0 n = true := by
  subst hk hn
  simp only [codeRows, List.drop_zero, beq_iff_eq] at h1 h2 ⊢
  rw [List.take_add, List.take_add, List.map_append, h1, h2]

theorem codeRows_all {l : List String} {m : List Nat} {n : Nat} (hl : l.length = n) (hm : m.length = n)
    (h : codeRows l m 0 n = true) : l.map strCode = m := by
  simp only [codeRows, List.drop_zero, beq_iff_eq] at h
  rw [← hl, List.take_length] at h
  rw [h, hl, ← hm, List.take_length]

/-- The code of a numbered name. -/
theorem strCode_getD {l : List String} {m : List Nat} (h : l.map strCode = m) {i : Nat} (hi : i < m.length) :
    strCode (l.getD i "") = m[i] := by
  have hl : i < l.length := by rw [← h, List.length_map] at hi; exact hi
  subst h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

/-- The code of a symbol's name is its entry of the codes, and 1, the code of the empty name, for
a symbol that is not numbered. -/
theorem strCode_symName_getD {c : Semantics} {sym : List Nat} (hc : (allSymNames c).map strCode = sym)
    (f : Sym) : strCode (c.symName f) = sym.getD f 1 := by
  rw [symName_eq_getD]
  by_cases hf : f < sym.length
  · rw [strCode_getD hc hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf, Option.getD_some]
  · have hf' : ¬ f < (allSymNames c).length := by rw [← hc, List.length_map] at hf; exact hf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hf'),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hf)]
    decide

/-! ## Distinct codes -/

theorem nodup_of_ascending {p : Nat} {l : List Nat} (h : ascending (msort p l) = true) : l.Nodup :=
  (msort_perm p l).nodup_iff.mp ((pairwise_of_ascending h).imp Nat.ne_of_lt)

theorem eq_of_nodup_getElem {l : List Nat} (hn : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : l[i] = l[j]) : i = j :=
  (List.Nodup.getElem_inj hn).mp h

/-! ## Codes of joined bytes -/

theorem bytesCode_append (l r : List UInt8) : bytesCode (l ++ r) = bytesCode r * 256 ^ l.length + (bytesCode l - 256 ^ l.length) := by
  induction l with
  | nil => simp [bytesCode]
  | cons b l ih =>
    have hb := b.toNat_lt
    have hl : 256 ^ l.length ≤ bytesCode l := by
      clear ih
      induction l with
      | nil => simp [bytesCode]
      | cons b' l ih' =>
        have := b'.toNat_lt
        simp only [bytesCode, List.length_cons, Nat.pow_succ]; omega
    simp only [List.cons_append, bytesCode, ih, List.length_cons, Nat.pow_succ]
    have : bytesCode r * (256 ^ l.length * 256) = bytesCode r * 256 ^ l.length * 256 := by
      rw [Nat.mul_assoc]
    rw [this]
    have h2 : (bytesCode l * 256 + b.toNat - 256 ^ l.length * 256) =
        (bytesCode l - 256 ^ l.length) * 256 + b.toNat := by
      rw [Nat.sub_mul]; omega
    rw [h2, Nat.add_mul, Nat.add_assoc]

theorem utf8Encode_cons_toList (c : Char) (l : List Char) :
    (c :: l).utf8Encode.data.toList = String.utf8EncodeChar c ++ l.utf8Encode.data.toList := by
  simp [List.utf8Encode]

/-- The positions from i of the entries of l that pass p. -/
def idxWhere (p : Nat → Bool) : List Nat → Nat → List Nat
  | [], _ => []
  | a :: l, i => if p a then i :: idxWhere p l (i + 1) else idxWhere p l (i + 1)

theorem mem_idxWhere (p : Nat → Bool) : ∀ (l : List Nat) (i j : Nat) (hj : j < l.length), p l[j] = true →
    i + j ∈ idxWhere p l i
  | [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a :: l, i, 0, _, hp => by
    simp only [List.getElem_cons_zero] at hp
    simp [idxWhere, hp]
  | a :: l, i, j + 1, hj, hp => by
    simp only [List.getElem_cons_succ] at hp
    have := mem_idxWhere p l (i + 1) j (by simp at hj; omega) hp
    rw [show i + (j + 1) = i + 1 + j by omega]
    unfold idxWhere
    split <;> simp [this]

/-! ## Names read as an instance -/

/-- Whether one of the base-256 digits of `n` below its leading one, among its lowest `f`, is 123,
the byte of `{`. -/
def braceDigits : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, n => if n < 256 then false else n % 256 == 123 || braceDigits f (n / 256)

/-- A code holding the byte of `{` among its digits. -/
def instCoded (n : Nat) : Bool := braceDigits n n

theorem length_le_bytesCode : ∀ l : List UInt8, l.length ≤ bytesCode l
  | [] => Nat.zero_le _
  | b :: bs => by
    have := length_le_bytesCode bs
    have := bytesCode_pos bs
    simp only [List.length_cons, bytesCode]; omega

theorem braceDigits_bytesCode : ∀ (l : List UInt8) (f : Nat), l.length ≤ f → (123 : UInt8) ∈ l →
    braceDigits f (bytesCode l) = true
  | [], _, _, hm => absurd hm List.not_mem_nil
  | b :: bs, 0, hl, _ => absurd hl (by simp)
  | b :: bs, f + 1, hl, hm => by
    have hp := bytesCode_pos bs
    have hb := b.toNat_lt
    have hlt : ¬ bytesCode bs * 256 + b.toNat < 256 := by omega
    have hmod : (bytesCode bs * 256 + b.toNat) % 256 = b.toNat := by omega
    have hdiv : (bytesCode bs * 256 + b.toNat) / 256 = bytesCode bs := by omega
    simp only [bytesCode, braceDigits, hlt, ↓reduceIte, hmod, hdiv, Bool.or_eq_true, beq_iff_eq]
    rcases List.mem_cons.mp hm with he | he
    · left; rw [← he]; rfl
    · right; exact braceDigits_bytesCode bs f (by simp at hl; omega) he

/-- A name the decoder reads as an instance holds `{`, so its UTF-8 bytes hold 123. -/
theorem brace_mem_bytes {n : String} (h : instDecode? n ≠ none) : (123 : UInt8) ∈ n.toByteArray.data.toList := by
  have hh : instDecHead n.toList ≠ none := by
    intro he; apply h; unfold instDecode?; rw [he]
  obtain ⟨⟨hd, r⟩, hp⟩ := Option.ne_none_iff_exists'.mp hh
  have hn : n = String.ofList (hd ++ '{' :: r) := by
    rw [← (instDecHead_eq_some.1 hp).1, String.ofList_toList]
  have hc : (['{'] : List Char).utf8Encode.data.toList = [123] := by decide
  rw [hn, String.toByteArray_ofList, List.utf8Encode_append, List.utf8Encode_cons, ByteArray.toList_data_append,
    ByteArray.toList_data_append, hc]
  simp

/-- A name the decoder reads as an instance has a code `instCoded` accepts. -/
theorem instCoded_of_instDecode {n : String} (h : instDecode? n ≠ none) : instCoded (strCode n) = true :=
  braceDigits_bytesCode _ _ (length_le_bytesCode _) (brace_mem_bytes h)

theorem idxWhere_append (p : Nat → Bool) : ∀ (l₁ l₂ : List Nat) (i : Nat),
    idxWhere p (l₁ ++ l₂) i = idxWhere p l₁ i ++ idxWhere p l₂ (i + l₁.length)
  | [], _, i => by simp [idxWhere]
  | a :: l₁, l₂, i => by
    have := idxWhere_append p l₁ l₂ (i + 1)
    rw [show i + 1 + l₁.length = i + (a :: l₁).length by simp; omega] at this
    simp only [List.cons_append, idxWhere, this]
    split <;> rfl

/-- The numbered symbols whose names' codes `instCoded` accepts, given the codes of all numbered
symbols' names. -/
def instIdx (sym : List Nat) : List Nat := idxWhere instCoded sym 0

/-- A symbol whose name the decoder reads as an instance is listed in `instIdx`. -/
theorem mem_instIdx {c : Semantics} {sym : List Nat} (hc : (allSymNames c).map strCode = sym) {f : Sym}
    (h : instDecode? (c.symName f) ≠ none) : f ∈ instIdx sym := by
  rw [symName_eq_getD] at h
  have hf : f < sym.length := by
    rw [← hc, List.length_map]
    refine Nat.lt_of_not_le fun hge => h ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  have := mem_idxWhere instCoded sym 0 f hf (by rw [← strCode_getD hc hf]; exact instCoded_of_instDecode h)
  simpa [instIdx] using this

/-! ## `namesNumbered` -/

namespace Model

/-- `namesNumbered` on codes: `I` lists the symbols that may be named like an instance
(`instIdx`, the names holding `{`); a constructor among them, or a symbol among them that an
overloading symbol overloads, is not so named (`instDecode?`, read on its name only there), and
every sort of a function is numbered. -/
def namesNumberedC (c : Semantics) (I : List Nat) : Bool :=
  c.ctorSigs.all (fun k => !I.contains k.name || (instDecode? (c.symName k.name)).isNone) &&
  c.ovls.all (fun o => o.over.all fun g => !I.contains g || (instDecode? (c.symName g)).isNone) &&
  c.allFns.all fun fn => (fn.result :: fn.args).all fun s => decide (s < nRegSorts + c.sortNames.length)

theorem namesNumbered_of_codes {c : Semantics} {sym I : List Nat} (hc : (allSymNames c).map strCode = sym)
    (hI : instIdx sym = I) (h : namesNumberedC c I = true) : namesNumbered c = true := by
  subst hI
  simp only [namesNumberedC, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none]
  refine ⟨⟨fun k hk => ?_, fun o ho g hg => ?_⟩, h3⟩
  · cases hn : instDecode? (c.symName k.name) with
    | none => rfl
    | some p =>
      rcases h1 k hk with h | h
      · exact absurd (mem_instIdx hc (by rw [hn]; exact Option.some_ne_none p)) (by simpa using h)
      · rw [hn] at h; cases h
  · cases hn : instDecode? (c.symName g) with
    | none => rfl
    | some p =>
      rcases h2 o ho g hg with h | h
      · exact absurd (mem_instIdx hc (by rw [hn]; exact Option.some_ne_none p)) (by simpa using h)
      · rw [hn] at h; cases h

/-! ## `itesApart` -/

/-- The entries of `kernelSyms` among `I`. -/
def iteSyms (c : Semantics) (I : List Nat) : List CtorSig := (kernelSyms c).filter fun k => I.contains k.name

/-- `itesApart` on codes, over the entries of `kernelSyms` among `I` (`iteSyms`), which lists
those that may be named like an instance (`instIdx`): such an entry's sort names are numbered sort
names (their codes are numbered sort names' codes), every such entry of its head has as many sorts,
its head is not `inj`, and its head's code is the code of no name of an entry of `kernelSyms` of no
arguments (`sym` the codes of the numbered symbols' names). -/
def itesApartC (c : Semantics) (I sym srt : List Nat) : Bool :=
  let cs := ((kernelSyms c).filter fun k => k.args.isEmpty).map fun k => sym.getD k.name 1
  (iteSyms c I).all fun k =>
    (match instDecode? (c.symName k.name) with
      | some (_, xs) => xs.all fun x => srt.contains (strCode x)
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, xs) => (iteSyms c I).all fun k' =>
          match instDecode? (c.symName k'.name) with
          | some (h', xs') => h' != h || xs'.length == xs.length
          | none => true
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, _) => h != "inj"
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, _) => !cs.contains (strCode h)
      | none => true)

theorem itesApart_of_codes {c : Semantics} {sym srt I : List Nat} (hc : (allSymNames c).map strCode = sym)
    (hs : (allSortNames c).map strCode = srt) (hI : instIdx sym = I) (h : itesApartC c I sym srt = true) :
    itesApart c = true := by
  subst hI
  have hmem : ∀ k ∈ kernelSyms c, instDecode? (c.symName k.name) ≠ none → k ∈ iteSyms c (instIdx sym) :=
    fun k hk hn => List.mem_filter.mpr ⟨hk, by simpa using mem_instIdx hc hn⟩
  simp only [itesApart, List.all_eq_true]
  intro k hk
  cases hd : instDecode? (c.symName k.name) with
  | none => rfl
  | some p =>
    obtain ⟨hh, xs⟩ := p
    have hks := hmem k hk (by rw [hd]; exact Option.some_ne_none _)
    have hk' := List.all_eq_true.mp h k hks
    simp only [hd, Bool.and_eq_true, List.all_eq_true] at hk' ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk'
    refine ⟨⟨⟨fun x hx => ?_, fun k' hk'' => ?_⟩, h3⟩, fun k' hk'' => ?_⟩
    · have := h1 x hx
      simp only [List.contains_iff_mem] at this
      obtain ⟨i, hi, hiX⟩ := List.getElem_of_mem this
      rw [← strCode_getD hs hi, ← sortName_eq_getD] at hiX
      have hi' : i < nRegSorts + c.sortNames.length := by
        rw [← allSortNames_length, ← List.length_map (f := strCode), hs]; exact hi
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨i, by simpa [kernelSorts] using hi', strCode_inj hiX⟩
    · cases hd' : instDecode? (c.symName k'.name) with
      | none => rfl
      | some p' =>
        have := h2 k' (hmem k' hk'' (by rw [hd']; exact Option.some_ne_none _))
        rw [hd'] at this
        exact this
    · cases ha : k'.args.isEmpty with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or, bne_iff_ne, ne_eq]
        intro hn
        have hm : strCode hh ∈ ((kernelSyms c).filter fun k => k.args.isEmpty).map fun k => sym.getD k.name 1 :=
          List.mem_map.mpr ⟨k', List.mem_filter.mpr ⟨hk'', ha⟩, by rw [← strCode_symName_getD hc, hn]⟩
        rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at h4
        exact h4 hm

/-! ## `namesApartK` -/

/-- The entries of `as`, numbered from n, at the positions `is`, ascending: one pass over `as`. -/
def pick : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: _, [], _ => []
  | i :: is, a :: as, n => if i == n then a :: pick is as (n + 1) else pick (i :: is) as (n + 1)

theorem pick_eq : ∀ (as is : List Nat) (n : Nat), is.Pairwise (· < ·) →
    (∀ i ∈ is, n ≤ i ∧ i < n + as.length) → pick is as n = is.map fun i => as.getD (i - n) 1
  | [], [], _, _, _ => rfl
  | [], i :: _, n, _, hb => by have := hb i (List.mem_cons_self ..); simp at this; omega
  | _ :: _, [], _, _, _ => rfl
  | a :: as, i :: is, n, hp, hb => by
    have hi := hb i (List.mem_cons_self ..)
    have hgt : ∀ j ∈ is, i < j := fun _ hj => List.rel_of_pairwise_cons hp hj
    have hp' := hp.of_cons
    simp only [pick]
    by_cases hin : i = n
    · subst hin
      simp only [beq_self_eq_true, ↓reduceIte, List.map_cons, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [pick_eq as is (i + 1) hp' fun j hj => by
        have := hgt j hj; have := (hb j (List.mem_cons_of_mem _ hj)).2; simp at this; omega]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      have := hgt j hj
      rw [show j - i = (j - (i + 1)) + 1 by omega, List.getD_cons_succ]
    · have hne : (i == n) = false := by simpa using hin
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [pick_eq as (i :: is) (n + 1) hp fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · simp at hi; omega
        · have := hgt j hj; have := (hb j (List.mem_cons_of_mem _ hj)).2; simp at this hi; omega]
      refine List.map_congr_left fun j hj => ?_
      have hj' : n < j := by
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · have := hgt j hj; omega
      rw [show j - n = (j - (n + 1)) + 1 by omega, List.getD_cons_succ]

/-- `namesApartK` on codes: the symbol numbers of `kernelSyms`, sorted, ascend (so they are distinct)
and are numbered; the codes of their names, picked from the codes of all numbered symbols' names
in one pass (`pick`), are distinct and none is `"inj"`'s; and the codes of all numbered sorts'
names are distinct. Distinctness by the sorted numbers (`ascending`). (The numbered symbols'
names need not all be distinct: a library projection the text applies is the definition's own
symbol and keeps the registry's name.) -/
def namesApartC (c : Semantics) (sym srt : List Nat) : Bool :=
  let ns := msort (passesFor (kernelSyms c).length) ((kernelSyms c).map (·.name))
  let pc := pick ns sym 0
  ascending ns && ns.all (fun i => decide (i < sym.length)) &&
  ascending (msort (passesFor pc.length) pc) && !pc.contains (strCode "inj") &&
  ascending (msort (passesFor srt.length) srt)

theorem namesApartK_of_codes {c : Semantics} {sym srt : List Nat} (hc : (allSymNames c).map strCode = sym)
    (hs : (allSortNames c).map strCode = srt) (h : namesApartC c sym srt = true) : namesApartK c = true := by
  simp only [namesApartC, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  generalize hns : msort (passesFor (kernelSyms c).length) ((kernelSyms c).map (·.name)) = ns at h1 h2 h3 h4
  have hperm : ns.Perm ((kernelSyms c).map (·.name)) := hns ▸ msort_perm _ _
  have hpw := pairwise_of_ascending h1
  have n0 : ((kernelSyms c).map (·.name)).Nodup := hperm.nodup_iff.mp (hpw.imp Nat.ne_of_lt)
  have hpick : pick ns sym 0 = ns.map fun i => sym.getD i 1 := by
    rw [pick_eq sym ns 0 hpw fun i hi => ⟨Nat.zero_le _, by simpa using h2 i hi⟩]
    simp
  rw [hpick] at h3 h4
  have n3 := (msort_perm _ _).nodup_iff.mp ((pairwise_of_ascending h3).imp Nat.ne_of_lt)
  have n5 := nodup_of_ascending h5
  have mem : ∀ k ∈ kernelSyms c, k.name ∈ ns := fun k hk => hperm.mem_iff.mpr (List.mem_map_of_mem hk)
  have code : ∀ k ∈ kernelSyms c, strCode (c.symName k.name) = sym.getD k.name 1 := fun k hk => by
    have hl := h2 k.name (mem k hk)
    rw [symName_eq_getD, strCode_getD hc hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
      Option.getD_some]
  simp only [namesApartK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  refine ⟨⟨fun k hk k' hk' => ?_, fun k hk => ?_⟩, fun s hs' s' hs'' => ?_⟩
  · by_cases he : c.symName k.name = c.symName k'.name
    · right
      have hcode := code k hk
      rw [he, code k' hk'] at hcode
      have hnm := inj_of_nodup_map (f := fun i => sym.getD i 1) n3 _ (mem k hk) _ (mem k' hk') hcode.symm
      exact inj_of_nodup_map (f := fun k : CtorSig => k.name) n0 k hk k' hk' hnm
    · exact Or.inl he
  · intro he
    have hcode := code k hk
    rw [he] at hcode
    have hm : strCode "inj" ∈ ns.map fun i => sym.getD i 1 := by
      rw [hcode]; exact List.mem_map_of_mem (mem k hk)
    rw [List.contains_iff_mem.mpr hm] at h4
    cases h4
  · have hlen : srt.length = nRegSorts + c.sortNames.length := by
      rw [← hs, List.length_map, allSortNames_length]
    have hsl : s < srt.length := by rw [hlen]; simpa [kernelSorts] using hs'
    have hsl' : s' < srt.length := by rw [hlen]; simpa [kernelSorts] using hs''
    by_cases he : c.sortName s = c.sortName s'
    · right
      have h1' := strCode_getD hs hsl
      have h2' := strCode_getD hs hsl'
      rw [← sortName_eq_getD] at h1' h2'
      rw [he] at h1'
      exact eq_of_nodup_getElem n5 hsl hsl' (h1'.symm.trans h2')
    · exact Or.inl he

end Model

end Faithful

open Faithful Faithful.Model in
/-- `faithCoreOK` from its conjuncts, each a decision of its own; the names' apartness as
`namesApartK` (which `namesApartK_of_codes` gives), not by `namesApartFast`. -/
theorem Semantics.faithCoreOK_of_partsK {c : Semantics} (h1 : namesNumbered c = true) (h2 : genWf c = true)
    (h3 : collSortsOK c = true) (h4 : collsOK c = true) (h5 : patHeadsOK c = true)
    (h6 : namesApartK c = true) (h7 : LitsApart c = true) (h8 : sortsNumbered c = true)
    (h10 : itesApart c = true) (h11 : kindsApart c = true) (h12 : ctorsOnce c = true)
    (h13 : fnsApart c = true) : c.faithCoreOK = true := by
  simp only [Semantics.faithCoreOK, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, Bool.and_self]

end KCore
