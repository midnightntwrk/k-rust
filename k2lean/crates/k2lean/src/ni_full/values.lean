/-! ## The values (`KResult`): low, quiet, typed by both stack typings -/

/-- An item that is a value. -/
def isRes : @KIT@ → Bool
@ARMS@
  | _ => false

@[simp] theorem and_true_left (x : Bool) : BoolHook.and true x = x := by
  cases x <;> rfl

/-- `isKResult` of one item: it is a value. -/
@[simp] theorem isKResult_eq (y : @KIT@) : @NA@.K.isKResult (.kseq y .dotk) = isRes y := by
  k2l_cases y <;> simp [@NA@.K.isKResult, @NA@.K.isKResult.rule1, isRes, @NA@.proj_KItem_KResult]

/-- An injection through `@VS@` is the injection. -/
@[simp] theorem inj_@HS@_@VS@_KItem (V : @NA@.Sort@VS@) :
    @NA@.inj_@HS@_KItem (@NA@.inj_@VS@_@HS@ V) = @NA@.inj_@VS@_KItem V := by
  k2l_cases V <;> rfl

@[simp] theorem inj_@HS@_KItem_own (o : @OWN@) :
    @NA@.inj_@HS@_KItem (@HOLE@.inj_@HS@ o) = @KIT@.inj_@HS@ o := rfl

@[simp] theorem isRes_own (o : @OWN@) : isRes (@KIT@.inj_@HS@ o) = false := rfl

/-- An item that is an injected term of the form `o`: the term is `o`. -/
@[simp] theorem inj_@HS@_eq_inj_@HS@_KItem (o : @OWN@) (e : @HOLE@) :
    @KIT@.inj_@HS@ o = @NA@.inj_@HS@_KItem e ↔ e = @HOLE@.inj_@HS@ o := by
  k2l_cases e <;> simp [@NA@.inj_@HS@_KItem, eq_comm]

theorem citem0_of_res (G : Lab) {v : @KIT@} (h : isRes v = true) : citem0 G v = some true := by
  k2l_cases v <;> simp_all [isRes@CLEAVES@]

theorem litem0_of_res (G : Lab) {v : @KIT@} (h : isRes v = true) : litem0 G v = some true := by
  k2l_cases v <;> simp_all [isRes@LLEAVES@]

@[simp] theorem lev_inj_@VS@ (G : Lab) (V : @NA@.Sort@VS@) :
    @LEV@ G (@NA@.inj_@VS@_@HS@ V) = some @LO@ := by
  k2l_cases V <;> first@LEVCASES@
@QUIETVAL@
@[simp] theorem litem0_inj_@VS@ (G : Lab) (V : @NA@.Sort@VS@) :
    litem0 G (@NA@.inj_@VS@_KItem V) = some true := by
  k2l_cases V <;> exact litem0_of_res G rfl

@[simp] theorem citem0_inj_@VS@ (G : Lab) (V : @NA@.Sort@VS@) :
    citem0 G (@NA@.inj_@VS@_KItem V) = some true := by
  k2l_cases V <;> exact citem0_of_res G rfl

/-- A term whose item is a value is an injected value. -/
theorem isRes_@HS@_iff (e : @HOLE@) :
    isRes (@NA@.inj_@HS@_KItem e) = true ↔ ∃ V, e = @NA@.inj_@VS@_@HS@ V := by
  constructor
  · intro h
    k2l_cases e <;> rename_i v <;> first@WITCASES@
      | cases h
  · rintro ⟨V, rfl⟩
    k2l_cases V <;> rfl

theorem toList_concat_element (l : @NA@.SortList) (x : @KIT@) :
    ListIso.toList (ListHook.concat l (ListHook.element x)) = ListIso.toList l ++ [x] := by
  simp [ListHook.concat, ListHook.element, ListIso.toList_ofList]

