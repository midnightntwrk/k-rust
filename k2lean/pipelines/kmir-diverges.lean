import KMir.Functions
import KPrelude.Tactic

/-! The functions of KMIR's concrete target that are least fixed points of their equations
(`kmir-termination.toml`) have no value on a type table that contains a cycle: K declares them
`total`, but its rewriting does not terminate there. Each theorem below is proved by the
function's fixpoint induction, with a motive at the arguments on the cycle; the lemmas before
them show that the other calls on the way are defined, so that `none` comes from the cycle and
from nothing else. A mutual group is one least fixed point, so one theorem covers the group: the
motives of its members off the cycle are `True` (`#pointeeProjectionTarget`; the four other members
of the decoding group). `kmir.sh check` elaborates this file against the generated library. -/

namespace KMir
open KPrelude

/-- `ty(0)`, `ty(1)`. -/
abbrev ty0 : SortTy := SortTy.ty 0
abbrev ty1 : SortTy := SortTy.ty 1

/-- An array of `ty(0)` of unknown length. -/
abbrev arrNo : SortTypeInfo := SortTypeInfo.«TypeInfo::ArrayType» ty0 SortMaybeTyConst.noTyConst

/-- The length 2 as a constant: one byte of type `u8` (`ty(1)`). -/
abbrev two : SortTyConstKind :=
  SortTyConstKind.«TyConstKind::Value» ty1
    (SortAllocation.allocation (SortMIRBytes.inj_Bytes [2])
      (SortProvenanceMap.provenanceMap SortProvenanceMapEntries.«ProvenanceMapEntries::empty»)
      (SortAlign.align 1) SortMutability.«Mutability::Not»)

/-- An array of two `ty(0)`. -/
abbrev arr2 : SortTypeInfo :=
  SortTypeInfo.«TypeInfo::ArrayType» ty0
    (SortMaybeTyConst.«someTyConst(_)» (SortTyConst.«tyConst(_,_)» two (SortTyConstId.«tyConstId(_)» 0)))

/-- `u8`. -/
abbrev u8 : SortTypeInfo :=
  SortTypeInfo.«TypeInfo::PrimitiveType» (SortPrimitiveType.«PrimitiveType::Uint» SortUintTy.«UintTy::U8»)

/-- A struct of 8 bytes whose one field, at offset 0, has the type `ty(0)`. -/
abbrev wrap : SortTypeInfo :=
  SortTypeInfo.«TypeInfo::StructType» (SortMIRString.inj_String "W") (SortAdtDef.«adtDef(_)» 0)
    (SortTys.«Tys::append» ty0 SortTys.«Tys::empty»)
    (SortMaybeLayoutShape.«someLayoutShape(_)»
      (SortLayoutShape.«layoutShape(_,_,_,_,_)»
        (SortFieldsShape.«FieldsShape::Arbitrary»
          (SortFieldsShapeArbitrary.«mk(_)»
            (SortMachineSizes.«MachineSizes::append» (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 0))
              SortMachineSizes.«MachineSizes::empty»)))
        (SortVariantsShape.«VariantsShape::Single» (SortVariantsShapeSingle.«mk(_)» (SortVariantIdx.variantIdx 0)))
        SortValueAbi.«ValueAbi::ScalarPair» (SortAlign.align 8)
        (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 64))))

/-- A table with the one entry `ty(0) |-> T`, and `ty(1) |-> u8`. -/
abbrev table (t : SortTypeInfo) : SortMaybeMap :=
  SortMaybeMap.«MaybeMap::someMap»
    (MapHook.ofEntries [(SortKItem.inj_Ty ty0, SortKItem.inj_TypeInfo t), (SortKItem.inj_Ty ty1, SortKItem.inj_TypeInfo u8)])

theorem lookup0 (t : SortTypeInfo) : K.«lookupTy(_,_)_RT-VALUE-SYNTAX_TypeInfo_MaybeMap_Ty» (table t) ty0 = some t := by
  rfl

/-- The length constant is defined: 2. -/
theorem two_val : K.«readTyConstInt(_,_)_RT-TYPES_Int_MaybeMap_TyConstKind» (table arr2) two = some 2 := by
  decide

/-- `#alignOf(M, [ty(0)])` needs `#alignOf(M, lookupTy(M, ty(0)))`, the same call. -/
theorem alignOf_diverges : K.«#alignOf(_,_)_RT-TYPES_Int_MaybeMap_TypeInfo» (table arrNo) arrNo = none := by
  refine K.«#alignOf(_,_)_RT-TYPES_Int_MaybeMap_TypeInfo».fixpoint_induct (table arrNo) (fun f => f arrNo = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun f h => ?_)
  simp [lookup0, h]

/-- `#sizeOf(M, [ty(0); 2])` is `#sizeOf(M, lookupTy(M, ty(0))) *Int 2`, the same call times 2. -/
theorem sizeOf_diverges : K.«#sizeOf(_,_)_RT-TYPES_Int_MaybeMap_TypeInfo» (table arr2) arr2 = none := by
  refine K.«#sizeOf(_,_)_RT-TYPES_Int_MaybeMap_TypeInfo».fixpoint_induct (table arr2) (fun f => f arr2 = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun f h => ?_)
  simp [lookup0, h]

/-- `#elemSize(M, [ty(0); 2])` is `#elemSize(M, lookupTy(M, ty(0))) *Int 2`, likewise. -/
theorem arr2_not_int : K.«#isIntType(_)_RT-NUMBERS_Bool_TypeInfo» arr2 = false := by
  decide

theorem elemSize_diverges : K.«#elemSize(_,_)_RT-DECODING_Int_MaybeMap_TypeInfo» (table arr2) arr2 = none := by
  refine K.«#elemSize(_,_)_RT-DECODING_Int_MaybeMap_TypeInfo».fixpoint_induct (table arr2) (fun f => f arr2 = none)
    (Lean.Order.admissible_apply (fun _ v => v = none) _ (Lean.Order.admissible_flatOrder _ rfl))
    (fun f h => ?_)
  simp [lookup0, h, arr2_not_int]

theorem u8_not_zst : K.«#zeroSizedType(_)_RT-TYPES_Bool_TypeInfo» u8 = false := by
  decide

theorem arrNo_not_zst : K.«#zeroSizedType(_)_RT-TYPES_Bool_TypeInfo» arrNo = false := by
  decide

/-- `#pointeeProjection(M, [ty(0)], u8)`: the types differ, neither is zero-sized, so the array
rule applies and needs `#pointeeProjection(M, lookupTy(M, ty(0)), u8)`, the same call; the
group's other member, `#pointeeProjectionTarget`, is not on the cycle (motive `True`). -/
theorem pointeeProjection_diverges :
    K.«#pointeeProjection(_,_,_)_RT-TYPES_MaybeProjectionElems_MaybeMap_TypeInfo_TypeInfo» (table arrNo) arrNo u8 = none := by
  refine K.«#pointeeProjection(_,_,_)_RT-TYPES_MaybeProjectionElems_MaybeMap_TypeInfo_TypeInfo».fixpoint_induct (table arrNo)
    (fun f => f arrNo u8 = none) (fun _ => True)
    (Lean.Order.admissible_apply (fun (_ : SortTypeInfo) (g : SortTypeInfo → Option SortMaybeProjectionElems) => g u8 = none) arrNo
      (Lean.Order.admissible_apply (fun _ v => v = none) u8 (Lean.Order.admissible_flatOrder _ rfl)))
    (Lean.Order.admissible_const_true)
    (fun f g hf _ => ?_) (by intros; trivial)
  simp [lookup0, hf, u8_not_zst, arrNo_not_zst, BoolHook.and, BoolHook.not]

abbrev b8 : SortBytes := [0, 0, 0, 0, 0, 0, 0, 0]

theorem elemSize_wrap : K.«#elemSize(_,_)_RT-DECODING_Int_MaybeMap_TypeInfo» (table wrap) wrap = some 8 := by
  rw [K.«#elemSize(_,_)_RT-DECODING_Int_MaybeMap_TypeInfo».eq_def]
  decide


abbrev tys0 : SortTys := SortTys.«Tys::append» ty0 SortTys.«Tys::empty»
abbrev off0 : SortMachineSizes :=
  SortMachineSizes.«MachineSizes::append» (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 0))
    SortMachineSizes.«MachineSizes::empty»

theorem wrap_not_int : K.«#isIntType(_)_RT-NUMBERS_Bool_TypeInfo» wrap = false := by
  decide

theorem offsets_wrap : K.«#layoutOffsets(_)_RT-TYPES_MachineSizes_MaybeLayoutShape»
    (SortMaybeLayoutShape.«someLayoutShape(_)»
      (SortLayoutShape.«layoutShape(_,_,_,_,_)»
        (SortFieldsShape.«FieldsShape::Arbitrary»
          (SortFieldsShapeArbitrary.«mk(_)»
            (SortMachineSizes.«MachineSizes::append» (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 0))
              SortMachineSizes.«MachineSizes::empty»)))
        (SortVariantsShape.«VariantsShape::Single» (SortVariantsShapeSingle.«mk(_)» (SortVariantIdx.variantIdx 0)))
        SortValueAbi.«ValueAbi::ScalarPair» (SortAlign.align 8)
        (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 64)))) = off0 := by
  decide

theorem msBytes0 : K.«#msBytes(_)_RT-DECODING_Int_MachineSize» (SortMachineSize.«MachineSize::num_bits» (SortMIRInt.inj_Int 0)) = some 0 := by
  decide

theorem needed_empty : K.«#neededBytesForOffsets(_,_,_)_RT-DECODING_Int_MaybeMap_Tys_MachineSizes» (table wrap)
    SortTys.«Tys::empty» SortMachineSizes.«MachineSizes::empty» = some 0 := by
  rw [K.«#neededBytesForOffsets(_,_,_)_RT-DECODING_Int_MaybeMap_Tys_MachineSizes».eq_def]

theorem needed_wrap : K.«#neededBytesForOffsets(_,_,_)_RT-DECODING_Int_MaybeMap_Tys_MachineSizes» (table wrap) tys0 off0 = some 8 := by
  rw [K.«#neededBytesForOffsets(_,_,_)_RT-DECODING_Int_MaybeMap_Tys_MachineSizes».eq_def]
  dsimp only
  split
  all_goals rename_i heq
  all_goals (repeat' split at heq)
  -- each split's equation, rewritten in turn: the offset is 0 bytes, the field's type `W`, its
  -- size 8, and the rest of the fields need 0 bytes
  all_goals simp only [msBytes0, lookup0, needed_empty, Option.some.injEq, reduceCtorEq] at *
  all_goals subst_vars
  all_goals simp only [elemSize_wrap, Option.some.injEq, reduceCtorEq] at *
  all_goals subst_vars
  all_goals (try simp_all [IntHook.max, IntHook.add])
  all_goals decide

theorem off0_ne : KEqHook.ne (SortK.kseq (SortKItem.inj_MachineSizes off0) SortK.dotk)
    (SortK.kseq (SortKItem.inj_MachineSizes SortMachineSizes.«MachineSizes::empty») SortK.dotk) = true := by
  decide

/-- The decoding group: `decodeValue(M, B, W)`, with `W` a struct of 8 bytes whose one field, at
offset 0, has the type `ty(0)` and `M` the table `ty(0) |-> W`, decodes the field by
`#decodeFieldsWithOffsets(M, B, ty(0), 0)`, which decodes the bytes 0 to 8 of `B`, that is `B`, as
`lookupTy(M, ty(0)) = W`: `decodeValue(M, B, W)` again. The other four members are not on the
cycle (motive `True`). -/
theorem decodeValue_diverges : K.decodeValue (table wrap) b8 wrap = none := by
  refine K.decodeValue.fixpoint_induct (table wrap) (fun _ => True) (fun _ => True)
    (fun f => f b8 wrap = none) (fun _ => True) (fun g => g b8 tys0 off0 = none) (fun _ => True)
    Lean.Order.admissible_const_true Lean.Order.admissible_const_true
    (Lean.Order.admissible_apply (fun (_ : SortBytes) (g : SortTypeInfo → Option SortEvaluation) => g wrap = none) b8
      (Lean.Order.admissible_apply (fun _ v => v = none) wrap (Lean.Order.admissible_flatOrder _ rfl)))
    Lean.Order.admissible_const_true
    (Lean.Order.admissible_apply (fun (_ : SortBytes) (g : SortTys → SortMachineSizes → Option SortList) => g tys0 off0 = none) b8
      (Lean.Order.admissible_apply (fun (_ : SortTys) (g : SortMachineSizes → Option SortList) => g off0 = none) tys0
        (Lean.Order.admissible_apply (fun _ v => v = none) off0 (Lean.Order.admissible_flatOrder _ rfl))))
    Lean.Order.admissible_const_true
    (by intros; trivial) (by intros; trivial) ?_ (by intros; trivial) ?_ (by intros; trivial)
  · intros
    simp_all [elemSize_wrap, wrap_not_int, offsets_wrap, needed_wrap, off0_ne, IntHook.ge, IntHook.eq, IntHook.le,
      BytesHook.length, BoolHook.and]
  · intros
    simp_all [lookup0, elemSize_wrap, msBytes0, IntHook.add, IntHook.ge, BytesHook.substr]


#k2l_assert_axioms KMir.alignOf_diverges
#k2l_assert_axioms KMir.two_val
#k2l_assert_axioms KMir.sizeOf_diverges
#k2l_assert_axioms KMir.elemSize_diverges
#k2l_assert_axioms KMir.pointeeProjection_diverges
#k2l_assert_axioms KMir.decodeValue_diverges

end KMir
