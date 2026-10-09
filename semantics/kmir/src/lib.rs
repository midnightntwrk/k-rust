//! Readable qualification slice for KMIR basic-block execution.
//!
//! The source mapping and adapter boundary are pinned in
//! `../../tests/kmir/source-map.md`.

use k::KResult;
use k::builtin::{Bool, Bytes, Int, KSequence, List, Map, String, bool, bytes, int, list, map};
#[allow(unused_imports)]
use k::map;

k::sorts! {
    MirValue: KResult;
    AllocId: k::KItem;
    MaybeTy: k::KItem;
    Ty: MaybeTy;
    IntTy: k::KItem;
    UintTy: k::KItem;
    FloatTy: k::KItem;
    PrimitiveType: k::KItem;
    TyConst: k::KItem;
    TyConstKind: k::KItem;
    TyConstId: k::KItem;
    Allocation: k::KItem;
    ProvenanceMap: k::KItem;
    Align: k::KItem;
    AdtDef: k::KItem;
    ClosureDef: k::KItem;
    GenericArg: k::KItem;
    GenericArgs: k::KItem;
    MaybeUserTypeAnnotationIndex: k::KItem;
    MaybeFieldIdx: k::KItem;
    AggregateKind: k::KItem;
    Tys: k::KItem;
    Tyss: k::KItem;
    Discriminant: k::KItem;
    Discriminants: k::KItem;
    MachineSize: k::KItem;
    MachineSizes: k::KItem;
    FieldsShapeArbitrary: k::KItem;
    FieldsShape: k::KItem;
    VariantsShapeSingle: k::KItem;
    LayoutShapes: k::KItem;
    IntegerLength: k::KItem;
    PrimitiveInt: k::KItem;
    AddressSpace: k::KItem;
    Primitive: k::KItem;
    WrappingRange: k::KItem;
    ScalarInitialized: k::KItem;
    Scalar: k::KItem;
    TagEncoding: k::KItem;
    VariantsShapeMultiple: k::KItem;
    VariantsShape: k::KItem;
    ValueAbiAggregate: k::KItem;
    ValueAbi: k::KItem;
    LayoutShape: k::KItem;
    MaybeLayoutShape: k::KItem;
    MaybeTyConst: k::KItem;
    TypeInfo: k::KItem;
    Mutability: k::KItem;
    Region: k::KItem;
    BorrowKind: k::KItem;
    MetadataSize: k::KItem;
    Metadata: k::KItem;
    TypedLocal: k::KItem;
    ProjectionElem: k::KItem;
    ProjectionElems: k::KItem;
    ProjectionTarget: k::KItem;
    ProjectionContext: k::KItem;
    ProjectionContexts: k::KItem;
    ProjectionAction: k::KItem;
    PtrCastPhase: k::KItem;
    Place: k::KItem;
    Operand: k::KItem;
    PointerCoercion: k::KItem;
    CastKind: k::KItem;
    UnaryOp: k::KItem;
    NullOp: k::KItem;
    BinaryOp: k::KItem;
    Rvalue: k::KItem;
    Statement: k::KItem;
    Statements: k::KItem;
    Branch: k::KItem;
    Branches: k::KItem;
    SwitchTargets: k::KItem;
    MaybeBasicBlockIdx: k::KItem;
    LocalDecl: k::KItem;
    LocalDecls: k::KItem;
    FunctionBody: k::KItem;
    Function: k::KItem;
    CallTarget: k::KItem;
    StackFrame: k::KItem;
    AssertMessage: k::KItem;
    UnwindAction: k::KItem;
    MirError: k::KItem;
    Terminator: k::KItem;
    BasicBlock: k::KItem;
    RetVal: k::KItem;
    Continuation: k::KItem;
    Command: k::KItem;
}

#[k::constructors(sort = AllocId, result = KResult)]
#[k::precedence((AllocId))]
pub enum MirAllocId {
    #[k::syntax("allocId({id})")]
    AllocId { id: Int },
}

#[k::constructors(sort = Ty, result = KResult)]
#[k::precedence((TyId))]
pub enum MirTy {
    #[k::syntax("ty({id})")]
    TyId { id: Int },
}

#[k::constructors(sort = MaybeTy, result = KResult)]
#[k::precedence((TyUnknown))]
pub enum MirMaybeTy {
    #[k::syntax("TyUnknown")]
    TyUnknown(),
}

#[k::constructors(sort = IntTy, result = KResult)]
#[k::precedence((Isize, I8, I16, I32, I64, I128))]
pub enum MirIntTy {
    #[k::syntax("intTyIsize")]
    Isize(),
    #[k::syntax("intTyI8")]
    I8(),
    #[k::syntax("intTyI16")]
    I16(),
    #[k::syntax("intTyI32")]
    I32(),
    #[k::syntax("intTyI64")]
    I64(),
    #[k::syntax("intTyI128")]
    I128(),
}

#[k::constructors(sort = UintTy, result = KResult)]
#[k::precedence((Usize, U8, U16, U32, U64, U128))]
pub enum MirUintTy {
    #[k::syntax("uintTyUsize")]
    Usize(),
    #[k::syntax("uintTyU8")]
    U8(),
    #[k::syntax("uintTyU16")]
    U16(),
    #[k::syntax("uintTyU32")]
    U32(),
    #[k::syntax("uintTyU64")]
    U64(),
    #[k::syntax("uintTyU128")]
    U128(),
}

#[k::constructors(sort = FloatTy, result = KResult)]
#[k::precedence((F16, F32, F64, F128))]
pub enum MirFloatTy {
    #[k::syntax("floatTyF16")]
    F16(),
    #[k::syntax("floatTyF32")]
    F32(),
    #[k::syntax("floatTyF64")]
    F64(),
    #[k::syntax("floatTyF128")]
    F128(),
}

#[k::constructors(sort = PrimitiveType, result = KResult)]
#[k::precedence((Bool, Char, SignedInteger, UnsignedInteger, Float, Str))]
pub enum MirPrimitiveType {
    #[k::syntax("primTypeBool")]
    Bool(),
    #[k::syntax("primTypeChar")]
    Char(),
    #[k::syntax("primTypeInt({kind})")]
    SignedInteger { kind: IntTy },
    #[k::syntax("primTypeUint({kind})")]
    UnsignedInteger { kind: UintTy },
    #[k::syntax("primTypeFloat({kind})")]
    Float { kind: FloatTy },
    #[k::syntax("primTypeStr")]
    Str(),
}

#[k::constructors(sort = TyConstId, result = KResult)]
#[k::precedence((TyConstId))]
pub enum MirTyConstId {
    #[k::syntax("tyConstId({id})")]
    TyConstId { id: Int },
}

#[k::constructors(sort = ProvenanceMap, result = KResult)]
#[k::precedence((EmptyProvenanceMap, SingletonProvenanceMap))]
pub enum MirProvenanceMap {
    #[k::syntax("provenanceMap(.ProvenanceMapEntries)")]
    EmptyProvenanceMap(),
    #[k::syntax("provenanceMap(provenanceMapEntry({offset}, {allocation}) .ProvenanceMapEntries)")]
    SingletonProvenanceMap { offset: Int, allocation: AllocId },
}

#[k::constructors(sort = Align, result = KResult)]
#[k::precedence((Align))]
pub enum MirAlign {
    #[k::syntax("align({bytes})")]
    Align { bytes: Int },
}

#[k::constructors(sort = AdtDef, result = KResult)]
#[k::precedence((AdtDef))]
pub enum MirAdtDef {
    #[k::syntax("adtDef({id})")]
    AdtDef { id: Int },
}

#[k::constructors(sort = ClosureDef, result = KResult)]
#[k::precedence((ClosureDef))]
pub enum MirClosureDef {
    #[k::syntax("closureDef({id})")]
    ClosureDef { id: Int },
}

#[k::constructors(sort = GenericArg, result = KResult)]
#[k::precedence((GenericArgLifetime, GenericArgType, GenericArgConst))]
pub enum MirGenericArg {
    #[k::syntax("genericArgKindLifetime({region})")]
    GenericArgLifetime { region: Region },
    #[k::syntax("genericArgKindType({ty})")]
    GenericArgType { ty: Ty },
    #[k::syntax("genericArgKindConst({value})")]
    GenericArgConst { value: TyConst },
}

#[k::constructors(sort = GenericArgs, result = KResult)]
#[k::precedence((GenericArgsEmpty, GenericArgsCons))]
pub enum MirGenericArgs {
    #[k::syntax(".GenericArgs")]
    GenericArgsEmpty(),
    #[k::syntax("{head} {tail}")]
    GenericArgsCons { head: GenericArg, tail: GenericArgs },
}

#[k::constructors(sort = MaybeUserTypeAnnotationIndex, result = KResult)]
#[k::precedence((NoUserTypeAnnotationIndex, SomeUserTypeAnnotationIndex))]
pub enum MirMaybeUserTypeAnnotationIndex {
    #[k::syntax("noUserTypeAnnotationIndex")]
    NoUserTypeAnnotationIndex(),
    #[k::syntax("someUserTypeAnnotationIndex(userTypeAnnotationIndex({index}))")]
    SomeUserTypeAnnotationIndex { index: Int },
}

#[k::constructors(sort = MaybeFieldIdx, result = KResult)]
#[k::precedence((NoFieldIdx, SomeFieldIdx))]
pub enum MirMaybeFieldIdx {
    #[k::syntax("noFieldIdx")]
    NoFieldIdx(),
    #[k::syntax("someFieldIdx(fieldIdx({index}))")]
    SomeFieldIdx { index: Int },
}

#[k::constructors(sort = AggregateKind, result = KResult)]
#[k::precedence((
    AggregateArray,
    AggregateTuple,
    AggregateAdt,
    AggregateClosure,
    AggregateRawPointer,
))]
pub enum MirAggregateKind {
    #[k::syntax("aggregateKindArray({ty})")]
    AggregateArray { ty: Ty },
    #[k::syntax("aggregateKindTuple")]
    AggregateTuple(),
    #[k::syntax("aggregateKindAdt({adt}, variantIdx({variant}), {args}, {user_ty}, {field})")]
    AggregateAdt {
        adt: AdtDef,
        variant: Int,
        args: GenericArgs,
        user_ty: MaybeUserTypeAnnotationIndex,
        field: MaybeFieldIdx,
    },
    #[k::syntax("aggregateKindClosure({closure}, {args})")]
    AggregateClosure {
        closure: ClosureDef,
        args: GenericArgs,
    },
    #[k::syntax("aggregateKindRawPtr({ty}, {mutability})")]
    AggregateRawPointer { ty: Ty, mutability: Mutability },
}

#[k::constructors(sort = Tys, result = KResult)]
#[k::precedence((TysEmpty, TysCons))]
pub enum MirTys {
    #[k::syntax(".Tys")]
    TysEmpty(),
    #[k::syntax("{head} {tail}")]
    TysCons { head: Ty, tail: Tys },
}

#[k::constructors(sort = Tyss, result = KResult)]
#[k::precedence((TyssEmpty, TyssCons))]
pub enum MirTyss {
    #[k::syntax(".Tyss")]
    TyssEmpty(),
    #[k::syntax("{head} : {tail}")]
    TyssCons { head: Tys, tail: Tyss },
}

#[k::constructors(sort = Discriminant, result = KResult)]
#[k::precedence((Discriminant))]
pub enum MirDiscriminant {
    #[k::syntax("discriminant({value})")]
    Discriminant { value: Int },
}

#[k::constructors(sort = Discriminants, result = KResult)]
#[k::precedence((DiscriminantsEmpty, DiscriminantsCons))]
pub enum MirDiscriminants {
    #[k::syntax(".Discriminants")]
    DiscriminantsEmpty(),
    #[k::syntax("{head} {tail}")]
    DiscriminantsCons {
        head: Discriminant,
        tail: Discriminants,
    },
}

#[k::constructors(sort = MachineSize, result = KResult)]
#[k::precedence((MachineSize))]
pub enum MirMachineSize {
    #[k::syntax("machineSize({bits})")]
    MachineSize { bits: Int },
}

#[k::constructors(sort = MachineSizes, result = KResult)]
#[k::precedence((MachineSizesEmpty, MachineSizesCons))]
pub enum MirMachineSizes {
    #[k::syntax(".MachineSizes")]
    MachineSizesEmpty(),
    #[k::syntax("{head} {tail}")]
    MachineSizesCons {
        head: MachineSize,
        tail: MachineSizes,
    },
}

#[k::constructors(sort = FieldsShapeArbitrary, result = KResult)]
#[k::precedence((ArbitraryFields))]
pub enum MirFieldsShapeArbitrary {
    #[k::syntax("mk({offsets})")]
    ArbitraryFields { offsets: MachineSizes },
}

#[k::constructors(sort = FieldsShape, result = KResult)]
#[k::precedence((FieldsShapeArbitrary))]
pub enum MirFieldsShape {
    #[k::syntax("fieldsShapeArbitrary({fields})")]
    FieldsShapeArbitrary { fields: FieldsShapeArbitrary },
}

#[k::constructors(sort = VariantsShapeSingle, result = KResult)]
#[k::precedence((SingleVariant))]
pub enum MirVariantsShapeSingle {
    #[k::syntax("mk(variantIdx({index}))")]
    SingleVariant { index: Int },
}

#[k::constructors(sort = LayoutShapes, result = KResult)]
#[k::precedence((LayoutShapesEmpty, LayoutShapesCons))]
pub enum MirLayoutShapes {
    #[k::syntax(".LayoutShapes")]
    LayoutShapesEmpty(),
    #[k::syntax("{head} {tail}")]
    LayoutShapesCons {
        head: LayoutShape,
        tail: LayoutShapes,
    },
}

#[k::constructors(sort = IntegerLength, result = KResult)]
#[k::precedence((LengthI8, LengthI16, LengthI32, LengthI64, LengthI128))]
pub enum MirIntegerLength {
    #[k::syntax("integerLengthI8")]
    LengthI8(),
    #[k::syntax("integerLengthI16")]
    LengthI16(),
    #[k::syntax("integerLengthI32")]
    LengthI32(),
    #[k::syntax("integerLengthI64")]
    LengthI64(),
    #[k::syntax("integerLengthI128")]
    LengthI128(),
}

#[k::constructors(sort = PrimitiveInt, result = KResult)]
#[k::precedence((PrimitiveInt))]
pub enum MirPrimitiveInt {
    #[k::syntax("mk({length}, {signed})")]
    PrimitiveInt { length: IntegerLength, signed: Bool },
}

#[k::constructors(sort = AddressSpace, result = KResult)]
#[k::precedence((AddressSpace))]
pub enum MirAddressSpace {
    #[k::syntax("addressSpace({id})")]
    AddressSpace { id: Int },
}

#[k::constructors(sort = Primitive, result = KResult)]
#[k::precedence((IntegerPrimitive, PointerPrimitive))]
pub enum MirPrimitive {
    #[k::syntax("primitiveInt({integer})")]
    IntegerPrimitive { integer: PrimitiveInt },
    #[k::syntax("primitivePointer({address_space})")]
    PointerPrimitive { address_space: AddressSpace },
}

#[k::constructors(sort = WrappingRange, result = KResult)]
#[k::precedence((WrappingRange))]
pub enum MirWrappingRange {
    #[k::syntax("wrappingRange({start}, {end})")]
    WrappingRange { start: Int, end: Int },
}

#[k::constructors(sort = ScalarInitialized, result = KResult)]
#[k::precedence((ScalarInitializedFields))]
pub enum MirScalarInitialized {
    #[k::syntax("mk({value}, {valid_range})")]
    ScalarInitializedFields {
        value: Primitive,
        valid_range: WrappingRange,
    },
}

#[k::constructors(sort = Scalar, result = KResult)]
#[k::precedence((InitializedScalar))]
pub enum MirScalar {
    #[k::syntax("scalarInitialized({scalar})")]
    InitializedScalar { scalar: ScalarInitialized },
}

#[k::constructors(sort = TagEncoding, result = KResult)]
#[k::precedence((Direct, Niche))]
pub enum MirTagEncoding {
    #[k::syntax("tagEncodingDirect")]
    Direct(),
    #[k::syntax("tagEncodingNiche()")]
    Niche(),
}

#[k::constructors(sort = VariantsShapeMultiple, result = KResult)]
#[k::precedence((MultipleVariants))]
pub enum MirVariantsShapeMultiple {
    #[k::syntax("mk({tag}, {tag_encoding}, {tag_field}, {variants})")]
    MultipleVariants {
        tag: Scalar,
        tag_encoding: TagEncoding,
        tag_field: Int,
        variants: LayoutShapes,
    },
}

#[k::constructors(sort = VariantsShape, result = KResult)]
#[k::precedence((VariantsShapeSingle, VariantsShapeMultiple))]
pub enum MirVariantsShape {
    #[k::syntax("variantsShapeSingle({variant})")]
    VariantsShapeSingle { variant: VariantsShapeSingle },
    #[k::syntax("variantsShapeMultiple({variants})")]
    VariantsShapeMultiple { variants: VariantsShapeMultiple },
}

#[k::constructors(sort = ValueAbiAggregate, result = KResult)]
#[k::precedence((AggregateAbi))]
pub enum MirValueAbiAggregate {
    #[k::syntax("mk({sized})")]
    AggregateAbi { sized: Bool },
}

#[k::constructors(sort = ValueAbi, result = KResult)]
#[k::precedence((ValueAbiScalar, ValueAbiAggregate))]
pub enum MirValueAbi {
    #[k::syntax("valueAbiScalar({scalar})")]
    ValueAbiScalar { scalar: Scalar },
    #[k::syntax("valueAbiAggregate({aggregate})")]
    ValueAbiAggregate { aggregate: ValueAbiAggregate },
}

#[k::constructors(sort = LayoutShape, result = KResult)]
#[k::precedence((LayoutShape))]
pub enum MirLayoutShape {
    #[k::syntax("layoutShape({fields}, {variants}, {abi}, {abi_align}, {size})")]
    LayoutShape {
        fields: FieldsShape,
        variants: VariantsShape,
        abi: ValueAbi,
        abi_align: Align,
        size: MachineSize,
    },
}

#[k::constructors(sort = MaybeLayoutShape, result = KResult)]
#[k::precedence((SomeLayoutShape, NoLayoutShape))]
pub enum MirMaybeLayoutShape {
    #[k::syntax("someLayoutShape({layout})")]
    SomeLayoutShape { layout: LayoutShape },
    #[k::syntax("noLayoutShape")]
    NoLayoutShape(),
}

#[k::constructors(sort = Allocation, result = KResult)]
#[k::precedence((Allocation))]
pub enum MirAllocation {
    #[k::syntax("allocation({bytes}, {provenance}, {align}, {mutability})")]
    Allocation {
        bytes: Bytes,
        provenance: ProvenanceMap,
        align: Align,
        mutability: Mutability,
    },
}

#[k::constructors(sort = TyConstKind, result = KResult)]
#[k::precedence((Value))]
pub enum MirTyConstKind {
    #[k::syntax("tyConstKindValue({ty}, {allocation})")]
    Value { ty: Ty, allocation: Allocation },
}

#[k::constructors(sort = TyConst, result = KResult)]
#[k::precedence((TyConst))]
pub enum MirTyConst {
    #[k::syntax("tyConst({kind}, {id})")]
    TyConst { kind: TyConstKind, id: TyConstId },
}

#[k::constructors(sort = MaybeTyConst, result = KResult)]
#[k::precedence((SomeTyConst, NoTyConst))]
pub enum MirMaybeTyConst {
    #[k::syntax("someTyConst({value})")]
    SomeTyConst { value: TyConst },
    #[k::syntax("noTyConst")]
    NoTyConst(),
}

#[k::constructors(sort = TypeInfo, result = KResult)]
#[k::precedence((
    PrimitiveType,
    ArrayType,
    PointerType,
    ReferenceType,
    StructType,
    UnionType,
    TupleType,
    EnumType,
    DynamicType,
    FunType,
    VoidType,
))]
pub enum MirTypeInfo {
    #[k::syntax("typeInfoPrimitiveType({primitive})")]
    PrimitiveType { primitive: PrimitiveType },
    #[k::syntax("typeInfoArrayType({element}, {size})")]
    ArrayType { element: Ty, size: MaybeTyConst },
    #[k::syntax("typeInfoPtrType({pointee})")]
    PointerType { pointee: Ty },
    #[k::syntax("typeInfoRefType({pointee})")]
    ReferenceType { pointee: Ty },
    #[k::syntax("typeInfoStructType({name}, {adt_def}, {fields}, {layout})")]
    StructType {
        name: String,
        adt_def: AdtDef,
        fields: Tys,
        layout: MaybeLayoutShape,
    },
    #[k::syntax("typeInfoUnionType({name}, {adt_def}, {fields}, {layout})")]
    UnionType {
        name: String,
        adt_def: AdtDef,
        fields: Tys,
        layout: MaybeLayoutShape,
    },
    #[k::syntax("typeInfoTupleType({fields}, {layout})")]
    TupleType {
        fields: Tys,
        layout: MaybeLayoutShape,
    },
    #[k::syntax("typeInfoEnumType({name}, {adt_def}, {discriminants}, {fields}, {layout})")]
    EnumType {
        name: String,
        adt_def: AdtDef,
        discriminants: Discriminants,
        fields: Tyss,
        layout: MaybeLayoutShape,
    },
    #[k::syntax("TypeInfoDynType({name}, {layout})")]
    DynamicType {
        name: String,
        layout: MaybeLayoutShape,
    },
    #[k::syntax("typeInfoFunType({name})")]
    FunType { name: String },
    #[k::syntax("typeInfoVoidType")]
    VoidType(),
}

#[k::constructors(sort = Mutability, result = KResult)]
#[k::precedence((NotMutable, Mutable))]
pub enum LocalMutability {
    #[k::syntax("mutabilityNot")]
    NotMutable(),
    #[k::syntax("mutabilityMut")]
    Mutable(),
}

#[k::constructors(sort = Region, result = KResult)]
#[k::precedence((Erased))]
pub enum MirRegion {
    #[k::syntax("region(regionKindReErased)")]
    Erased(),
}

#[k::constructors(sort = BorrowKind, result = KResult)]
#[k::precedence((SharedBorrow, MutableBorrow))]
pub enum MirBorrowKind {
    #[k::syntax("borrowKindShared")]
    SharedBorrow(),
    #[k::syntax("borrowKindMut(mutBorrowKindDefault)")]
    MutableBorrow(),
}

#[k::constructors(sort = PointerCoercion, result = KResult)]
#[k::precedence((Unsize))]
pub enum MirPointerCoercion {
    #[k::syntax("pointerCoercionUnsize")]
    Unsize(),
}

#[k::constructors(sort = CastKind, result = KResult)]
#[k::precedence((PointerCoercion, PtrToPtr, Transmute))]
pub enum MirCastKind {
    #[k::syntax("castKindPointerCoercion({coercion})")]
    PointerCoercion { coercion: PointerCoercion },
    #[k::syntax("castKindPtrToPtr")]
    PtrToPtr(),
    #[k::syntax("castKindTransmute")]
    Transmute(),
}

#[k::constructors(sort = MetadataSize, result = KResult)]
#[k::precedence((NoMetadataSize, StaticSize, DynamicSize))]
pub enum MirMetadataSize {
    #[k::syntax("noMetadataSize")]
    NoMetadataSize(),
    #[k::syntax("staticSize({size})")]
    StaticSize { size: Int },
    #[k::syntax("dynamicSize({size})")]
    DynamicSize { size: Int },
}

#[k::constructors(sort = Metadata, result = KResult)]
#[k::precedence((Metadata))]
pub enum MirMetadata {
    #[k::syntax("metadata({size}, {offset}, {origin_size})")]
    Metadata {
        size: MetadataSize,
        offset: Int,
        origin_size: MetadataSize,
    },
}

#[k::constructors(sort = TypedLocal, result = KResult)]
#[k::precedence((NewLocal, TypedValue))]
pub enum LocalValue {
    #[k::syntax("newLocal({ty}, {mutability})")]
    NewLocal { ty: Ty, mutability: Mutability },
    #[k::syntax("typedValue({value}, {ty}, {mutability})")]
    TypedValue {
        value: MirValue,
        ty: Ty,
        mutability: Mutability,
    },
}

#[k::function(total, sort = Ty, syntax = "#localTy({entry})")]
pub struct LocalTy {
    pub entry: k::Term<TypedLocal>,
}

#[k::equation]
fn local_ty_new(
    k::term![LocalTy {
        entry: LocalValue::NewLocal { ty, mutability: _ },
    }]: k::Term<Ty>,
) -> k::Term<Ty> {
    ty
}

#[k::equation]
fn local_ty_value(
    k::term![LocalTy {
        entry: LocalValue::TypedValue {
            value: _,
            ty,
            mutability: _,
        },
    }]: k::Term<Ty>,
) -> k::Term<Ty> {
    ty
}

#[k::function(total, sort = MaybeTy, syntax = "pointeeTy({info})")]
pub struct PointeeTy {
    pub info: k::Term<TypeInfo>,
}

#[k::equation]
fn pointee_ty_pointer(
    k::term![PointeeTy {
        info: MirTypeInfo::PointerType { pointee },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    pointee
}

#[k::equation]
fn pointee_ty_reference(
    k::term![PointeeTy {
        info: MirTypeInfo::ReferenceType { pointee },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    pointee
}

#[k::equation(priority = 60)]
fn pointee_ty_other(k::term![PointeeTy { info: _ }]: k::Term<MaybeTy>) -> k::Term<MaybeTy> {
    k::term![MirMaybeTy::TyUnknown()]
}

#[k::function(total, sort = MaybeTy, syntax = "elemTy({info})")]
pub struct ElemTy {
    pub info: k::Term<TypeInfo>,
}

#[k::equation]
fn elem_ty_array(
    k::term![ElemTy {
        info: MirTypeInfo::ArrayType { element, size: _ },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    element
}

#[k::equation(priority = 60)]
fn elem_ty_other(k::term![ElemTy { info: _ }]: k::Term<MaybeTy>) -> k::Term<MaybeTy> {
    k::term![MirMaybeTy::TyUnknown()]
}

#[k::function(
    total,
    sort = MaybeTy,
    syntax = "getTyOf({types}, {ty}, {projections})"
)]
pub struct GetTyOf {
    pub types: k::Term<Map>,
    pub ty: k::Term<MaybeTy>,
    pub projections: k::Term<ProjectionElems>,
}

#[k::equation(priority = 40)]
fn get_ty_of_unknown(
    k::term![GetTyOf {
        types: _,
        ty: MirMaybeTy::TyUnknown(),
        projections: _,
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![MirMaybeTy::TyUnknown()]
}

#[k::equation]
fn get_ty_of_done(
    k::term![GetTyOf {
        types: _,
        ty,
        projections: Projections::ProjectionsEmpty(),
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    ty
}

#[k::equation]
fn get_ty_of_deref(
    k::term![GetTyOf {
        types,
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Deref(),
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty: PointeeTy {
            info: map::get(types, ty),
        },
        projections: tail,
    }]
}

#[k::equation]
fn get_ty_of_field(
    k::term![GetTyOf {
        types,
        ty: _,
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field: _, ty },
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty,
        projections: tail,
    }]
}

#[k::equation]
fn get_ty_of_index(
    k::term![GetTyOf {
        types,
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Index { local: _ },
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty: ElemTy {
            info: map::get(types, ty),
        },
        projections: tail,
    }]
}

#[k::equation]
fn get_ty_of_constant_index(
    k::term![GetTyOf {
        types,
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: _,
                min_length: _,
                from_end: _,
            },
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty: ElemTy {
            info: map::get(types, ty),
        },
        projections: tail,
    }]
}

#[k::equation]
fn get_ty_of_subslice(
    k::term![GetTyOf {
        types,
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from: _,
                to: _,
                from_end: _,
            },
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty,
        projections: tail,
    }]
}

#[k::equation]
fn get_ty_of_downcast(
    k::term![GetTyOf {
        types,
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Downcast { variant: _ },
            tail,
        },
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![GetTyOf {
        types,
        ty,
        projections: tail,
    }]
}

#[k::equation(priority = 60)]
fn get_ty_of_other(
    k::term![GetTyOf {
        types: _,
        ty: _,
        projections: _,
    }]: k::Term<MaybeTy>,
) -> k::Term<MaybeTy> {
    k::term![MirMaybeTy::TyUnknown()]
}

#[k::function(total, sort = TypeInfo, syntax = "#lookupMaybeTy({types}, {ty})")]
pub struct LookupMaybeTy {
    pub types: k::Term<Map>,
    pub ty: k::Term<MaybeTy>,
}

#[k::equation]
fn lookup_maybe_ty_known(
    k::term![LookupMaybeTy { types, ty }]: k::Term<TypeInfo>,
) -> k::Term<TypeInfo> {
    k::term![map::get(types, ty)]
}

#[k::equation]
fn lookup_maybe_ty_unknown(
    k::term![LookupMaybeTy {
        types: _,
        ty: MirMaybeTy::TyUnknown(),
    }]: k::Term<TypeInfo>,
) -> k::Term<TypeInfo> {
    k::term![MirTypeInfo::VoidType()]
}

#[k::function(total, sort = MetadataSize, syntax = "#metadataSizeOf({info})")]
pub struct MetadataSizeOf {
    pub info: k::Term<TypeInfo>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#readTyConstInt({bytes}, {index}, {multiplier}, {result})"
)]
pub struct ReadTyConstInt {
    pub bytes: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub multiplier: k::Term<Int>,
    pub result: k::Term<Int>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeAllocatedReference({allocation}, {bytes}, {stored}, {info}, {types})"
)]
pub struct DecodeAllocatedReference {
    pub allocation: k::Term<AllocId>,
    pub bytes: k::Term<Bytes>,
    pub stored: k::Term<MirValue>,
    pub info: k::Term<TypeInfo>,
    pub types: k::Term<Map>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#intWidth({kind})"
)]
pub struct IntWidth {
    pub kind: k::Term<IntTy>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#uintWidth({kind})"
)]
pub struct UintWidth {
    pub kind: k::Term<UintTy>,
}

#[k::function(partial, sort = Int, syntax = "#floatWidth({kind})")]
pub struct FloatWidth {
    pub kind: k::Term<FloatTy>,
}

#[k::function(total, sort = Int, syntax = "#sizeOf({types}, {info})")]
pub struct SizeOfTypeInfo {
    pub types: k::Term<Map>,
    pub info: k::Term<TypeInfo>,
}

#[k::function(total, sort = Int, syntax = "#alignOf({types}, {info})")]
pub struct AlignOfTypeInfo {
    pub types: k::Term<Map>,
    pub info: k::Term<TypeInfo>,
}

#[k::function(total, sort = Int, syntax = "#layoutSize({layout})")]
pub struct LayoutSize {
    pub layout: k::Term<MaybeLayoutShape>,
}

#[k::function(total, sort = Int, syntax = "#layoutAlign({layout})")]
pub struct LayoutAlign {
    pub layout: k::Term<MaybeLayoutShape>,
}

#[k::function(total, sort = Int, syntax = "#pointerWords({info})")]
pub struct PointerWords {
    pub info: k::Term<TypeInfo>,
}

#[k::function(total, sort = Bool, syntax = "#isVoidType({info})")]
pub struct IsVoidType {
    pub info: k::Term<TypeInfo>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeInteger({bytes}, {width}, {signed})"
)]
pub struct DecodeInteger {
    pub bytes: k::Term<Bytes>,
    pub width: k::Term<Int>,
    pub signed: k::Term<Bool>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeAllocatedValue({types}, {bytes}, {info})"
)]
pub struct DecodeAllocatedValue {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub info: k::Term<TypeInfo>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeZeroSizedConstant({info})"
)]
pub struct DecodeZeroSizedConstant {
    pub info: k::Term<TypeInfo>,
}

#[k::function(partial, sort = Int, syntax = "#elementSize({types}, {info})")]
pub struct ElementSize {
    pub types: k::Term<Map>,
    pub info: k::Term<TypeInfo>,
}

#[k::function(partial, sort = Int, syntax = "#maximum({first}, {second})")]
pub struct Maximum {
    pub first: k::Term<Int>,
    pub second: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#neededBytesForOffsets({types}, {fields}, {offsets})"
)]
pub struct NeededBytesForOffsets {
    pub types: k::Term<Map>,
    pub fields: k::Term<Tys>,
    pub offsets: k::Term<MachineSizes>,
}

#[k::function(
    partial,
    sort = List,
    syntax = "#decodeFieldsWithOffsets({types}, {bytes}, {fields}, {offsets})"
)]
pub struct DecodeFieldsWithOffsets {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub fields: k::Term<Tys>,
    pub offsets: k::Term<MachineSizes>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeArrayAllocation({types}, {bytes}, {info}, {length})"
)]
pub struct DecodeArrayAllocation {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub info: k::Term<TypeInfo>,
    pub length: k::Term<Int>,
}

#[k::function(
    partial,
    sort = List,
    syntax = "#decodeArrayElements({types}, {bytes}, {info}, {remaining}, {accumulated})"
)]
pub struct DecodeArrayElements {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub info: k::Term<TypeInfo>,
    pub remaining: k::Term<Int>,
    pub accumulated: k::Term<List>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeSliceAllocation({types}, {bytes}, {info})"
)]
pub struct DecodeSliceAllocation {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub info: k::Term<TypeInfo>,
}

#[k::function(total, sort = Bool, syntax = "#noFields({fields})")]
pub struct NoFields {
    pub fields: k::Term<Tyss>,
}

#[k::function(partial, sort = Int, syntax = "#findVariantIdx({tag}, {discriminants})")]
pub struct FindVariantIndex {
    pub tag: k::Term<Int>,
    pub discriminants: k::Term<Discriminants>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#findVariantIdxAux({tag}, {discriminants}, {index})"
)]
pub struct FindVariantIndexAux {
    pub tag: k::Term<Int>,
    pub discriminants: k::Term<Discriminants>,
    pub index: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#lookupDiscriminant({discriminants}, {index})"
)]
pub struct LookupDiscriminant {
    pub discriminants: k::Term<Discriminants>,
    pub index: k::Term<Int>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#decodeEnumDirectFields({types}, {bytes}, {index}, {fields}, {layouts})"
)]
pub struct DecodeEnumDirectFields {
    pub types: k::Term<Map>,
    pub bytes: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub fields: k::Term<Tyss>,
    pub layouts: k::Term<LayoutShapes>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#decodeEnumDirectTag({bytes}, {width})"
)]
pub struct DecodeEnumDirectTag {
    pub bytes: k::Term<Bytes>,
    pub width: k::Term<IntegerLength>,
}

#[k::function(partial, sort = Tys, syntax = "#nthTys({fields}, {index})")]
pub struct NthTys {
    pub fields: k::Term<Tyss>,
    pub index: k::Term<Int>,
}

#[k::function(
    partial,
    sort = MachineSizes,
    syntax = "#nthVariantOffsets({layouts}, {index})"
)]
pub struct NthVariantOffsets {
    pub layouts: k::Term<LayoutShapes>,
    pub index: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#byteLength({width})")]
pub struct ByteLength {
    pub width: k::Term<IntegerLength>,
}

#[k::equation]
#[k::requires(int::ge(index, bytes::length(value)))]
fn read_ty_const_int_done(
    k::term![ReadTyConstInt {
        bytes: value,
        index,
        multiplier: _,
        result,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![result]
}

#[k::equation]
#[k::requires(bool::and(int::ge(index, 0), int::lt(index, bytes::length(value))))]
fn read_ty_const_int_byte(
    k::term![ReadTyConstInt {
        bytes: value,
        index,
        multiplier,
        result,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![ReadTyConstInt {
        bytes: value,
        index: int::add(index, 1),
        multiplier: int::mul(multiplier, 256),
        result: int::add(result, int::mul(bytes::get(value, index), multiplier)),
    }]
}

#[k::equation]
fn int_width_isize(
    k::term![IntWidth {
        kind: MirIntTy::Isize(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![64]
}

#[k::equation]
fn int_width_i8(
    k::term![IntWidth {
        kind: MirIntTy::I8(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![8]
}

#[k::equation]
fn int_width_i16(
    k::term![IntWidth {
        kind: MirIntTy::I16(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![16]
}

#[k::equation]
fn int_width_i32(
    k::term![IntWidth {
        kind: MirIntTy::I32(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![32]
}

#[k::equation]
fn int_width_i64(
    k::term![IntWidth {
        kind: MirIntTy::I64(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![64]
}

#[k::equation]
fn int_width_i128(
    k::term![IntWidth {
        kind: MirIntTy::I128(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![128]
}

#[k::equation]
fn uint_width_usize(
    k::term![UintWidth {
        kind: MirUintTy::Usize(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![64]
}

#[k::equation]
fn uint_width_u8(
    k::term![UintWidth {
        kind: MirUintTy::U8(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![8]
}

#[k::equation]
fn uint_width_u16(
    k::term![UintWidth {
        kind: MirUintTy::U16(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![16]
}

#[k::equation]
fn uint_width_u32(
    k::term![UintWidth {
        kind: MirUintTy::U32(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![32]
}

#[k::equation]
fn uint_width_u64(
    k::term![UintWidth {
        kind: MirUintTy::U64(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![64]
}

#[k::equation]
fn uint_width_u128(
    k::term![UintWidth {
        kind: MirUintTy::U128(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![128]
}

#[k::equation]
fn float_width_f16(
    k::term![FloatWidth {
        kind: MirFloatTy::F16(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![16]
}

#[k::equation]
fn float_width_f32(
    k::term![FloatWidth {
        kind: MirFloatTy::F32(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![32]
}

#[k::equation]
fn float_width_f64(
    k::term![FloatWidth {
        kind: MirFloatTy::F64(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![64]
}

#[k::equation]
fn float_width_f128(
    k::term![FloatWidth {
        kind: MirFloatTy::F128(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![128]
}

#[k::equation]
fn layout_size_known(
    k::term![LayoutSize {
        layout: MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape {
                fields: _,
                variants: _,
                abi: _,
                abi_align: _,
                size: MirMachineSize::MachineSize { bits },
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(bits, 8)]
}

#[k::equation]
fn layout_size_unknown(
    k::term![LayoutSize {
        layout: MirMaybeLayoutShape::NoLayoutShape(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn layout_align_known(
    k::term![LayoutAlign {
        layout: MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape {
                fields: _,
                variants: _,
                abi: _,
                abi_align: MirAlign::Align { bytes },
                size: _,
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    bytes
}

#[k::equation]
fn layout_align_unknown(
    k::term![LayoutAlign {
        layout: MirMaybeLayoutShape::NoLayoutShape(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn pointer_words_dynamic_array(
    k::term![PointerWords {
        info: MirTypeInfo::ArrayType {
            element: _,
            size: MirMaybeTyConst::NoTyConst(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![2]
}

#[k::equation(priority = 60)]
fn pointer_words_thin(k::term![PointerWords { info: _ }]: k::Term<Int>) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn is_void_type(
    k::term![IsVoidType {
        info: MirTypeInfo::VoidType(),
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::equation(priority = 60)]
fn is_not_void_type(k::term![IsVoidType { info: _ }]: k::Term<Bool>) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn size_of_boolean(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Bool(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn size_of_char(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Char(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4]
}

#[k::equation]
fn size_of_signed_integer(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::SignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(IntWidth { kind }, 8)]
}

#[k::equation]
fn size_of_unsigned_integer(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(UintWidth { kind }, 8)]
}

#[k::equation]
fn size_of_float(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Float { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(FloatWidth { kind }, 8)]
}

#[k::equation]
fn size_of_str(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Str(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn size_of_enum(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::EnumType {
            name: _,
            adt_def: _,
            discriminants: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutSize { layout }]
}

#[k::equation]
fn size_of_struct(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutSize { layout }]
}

#[k::equation]
fn size_of_union(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::UnionType {
            name: _,
            adt_def: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutSize { layout }]
}

#[k::equation]
fn size_of_tuple(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::TupleType { fields: _, layout },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutSize { layout }]
}

#[k::equation]
fn size_of_dynamic_array(
    k::term![SizeOfTypeInfo {
        types: _,
        info: MirTypeInfo::ArrayType {
            element: _,
            size: MirMaybeTyConst::NoTyConst(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn size_of_static_array(
    k::term![SizeOfTypeInfo {
        types,
        info: MirTypeInfo::ArrayType {
            element,
            size: MirMaybeTyConst::SomeTyConst {
                value: MirTyConst::TyConst {
                    kind: MirTyConstKind::Value {
                        ty: _,
                        allocation: MirAllocation::Allocation {
                            bytes,
                            provenance: _,
                            align: _,
                            mutability: _,
                        },
                    },
                    id: _,
                },
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::mul(
        SizeOfTypeInfo {
            types,
            info: map::get(types, element),
        },
        ReadTyConstInt {
            bytes,
            index: 0,
            multiplier: 1,
            result: 0,
        },
    )]
}

#[k::equation]
fn size_of_pointer(
    k::term![SizeOfTypeInfo {
        types,
        info: MirTypeInfo::PointerType { pointee },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::mul(
        SizeOfTypeInfo {
            types,
            info: MirTypeInfo::PrimitiveType {
                primitive: MirPrimitiveType::UnsignedInteger {
                    kind: MirUintTy::Usize(),
                },
            },
        },
        PointerWords {
            info: map::get(types, pointee),
        },
    )]
}

#[k::equation]
fn size_of_reference(
    k::term![SizeOfTypeInfo {
        types,
        info: MirTypeInfo::ReferenceType { pointee },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::mul(
        SizeOfTypeInfo {
            types,
            info: MirTypeInfo::PrimitiveType {
                primitive: MirPrimitiveType::UnsignedInteger {
                    kind: MirUintTy::Usize(),
                },
            },
        },
        PointerWords {
            info: map::get(types, pointee),
        },
    )]
}

#[k::equation(priority = 60)]
fn size_of_other(k::term![SizeOfTypeInfo { types: _, info: _ }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn align_of_boolean(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Bool(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn align_of_char(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Char(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4]
}

#[k::equation]
fn align_of_signed_integer(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::SignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(IntWidth { kind }, 8)]
}

#[k::equation]
fn align_of_unsigned_integer(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(UintWidth { kind }, 8)]
}

#[k::equation]
fn align_of_float(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Float { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(FloatWidth { kind }, 8)]
}

#[k::equation]
fn align_of_str(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Str(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4]
}

#[k::equation]
fn align_of_enum(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::EnumType {
            name: _,
            adt_def: _,
            discriminants: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutAlign { layout }]
}

#[k::equation]
fn align_of_struct(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutAlign { layout }]
}

#[k::equation]
fn align_of_union(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::UnionType {
            name: _,
            adt_def: _,
            fields: _,
            layout,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutAlign { layout }]
}

#[k::equation]
fn align_of_tuple(
    k::term![AlignOfTypeInfo {
        types: _,
        info: MirTypeInfo::TupleType { fields: _, layout },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LayoutAlign { layout }]
}

#[k::equation]
fn align_of_array(
    k::term![AlignOfTypeInfo {
        types,
        info: MirTypeInfo::ArrayType { element, size: _ },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![AlignOfTypeInfo {
        types,
        info: map::get(types, element),
    }]
}

#[k::equation]
fn align_of_pointer(
    k::term![AlignOfTypeInfo {
        types,
        info: MirTypeInfo::PointerType { pointee: _ },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![AlignOfTypeInfo {
        types,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger {
                kind: MirUintTy::Usize(),
            },
        },
    }]
}

#[k::equation]
fn align_of_reference(
    k::term![AlignOfTypeInfo {
        types,
        info: MirTypeInfo::ReferenceType { pointee: _ },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![AlignOfTypeInfo {
        types,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger {
                kind: MirUintTy::Usize(),
            },
        },
    }]
}

#[k::equation(priority = 60)]
fn align_of_other(k::term![AlignOfTypeInfo { types: _, info: _ }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
#[k::requires(int::eq(bytes::length(bytes), int::div(width, 8)))]
fn decode_integer(
    k::term![DecodeInteger {
        bytes,
        width,
        signed,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Integer {
        value: TruncateInteger {
            value: ReadTyConstInt {
                bytes,
                index: 0,
                multiplier: 1,
                result: 0,
            },
            width,
            signed,
        },
        width,
        signed,
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::eq(bytes::length(bytes), 1),
    int::eq(
        ReadTyConstInt {
            bytes,
            index: 0,
            multiplier: 1,
            result: 0,
        },
        0,
    ),
))]
fn decode_allocated_boolean_false(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Bool(),
        },
        types: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Boolean(false)]
}

#[k::equation]
#[k::requires(bool::and(
    int::eq(bytes::length(bytes), 1),
    int::eq(
        ReadTyConstInt {
            bytes,
            index: 0,
            multiplier: 1,
            result: 0,
        },
        1,
    ),
))]
fn decode_allocated_boolean_true(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Bool(),
        },
        types: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Boolean(true)]
}

#[k::equation]
fn decode_allocated_signed_integer(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::SignedInteger { kind },
        },
        types: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeInteger {
        bytes,
        width: IntWidth { kind },
        signed: true,
    }]
}

#[k::equation]
fn decode_allocated_unsigned_integer(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger { kind },
        },
        types: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeInteger {
        bytes,
        width: UintWidth { kind },
        signed: false,
    }]
}

#[k::equation]
fn no_fields_empty(
    k::term![NoFields {
        fields: MirTyss::TyssEmpty(),
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::equation]
fn no_fields_empty_variant(
    k::term![NoFields {
        fields: MirTyss::TyssCons {
            head: MirTys::TysEmpty(),
            tail,
        },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![NoFields { fields: tail }]
}

#[k::equation]
fn no_fields_nonempty_variant(
    k::term![NoFields {
        fields: MirTyss::TyssCons {
            head: MirTys::TysCons { head: _, tail: _ },
            tail: _,
        },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn find_variant_index(
    k::term![FindVariantIndex { tag, discriminants }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![FindVariantIndexAux {
        tag,
        discriminants,
        index: 0,
    }]
}

#[k::equation]
#[k::requires(int::eq(tag, discriminant))]
fn find_variant_index_match(
    k::term![FindVariantIndexAux {
        tag,
        discriminants: MirDiscriminants::DiscriminantsCons {
            head: MirDiscriminant::Discriminant {
                value: discriminant,
            },
            tail: _,
        },
        index,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![index]
}

#[k::equation]
#[k::requires(int::ne(tag, discriminant))]
fn find_variant_index_continue(
    k::term![FindVariantIndexAux {
        tag,
        discriminants: MirDiscriminants::DiscriminantsCons {
            head: MirDiscriminant::Discriminant {
                value: discriminant,
            },
            tail,
        },
        index,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![FindVariantIndexAux {
        tag,
        discriminants: tail,
        index: int::add(index, 1),
    }]
}

#[k::equation]
#[k::requires(int::eq(index, 0))]
fn lookup_discriminant_head(
    k::term![LookupDiscriminant {
        discriminants: MirDiscriminants::DiscriminantsCons {
            head: MirDiscriminant::Discriminant { value },
            tail: _,
        },
        index,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    value
}

#[k::equation]
#[k::requires(int::gt(index, 0))]
fn lookup_discriminant_tail(
    k::term![LookupDiscriminant {
        discriminants: MirDiscriminants::DiscriminantsCons { head: _, tail },
        index,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![LookupDiscriminant {
        discriminants: tail,
        index: int::sub(index, 1),
    }]
}

#[k::equation]
#[k::requires(bool::eq(NoFields { fields }, false))]
fn decode_allocated_direct_enum(
    k::term![DecodeAllocatedValue {
        types,
        bytes,
        info: MirTypeInfo::EnumType {
            name: _,
            adt_def: _,
            discriminants,
            fields,
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: _,
                    variants: MirVariantsShape::VariantsShapeMultiple {
                        variants: MirVariantsShapeMultiple::MultipleVariants {
                            tag: MirScalar::InitializedScalar {
                                scalar: MirScalarInitialized::ScalarInitializedFields {
                                    value: MirPrimitive::IntegerPrimitive {
                                        integer: MirPrimitiveInt::PrimitiveInt {
                                            length,
                                            signed: _,
                                        },
                                    },
                                    valid_range: _,
                                },
                            },
                            tag_encoding: MirTagEncoding::Direct(),
                            tag_field: 0,
                            variants: layouts,
                        },
                    },
                    abi: _,
                    abi_align: _,
                    size: _,
                },
            },
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeEnumDirectFields {
        types,
        bytes,
        index: FindVariantIndex {
            tag: DecodeEnumDirectTag {
                bytes,
                width: length
            },
            discriminants,
        },
        fields,
        layouts,
    }]
}

#[k::equation]
#[k::requires(int::eq(
    ReadTyConstInt {
        bytes,
        index: 0,
        multiplier: 1,
        result: 0,
    },
    0,
))]
fn decode_allocated_niche_pointer_none(
    k::term![DecodeAllocatedValue {
        types: _,
        bytes,
        info: MirTypeInfo::EnumType {
            name: _,
            adt_def: _,
            discriminants: MirDiscriminants::DiscriminantsCons {
                head: MirDiscriminant::Discriminant { value: 0 },
                tail: MirDiscriminants::DiscriminantsCons {
                    head: MirDiscriminant::Discriminant { value: 1 },
                    tail: MirDiscriminants::DiscriminantsEmpty(),
                },
            },
            fields: MirTyss::TyssCons {
                head: MirTys::TysEmpty(),
                tail: MirTyss::TyssCons {
                    head: MirTys::TysCons {
                        head: _,
                        tail: MirTys::TysEmpty(),
                    },
                    tail: MirTyss::TyssEmpty(),
                },
            },
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: MirFieldsShape::FieldsShapeArbitrary {
                        fields: MirFieldsShapeArbitrary::ArbitraryFields {
                            offsets: MirMachineSizes::MachineSizesCons {
                                head: MirMachineSize::MachineSize { bits: 0 },
                                tail: MirMachineSizes::MachineSizesEmpty(),
                            },
                        },
                    },
                    variants: MirVariantsShape::VariantsShapeMultiple {
                        variants: MirVariantsShapeMultiple::MultipleVariants {
                            tag: MirScalar::InitializedScalar {
                                scalar: MirScalarInitialized::ScalarInitializedFields {
                                    value: MirPrimitive::PointerPrimitive { address_space: _ },
                                    valid_range: MirWrappingRange::WrappingRange {
                                        start: 1,
                                        end: 0,
                                    },
                                },
                            },
                            tag_encoding: MirTagEncoding::Niche(),
                            tag_field: 0,
                            variants: _,
                        },
                    },
                    abi: _,
                    abi_align: _,
                    size: _,
                },
            },
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: list::empty(),
    }]
}

#[k::equation]
#[k::requires(int::ge(index, 0))]
fn decode_enum_direct_fields(
    k::term![DecodeEnumDirectFields {
        types,
        bytes,
        index,
        fields,
        layouts,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: index,
        fields: DecodeFieldsWithOffsets {
            types,
            bytes,
            fields: NthTys { fields, index },
            offsets: NthVariantOffsets { layouts, index },
        },
    }]
}

#[k::equation]
#[k::requires(int::ge(bytes::length(bytes), ByteLength { width }))]
fn decode_enum_direct_tag(
    k::term![DecodeEnumDirectTag { bytes, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![ReadTyConstInt {
        bytes: bytes::substr(bytes, 0, ByteLength { width }),
        index: 0,
        multiplier: 1,
        result: 0,
    }]
}

#[k::equation]
fn nth_tys_first(
    k::term![NthTys {
        fields: MirTyss::TyssCons { head, tail: _ },
        index: 0,
    }]: k::Term<Tys>,
) -> k::Term<Tys> {
    head
}

#[k::equation]
#[k::requires(int::gt(index, 0))]
fn nth_tys_next(
    k::term![NthTys {
        fields: MirTyss::TyssCons { head: _, tail },
        index,
    }]: k::Term<Tys>,
) -> k::Term<Tys> {
    k::term![NthTys {
        fields: tail,
        index: int::sub(index, 1),
    }]
}

#[k::equation]
fn nth_variant_offsets_first(
    k::term![NthVariantOffsets {
        layouts: MirLayoutShapes::LayoutShapesCons {
            head: MirLayoutShape::LayoutShape {
                fields: MirFieldsShape::FieldsShapeArbitrary {
                    fields: MirFieldsShapeArbitrary::ArbitraryFields { offsets },
                },
                variants: _,
                abi: _,
                abi_align: _,
                size: _,
            },
            tail: _,
        },
        index: 0,
    }]: k::Term<MachineSizes>,
) -> k::Term<MachineSizes> {
    offsets
}

#[k::equation]
#[k::requires(int::gt(index, 0))]
fn nth_variant_offsets_next(
    k::term![NthVariantOffsets {
        layouts: MirLayoutShapes::LayoutShapesCons { head: _, tail },
        index,
    }]: k::Term<MachineSizes>,
) -> k::Term<MachineSizes> {
    k::term![NthVariantOffsets {
        layouts: tail,
        index: int::sub(index, 1),
    }]
}

#[k::equation]
fn byte_length_i8(
    k::term![ByteLength {
        width: MirIntegerLength::LengthI8(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn byte_length_i16(
    k::term![ByteLength {
        width: MirIntegerLength::LengthI16(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![2]
}

#[k::equation]
fn byte_length_i32(
    k::term![ByteLength {
        width: MirIntegerLength::LengthI32(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4]
}

#[k::equation]
fn byte_length_i64(
    k::term![ByteLength {
        width: MirIntegerLength::LengthI64(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![8]
}

#[k::equation]
fn byte_length_i128(
    k::term![ByteLength {
        width: MirIntegerLength::LengthI128(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![16]
}

#[k::equation]
fn element_size_boolean(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::Bool(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn element_size_signed_integer(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::SignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(IntWidth { kind }, 8)]
}

#[k::equation]
fn element_size_unsigned_integer(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::PrimitiveType {
            primitive: MirPrimitiveType::UnsignedInteger { kind },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(UintWidth { kind }, 8)]
}

#[k::equation]
fn element_size_struct(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: _,
                    variants: _,
                    abi: _,
                    abi_align: _,
                    size: MirMachineSize::MachineSize { bits },
                },
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(bits, 8)]
}

#[k::equation]
fn element_size_tuple_layout(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::TupleType {
            fields: _,
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: _,
                    variants: _,
                    abi: _,
                    abi_align: _,
                    size: MirMachineSize::MachineSize { bits },
                },
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(bits, 8)]
}

#[k::equation]
fn element_size_empty_tuple(
    k::term![ElementSize {
        types: _,
        info: MirTypeInfo::TupleType {
            fields: MirTys::TysEmpty(),
            layout: MirMaybeLayoutShape::NoLayoutShape(),
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn element_size_static_array(
    k::term![ElementSize {
        types,
        info: MirTypeInfo::ArrayType {
            element,
            size: MirMaybeTyConst::SomeTyConst {
                value: MirTyConst::TyConst {
                    kind: MirTyConstKind::Value {
                        ty: _,
                        allocation: MirAllocation::Allocation {
                            bytes,
                            provenance: _,
                            align: _,
                            mutability: _,
                        },
                    },
                    id: _,
                },
            },
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::mul(
        ElementSize {
            types,
            info: map::get(types, element),
        },
        ReadTyConstInt {
            bytes,
            index: 0,
            multiplier: 1,
            result: 0,
        },
    )]
}

#[k::equation]
#[k::requires(int::ge(first, second))]
fn maximum_first(k::term![Maximum { first, second }]: k::Term<Int>) -> k::Term<Int> {
    k::term![first]
}

#[k::equation]
#[k::requires(int::lt(first, second))]
fn maximum_second(k::term![Maximum { first, second }]: k::Term<Int>) -> k::Term<Int> {
    k::term![second]
}

#[k::equation]
fn needed_bytes_for_offsets_done(
    k::term![NeededBytesForOffsets {
        types: _,
        fields: MirTys::TysEmpty(),
        offsets: MirMachineSizes::MachineSizesEmpty(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn needed_bytes_for_offsets_cons(
    k::term![NeededBytesForOffsets {
        types,
        fields: MirTys::TysCons {
            head: field,
            tail: fields,
        },
        offsets: MirMachineSizes::MachineSizesCons {
            head: MirMachineSize::MachineSize { bits },
            tail: offsets,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![Maximum {
        first: int::add(
            int::div(bits, 8),
            ElementSize {
                types,
                info: map::get(types, field),
            },
        ),
        second: NeededBytesForOffsets {
            types,
            fields,
            offsets,
        },
    }]
}

#[k::equation]
fn decode_fields_with_offsets_done(
    k::term![DecodeFieldsWithOffsets {
        types: _,
        bytes: _,
        fields: MirTys::TysEmpty(),
        offsets: MirMachineSizes::MachineSizesEmpty(),
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::equation]
#[k::requires(int::ge(
    bytes::length(bytes),
    int::add(
        int::div(bits, 8),
        ElementSize {
            types,
            info: map::get(types, field),
        },
    ),
))]
fn decode_fields_with_offsets_cons(
    k::term![DecodeFieldsWithOffsets {
        types,
        bytes,
        fields: MirTys::TysCons {
            head: field,
            tail: fields,
        },
        offsets: MirMachineSizes::MachineSizesCons {
            head: MirMachineSize::MachineSize { bits },
            tail: offsets,
        },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(DecodeAllocatedValue {
            bytes: bytes::substr(
                bytes,
                int::div(bits, 8),
                int::add(
                    int::div(bits, 8),
                    ElementSize {
                        types,
                        info: map::get(types, field),
                    },
                ),
            ),
            info: map::get(types, field),
            types,
        }),
        DecodeFieldsWithOffsets {
            types,
            bytes,
            fields,
            offsets,
        },
    )]
}

#[k::equation]
fn decode_array_allocation(
    k::term![DecodeArrayAllocation {
        types,
        bytes,
        info,
        length,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: DecodeArrayElements {
            types,
            bytes,
            info,
            remaining: length,
            accumulated: list::empty(),
        },
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::gt(remaining, 0),
    bool::and(
        int::gt(ElementSize { types, info }, 0),
        int::ge(bytes::length(bytes), ElementSize { types, info }),
    ),
))]
fn decode_array_elements_cons(
    k::term![DecodeArrayElements {
        types,
        bytes,
        info,
        remaining,
        accumulated,
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![DecodeArrayElements {
        types,
        bytes: bytes::substr(bytes, ElementSize { types, info }, bytes::length(bytes),),
        info,
        remaining: int::sub(remaining, 1),
        accumulated: list::concat(
            accumulated,
            list::item(DecodeAllocatedValue {
                bytes: bytes::substr(bytes, 0, ElementSize { types, info }),
                info,
                types,
            }),
        ),
    }]
}

#[k::equation]
#[k::requires(bool::and(int::le(remaining, 0), int::eq(bytes::length(bytes), 0),))]
fn decode_array_elements_done(
    k::term![DecodeArrayElements {
        types: _,
        bytes,
        info: _,
        remaining,
        accumulated,
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![accumulated]
}

#[k::equation]
#[k::requires(bool::and(
    int::gt(ElementSize { types, info }, 0),
    int::eq(
        int::rem_euclid(bytes::length(bytes), ElementSize { types, info }),
        0,
    ),
))]
fn decode_slice_allocation(
    k::term![DecodeSliceAllocation { types, bytes, info }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeArrayAllocation {
        types,
        bytes,
        info,
        length: int::div(bytes::length(bytes), ElementSize { types, info }),
    }]
}

#[k::equation]
fn decode_allocated_static_array(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::ArrayType {
            element,
            size: MirMaybeTyConst::SomeTyConst {
                value: MirTyConst::TyConst {
                    kind: MirTyConstKind::Value {
                        ty: _,
                        allocation: MirAllocation::Allocation {
                            bytes: length_bytes,
                            provenance: _,
                            align: _,
                            mutability: _,
                        },
                    },
                    id: _,
                },
            },
        },
        types,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeArrayAllocation {
        types,
        bytes,
        info: map::get(types, element),
        length: ReadTyConstInt {
            bytes: length_bytes,
            index: 0,
            multiplier: 1,
            result: 0,
        },
    }]
}

#[k::equation]
fn decode_allocated_slice(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::ArrayType {
            element,
            size: MirMaybeTyConst::NoTyConst(),
        },
        types,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![DecodeSliceAllocation {
        types,
        bytes,
        info: map::get(types, element),
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(
        NeededBytesForOffsets {
            types,
            fields,
            offsets,
        },
        0,
    ),
    int::ge(
        bytes::length(bytes),
        NeededBytesForOffsets {
            types,
            fields,
            offsets,
        },
    ),
))]
fn decode_allocated_struct(
    k::term![DecodeAllocatedValue {
        bytes,
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields,
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: MirFieldsShape::FieldsShapeArbitrary {
                        fields: MirFieldsShapeArbitrary::ArbitraryFields { offsets },
                    },
                    variants: _,
                    abi: _,
                    abi_align: _,
                    size: _,
                },
            },
        },
        types,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: DecodeFieldsWithOffsets {
            types,
            bytes,
            fields,
            offsets,
        },
    }]
}

#[k::equation]
#[k::requires(int::eq(bytes::length(bytes), 0))]
fn decode_allocated_empty_tuple(
    k::term![DecodeAllocatedValue {
        types: _,
        bytes,
        info: MirTypeInfo::TupleType {
            fields: MirTys::TysEmpty(),
            layout: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: list::empty(),
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(
        NeededBytesForOffsets {
            types,
            fields: MirTys::TysCons {
                head: first,
                tail: remaining,
            },
            offsets,
        },
        0,
    ),
    int::ge(
        bytes::length(bytes),
        NeededBytesForOffsets {
            types,
            fields: MirTys::TysCons {
                head: first,
                tail: remaining,
            },
            offsets,
        },
    ),
))]
fn decode_allocated_tuple(
    k::term![DecodeAllocatedValue {
        types,
        bytes,
        info: MirTypeInfo::TupleType {
            fields: MirTys::TysCons {
                head: first,
                tail: remaining,
            },
            layout: MirMaybeLayoutShape::SomeLayoutShape {
                layout: MirLayoutShape::LayoutShape {
                    fields: MirFieldsShape::FieldsShapeArbitrary {
                        fields: MirFieldsShapeArbitrary::ArbitraryFields { offsets },
                    },
                    variants: _,
                    abi: _,
                    abi_align: _,
                    size: _,
                },
            },
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: DecodeFieldsWithOffsets {
            types,
            bytes,
            fields: MirTys::TysCons {
                head: first,
                tail: remaining,
            },
            offsets,
        },
    }]
}

#[k::equation]
#[k::requires(bool::eq(NoFields { fields }, true))]
fn decode_allocated_fieldless_enum(
    k::term![DecodeAllocatedValue {
        types: _,
        bytes,
        info: MirTypeInfo::EnumType {
            name: _,
            adt_def: _,
            discriminants,
            fields,
            layout: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: FindVariantIndex {
            tag: ReadTyConstInt {
                bytes,
                index: 0,
                multiplier: 1,
                result: 0,
            },
            discriminants,
        },
        fields: list::empty(),
    }]
}

#[k::equation]
fn decode_zero_sized_struct(
    k::term![DecodeZeroSizedConstant {
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: list::empty(),
    }]
}

#[k::equation]
fn decode_zero_sized_tuple(
    k::term![DecodeZeroSizedConstant {
        info: MirTypeInfo::TupleType {
            fields: _,
            layout: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: list::empty(),
    }]
}

#[k::equation]
fn decode_zero_sized_array(
    k::term![DecodeZeroSizedConstant {
        info: MirTypeInfo::ArrayType {
            element: _,
            size: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: list::empty(),
    }]
}

#[k::equation]
fn decode_zero_sized_function(
    k::term![DecodeZeroSizedConstant {
        info: MirTypeInfo::FunType { name: _ },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: list::empty(),
    }]
}

#[k::equation]
#[k::requires(int::eq(bytes::length(bytes), 8))]
fn decode_allocated_reference_thin(
    k::term![DecodeAllocatedReference {
        allocation,
        bytes,
        stored: _,
        info: MirTypeInfo::ReferenceType { pointee },
        types,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::AllocationReference {
        allocation,
        projections: Projections::ProjectionsEmpty(),
        metadata: MirMetadata::Metadata {
            size: MetadataSizeOf {
                info: map::get(types, pointee),
            },
            offset: 0,
            origin_size: MetadataSizeOf {
                info: map::get(types, pointee),
            },
        },
    }]
}

#[k::equation]
#[k::requires(int::eq(bytes::length(bytes), 16))]
fn decode_allocated_reference_fat(
    k::term![DecodeAllocatedReference {
        allocation,
        bytes,
        stored: _,
        info: MirTypeInfo::ReferenceType { pointee: _ },
        types: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::AllocationReference {
        allocation,
        projections: Projections::ProjectionsEmpty(),
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::DynamicSize(ReadTyConstInt {
                bytes,
                index: 8,
                multiplier: 1,
                result: 0,
            }),
            offset: 0,
            origin_size: MirMetadataSize::DynamicSize(ReadTyConstInt {
                bytes,
                index: 8,
                multiplier: 1,
                result: 0,
            }),
        },
    }]
}

#[k::equation]
fn metadata_size_of_primitive(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::PrimitiveType { primitive: _ },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::equation]
fn metadata_size_of_pointer(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::PointerType { pointee: _ },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::equation]
fn metadata_size_of_reference(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::ReferenceType { pointee: _ },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::equation]
fn metadata_size_of_struct(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout: _,
        },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::equation]
fn metadata_size_of_void(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::VoidType(),
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::function(total, sort = Bool, syntax = "#zeroSizedType({info})")]
pub struct ZeroSizedType {
    pub info: k::Term<TypeInfo>,
}

#[k::equation(priority = 40)]
fn zero_sized_type_void(
    k::term![ZeroSizedType {
        info: MirTypeInfo::VoidType(),
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::equation]
fn zero_sized_type_primitive(
    k::term![ZeroSizedType {
        info: MirTypeInfo::PrimitiveType { primitive: _ },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn zero_sized_type_array(
    k::term![ZeroSizedType {
        info: MirTypeInfo::ArrayType {
            element: _,
            size: _,
        },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn zero_sized_type_pointer(
    k::term![ZeroSizedType {
        info: MirTypeInfo::PointerType { pointee: _ },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn zero_sized_type_reference(
    k::term![ZeroSizedType {
        info: MirTypeInfo::ReferenceType { pointee: _ },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::equation]
fn zero_sized_type_struct(
    k::term![ZeroSizedType {
        info: MirTypeInfo::StructType {
            name: _,
            adt_def: _,
            fields: _,
            layout: _,
        },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::function(partial, sort = Bool, syntax = "#sameTypeInfo({first}, {second})")]
pub struct SameTypeInfo {
    pub first: k::Term<TypeInfo>,
    pub second: k::Term<TypeInfo>,
}

#[k::equation]
fn same_type_info(
    k::term![SameTypeInfo {
        first: info,
        second: info,
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::function(
    partial,
    sort = Bool,
    syntax = "#zeroFieldOffset({layout})"
)]
pub struct ZeroFieldOffset {
    pub layout: k::Term<MaybeLayoutShape>,
}

#[k::equation]
fn zero_field_offset(
    k::term![ZeroFieldOffset {
        layout: MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape {
                fields: MirFieldsShape::FieldsShapeArbitrary {
                    fields: MirFieldsShapeArbitrary::ArbitraryFields {
                        offsets: MirMachineSizes::MachineSizesCons {
                            head: MirMachineSize::MachineSize { bits: 0 },
                            tail: MirMachineSizes::MachineSizesEmpty(),
                        },
                    },
                },
                variants: _,
                abi: _,
                abi_align: _,
                size: _,
            },
        },
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::equation]
fn metadata_size_of_dynamic_array(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::ArrayType {
            element: _,
            size: MirMaybeTyConst::NoTyConst(),
        },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::DynamicSize(1)]
}

#[k::equation]
fn metadata_size_of_static_array(
    k::term![MetadataSizeOf {
        info: MirTypeInfo::ArrayType {
            element: _,
            size: MirMaybeTyConst::SomeTyConst {
                value: MirTyConst::TyConst {
                    kind: MirTyConstKind::Value {
                        ty: _,
                        allocation: MirAllocation::Allocation {
                            bytes: value,
                            provenance: _,
                            align: _,
                            mutability: _,
                        },
                    },
                    id: _,
                },
            },
        },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::StaticSize(ReadTyConstInt {
        bytes: value,
        index: 0,
        multiplier: 1,
        result: 0,
    })]
}

#[k::function(total, sort = Metadata, syntax = "#convertPointerMetadata({metadata}, {target_size})")]
pub struct ConvertPointerMetadata {
    pub metadata: k::Term<Metadata>,
    pub target_size: k::Term<MetadataSize>,
}

#[k::equation(priority = 40)]
fn convert_pointer_metadata_thin(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size,
            offset,
            origin_size: _,
        },
        target_size: MirMetadataSize::NoMetadataSize(),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::NoMetadataSize(),
        offset,
        origin_size: size,
    }]
}

#[k::equation]
fn convert_pointer_metadata_thin_to_dynamic(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::NoMetadataSize(),
            offset,
            origin_size,
        },
        target_size: MirMetadataSize::DynamicSize(size),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::DynamicSize(size),
        offset,
        origin_size,
    }]
}

#[k::equation]
fn convert_pointer_metadata_thin_to_static(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::NoMetadataSize(),
            offset,
            origin_size,
        },
        target_size: MirMetadataSize::StaticSize(size),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::StaticSize(size),
        offset,
        origin_size,
    }]
}

#[k::equation]
fn convert_pointer_metadata_static_to_dynamic(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::StaticSize(size),
            offset,
            origin_size: _,
        },
        target_size: MirMetadataSize::DynamicSize(_),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::DynamicSize(size),
        offset,
        origin_size: MirMetadataSize::StaticSize(size),
    }]
}

#[k::equation]
fn convert_pointer_metadata_dynamic_to_dynamic(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::DynamicSize(size),
            offset,
            origin_size: _,
        },
        target_size: MirMetadataSize::DynamicSize(_),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::DynamicSize(size),
        offset,
        origin_size: MirMetadataSize::DynamicSize(size),
    }]
}

#[k::equation]
fn convert_pointer_metadata_static_to_static(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::StaticSize(origin),
            offset,
            origin_size: _,
        },
        target_size: MirMetadataSize::StaticSize(size),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::StaticSize(size),
        offset,
        origin_size: MirMetadataSize::StaticSize(origin),
    }]
}

#[k::equation]
fn convert_pointer_metadata_dynamic_to_static(
    k::term![ConvertPointerMetadata {
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::DynamicSize(origin),
            offset,
            origin_size: _,
        },
        target_size: MirMetadataSize::StaticSize(size),
    }]: k::Term<Metadata>,
) -> k::Term<Metadata> {
    k::term![MirMetadata::Metadata {
        size: MirMetadataSize::StaticSize(size),
        offset,
        origin_size: MirMetadataSize::DynamicSize(origin),
    }]
}

#[k::constructors(sort = ProjectionElem, result = KResult)]
#[k::precedence((
    Deref,
    Field,
    Index,
    ConstantIndex,
    Subslice,
    Downcast,
    PointerOffset,
    DerefTruncate,
    SingletonArray,
    WrapStruct,
    ToZst,
    FromZst,
))]
pub enum Projection {
    #[k::syntax("projectionElemDeref")]
    Deref(),
    #[k::syntax("projectionElemField(fieldIdx({field}), {ty})")]
    Field { field: Int, ty: Ty },
    #[k::syntax("projectionElemIndex(local({local}))")]
    Index { local: Int },
    #[k::syntax("projectionElemConstantIndex({offset}, {min_length}, {from_end})")]
    ConstantIndex {
        offset: Int,
        min_length: Int,
        from_end: Bool,
    },
    #[k::syntax("projectionElemSubslice({from}, {to}, {from_end})")]
    Subslice { from: Int, to: Int, from_end: Bool },
    #[k::syntax("projectionElemDowncast(variantIdx({variant}))")]
    Downcast { variant: Int },
    #[k::syntax("PointerOffset({offset}, {origin_size})")]
    PointerOffset { offset: Int, origin_size: Int },
    #[k::syntax("#derefTruncate({size})")]
    DerefTruncate { size: MetadataSize },
    #[k::syntax("projectionElemSingletonArray")]
    SingletonArray(),
    #[k::syntax("projectionElemWrapStruct")]
    WrapStruct(),
    #[k::syntax("projectionElemToZST")]
    ToZst(),
    #[k::syntax("projectionElemFromZST")]
    FromZst(),
}

#[k::constructors(sort = ProjectionElems, result = KResult)]
#[k::precedence((ProjectionsEmpty, ProjectionsCons))]
pub enum Projections {
    #[k::syntax(".ProjectionElems")]
    ProjectionsEmpty(),
    #[k::syntax("{head} {tail}")]
    ProjectionsCons {
        head: ProjectionElem,
        tail: ProjectionElems,
    },
}

#[k::function(
    total,
    sort = ProjectionElems,
    syntax = "removeIndexTail({projections})"
)]
pub struct RemoveIndexTail {
    pub projections: k::Term<ProjectionElems>,
}

#[k::equation]
fn remove_index_tail_empty(
    k::term![RemoveIndexTail {
        projections: Projections::ProjectionsEmpty(),
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsEmpty()]
}

#[k::equation(priority = 40)]
fn remove_index_tail_zero(
    k::term![RemoveIndexTail {
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: 0,
                min_length: _,
                from_end: _,
            },
            tail: Projections::ProjectionsEmpty(),
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsEmpty()]
}

#[k::equation]
fn remove_index_tail_cons(
    k::term![RemoveIndexTail {
        projections: Projections::ProjectionsCons { head, tail },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head,
        tail: RemoveIndexTail { projections: tail },
    }]
}

#[k::function(
    partial,
    sort = MetadataSize,
    syntax = "#projectionMetadataSize({ty}, {projections}, {types})"
)]
pub struct ProjectionMetadataSize {
    pub ty: k::Term<Ty>,
    pub projections: k::Term<ProjectionElems>,
    pub types: k::Term<Map>,
}

#[k::equation]
fn projection_metadata_size_done(
    k::term![ProjectionMetadataSize {
        ty,
        projections: Projections::ProjectionsEmpty(),
        types,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MetadataSizeOf {
        info: map::get(types, ty),
    }]
}

#[k::equation]
fn projection_metadata_size_field(
    k::term![ProjectionMetadataSize {
        ty: _,
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field: _, ty },
            tail,
        },
        types,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![ProjectionMetadataSize {
        ty,
        projections: tail,
        types,
    }]
}

#[k::equation]
fn projection_metadata_size_index(
    k::term![ProjectionMetadataSize {
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Index { local: _ },
            tail,
        },
        types,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![ProjectionMetadataSize {
        ty: ArrayElementType {
            info: map::get(types, ty),
        },
        projections: tail,
        types,
    }]
}

#[k::equation]
fn projection_metadata_size_constant_index(
    k::term![ProjectionMetadataSize {
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: _,
                min_length: _,
                from_end: _,
            },
            tail,
        },
        types,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![ProjectionMetadataSize {
        ty: ArrayElementType {
            info: map::get(types, ty),
        },
        projections: tail,
        types,
    }]
}

#[k::equation]
fn projection_metadata_size_reference_deref(
    k::term![ProjectionMetadataSize {
        ty,
        projections: Projections::ProjectionsCons {
            head: Projection::Deref(),
            tail,
        },
        types,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![ProjectionMetadataSize {
        ty: ReferencePointeeType {
            info: map::get(types, ty),
        },
        projections: tail,
        types,
    }]
}

#[k::function(partial, sort = Ty, syntax = "#arrayElementType({info})")]
pub struct ArrayElementType {
    pub info: k::Term<TypeInfo>,
}

#[k::equation]
fn array_element_type(
    k::term![ArrayElementType {
        info: MirTypeInfo::ArrayType { element, size: _ },
    }]: k::Term<Ty>,
) -> k::Term<Ty> {
    element
}

#[k::function(partial, sort = Ty, syntax = "#referencePointeeType({info})")]
pub struct ReferencePointeeType {
    pub info: k::Term<TypeInfo>,
}

#[k::equation]
fn reference_pointee_type(
    k::term![ReferencePointeeType {
        info: MirTypeInfo::ReferenceType { pointee },
    }]: k::Term<Ty>,
) -> k::Term<Ty> {
    pointee
}

#[k::equation]
fn pointer_pointee_type(
    k::term![ReferencePointeeType {
        info: MirTypeInfo::PointerType { pointee },
    }]: k::Term<Ty>,
) -> k::Term<Ty> {
    pointee
}

#[k::function(total, sort = MetadataSize, syntax = "#maybeDynamicSize({size}, {value})")]
pub struct MaybeDynamicSize {
    pub size: k::Term<MetadataSize>,
    pub value: k::Term<MirValue>,
}

#[k::equation(priority = 40)]
fn maybe_dynamic_size_range(
    k::term![MaybeDynamicSize {
        size: MirMetadataSize::DynamicSize(_),
        value: Value::Range { elements },
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::DynamicSize(list::size(elements))]
}

#[k::equation]
fn maybe_dynamic_size_non_range(
    k::term![MaybeDynamicSize {
        size: MirMetadataSize::DynamicSize(_),
        value: _,
    }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    k::term![MirMetadataSize::NoMetadataSize()]
}

#[k::equation(priority = 60)]
fn maybe_dynamic_size_other(
    k::term![MaybeDynamicSize { size, value: _ }]: k::Term<MetadataSize>,
) -> k::Term<MetadataSize> {
    size
}

#[k::function(
    total,
    sort = ProjectionElems,
    syntax = "#projectionsFor({contexts}, {projections})"
)]
pub struct ProjectionsFor {
    pub contexts: k::Term<ProjectionContexts>,
    pub projections: k::Term<ProjectionElems>,
}

#[k::equation]
fn projections_for_done(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsEmpty(),
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    projections
}

#[k::equation]
fn projections_for_field(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::FieldContext {
                variant: _,
                fields: _,
                field,
                ty,
            },
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field, ty },
            tail: projections,
        },
    }]
}

#[k::equation]
fn projections_for_union_field(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::UnionFieldContext {
                field,
                value: _,
                ty,
            },
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field, ty },
            tail: projections,
        },
    }]
}

#[k::equation]
fn projections_for_index(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::IndexContext { elements: _, index },
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: index,
                min_length: 0,
                from_end: false,
            },
            tail: projections,
        },
    }]
}

#[k::equation]
fn projections_for_subslice(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::SubsliceContext {
                elements: _,
                start,
                from_back,
            },
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from: start,
                to: from_back,
                from_end: false,
            },
            tail: projections,
        },
    }]
}

#[k::equation]
fn projections_for_pointer_offset(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::PointerOffsetContext {
                elements: _,
                offset,
                origin_size,
            },
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::PointerOffset {
                offset,
                origin_size,
            },
            tail: projections,
        },
    }]
}

#[k::equation]
fn projections_for_wrap_struct(
    k::term![ProjectionsFor {
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::WrapStructContext(),
            tail,
        },
        projections,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![ProjectionsFor {
        contexts: tail,
        projections: Projections::ProjectionsCons {
            head: Projection::WrapStruct(),
            tail: projections,
        },
    }]
}

#[k::constructors(sort = ProjectionTarget, result = KResult)]
#[k::precedence((ToLocal, ToStack, ToAllocation))]
pub enum MirProjectionTarget {
    #[k::syntax("toLocal(local({local}))")]
    ToLocal { local: Int },
    #[k::syntax("toStack({height}, local({local}))")]
    ToStack { height: Int, local: Int },
    #[k::syntax("toAlloc({allocation})")]
    ToAllocation { allocation: AllocId },
}

#[k::constructors(sort = ProjectionContext, result = KResult)]
#[k::precedence((
    FieldContext,
    UnionFieldContext,
    IndexContext,
    SubsliceContext,
    PointerOffsetContext,
    WrapStructContext,
))]
pub enum MirProjectionContext {
    #[k::syntax("CtxField(variantIdx({variant}), {fields}, fieldIdx({field}), {ty})")]
    FieldContext {
        variant: Int,
        fields: List,
        field: Int,
        ty: Ty,
    },
    #[k::syntax("CtxFieldUnion(fieldIdx({field}), {value}, {ty})")]
    UnionFieldContext { field: Int, value: MirValue, ty: Ty },
    #[k::syntax("CtxIndex({elements}, {index})")]
    IndexContext { elements: List, index: Int },
    #[k::syntax("CtxSubslice({elements}, {start}, {from_back})")]
    SubsliceContext {
        elements: List,
        start: Int,
        from_back: Int,
    },
    #[k::syntax("CtxPointerOffset({elements}, {offset}, {origin_size})")]
    PointerOffsetContext {
        elements: List,
        offset: Int,
        origin_size: Int,
    },
    #[k::syntax("CtxWrapStruct")]
    WrapStructContext(),
}

#[k::constructors(sort = ProjectionContexts, result = KResult)]
#[k::precedence((ContextsEmpty, ContextsCons))]
pub enum MirProjectionContexts {
    #[k::syntax(".ProjectionContexts")]
    ContextsEmpty(),
    #[k::syntax("{head} {tail}")]
    ContextsCons {
        head: ProjectionContext,
        tail: ProjectionContexts,
    },
}

#[k::constructors(sort = ProjectionAction, result = KResult)]
#[k::precedence((ReadAction, WriteAction, MoveAction, ReferenceAction))]
pub enum MirProjectionAction {
    #[k::syntax("readProjection({continuation})")]
    ReadAction { continuation: Continuation },
    #[k::syntax("writeProjection({value})")]
    WriteAction { value: MirValue },
    #[k::syntax("moveProjection({continuation})")]
    MoveAction { continuation: Continuation },
    #[k::syntax("referenceProjection({place}, {mutability}, {metadata})")]
    ReferenceAction {
        place: Place,
        mutability: Mutability,
        metadata: Metadata,
    },
}

#[k::constructors(sort = PtrCastPhase, result = KResult)]
#[k::precedence((Compare, Source, TargetPhase))]
pub enum MirPtrCastPhase {
    #[k::syntax("ptrCastCompare")]
    Compare(),
    #[k::syntax("ptrCastSource")]
    Source(),
    #[k::syntax("ptrCastTarget")]
    TargetPhase(),
}

#[k::constructors(sort = Place, result = KResult)]
#[k::precedence((Place))]
pub enum MirPlace {
    #[k::syntax("place(local({local}), {projections})")]
    Place {
        local: Int,
        projections: ProjectionElems,
    },
}

#[k::constructors(sort = MirValue, result = KResult)]
#[k::precedence((
    Integer,
    Boolean,
    Aggregate,
    Union,
    Range,
    Reference,
    Pointer,
    AllocationReference,
    Moved,
))]
pub enum Value {
    #[k::syntax("Integer({value}, {width}, {signed})")]
    Integer {
        value: Int,
        width: Int,
        signed: Bool,
    },
    #[k::syntax("BoolVal({value})")]
    Boolean { value: Bool },
    #[k::syntax("Aggregate(variantIdx({variant}), {fields})")]
    Aggregate { variant: Int, fields: List },
    #[k::syntax("Union(fieldIdx({field}), {value})")]
    Union { field: Int, value: MirValue },
    #[k::syntax("Range({elements})")]
    Range { elements: List },
    #[k::syntax("Reference({height}, {place}, {mutability}, {metadata})")]
    Reference {
        height: Int,
        place: Place,
        mutability: Mutability,
        metadata: Metadata,
    },
    #[k::syntax("PtrLocal({height}, {place}, {mutability}, {metadata})")]
    Pointer {
        height: Int,
        place: Place,
        mutability: Mutability,
        metadata: Metadata,
    },
    #[k::syntax("AllocRef({allocation}, {projections}, {metadata})")]
    AllocationReference {
        allocation: AllocId,
        projections: ProjectionElems,
        metadata: Metadata,
    },
    #[k::syntax("Moved")]
    Moved(),
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#mkAggregate({kind}, {values})"
)]
pub struct MaterializeAggregate {
    pub kind: k::Term<AggregateKind>,
    pub values: k::Term<List>,
}

#[k::equation]
fn materialize_adt(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateAdt {
            adt: _,
            variant,
            args: _,
            user_ty: _,
            field: MirMaybeFieldIdx::NoFieldIdx(),
        },
        values,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant,
        fields: values
    }]
}

#[k::equation]
fn materialize_union(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateAdt {
            adt: _,
            variant: _,
            args: _,
            user_ty: _,
            field: MirMaybeFieldIdx::SomeFieldIdx { index: field },
        },
        values: list::concat(list::item(value), list::empty()),
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Union { field, value }]
}

#[k::equation]
fn materialize_fat_raw_pointer(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateRawPointer { ty: _, mutability },
        values: list::concat(
            list::item(Value::Pointer {
                height,
                place: MirPlace::Place { local, projections },
                mutability: _,
                metadata: MirMetadata::Metadata {
                    size: _,
                    offset,
                    origin_size,
                },
            }),
            list::concat(
                list::item(Value::Integer {
                    value: length,
                    width: 64,
                    signed: false,
                }),
                list::empty(),
            ),
        ),
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Pointer {
        height,
        place: MirPlace::Place {
            local,
            projections: RemoveIndexTail { projections },
        },
        mutability,
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::DynamicSize(length),
            offset,
            origin_size,
        },
    }]
}

#[k::equation]
fn materialize_thin_raw_pointer(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateRawPointer { ty: _, mutability },
        values: list::concat(
            list::item(Value::Pointer {
                height,
                place,
                mutability: _,
                metadata: MirMetadata::Metadata {
                    size: _,
                    offset,
                    origin_size,
                },
            }),
            list::concat(
                list::item(Value::Aggregate {
                    variant: _,
                    fields: list::empty(),
                }),
                list::empty(),
            ),
        ),
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Pointer {
        height,
        place,
        mutability,
        metadata: MirMetadata::Metadata {
            size: MirMetadataSize::NoMetadataSize(),
            offset,
            origin_size,
        },
    }]
}

#[k::equation]
fn materialize_array(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateArray { ty: _ },
        values,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range { elements: values }]
}

#[k::equation]
fn materialize_tuple(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateTuple(),
        values,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: values,
    }]
}

#[k::equation]
fn materialize_closure(
    k::term![MaterializeAggregate {
        kind: MirAggregateKind::AggregateClosure {
            closure: _,
            args: _,
        },
        values,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant: 0,
        fields: values,
    }]
}

#[k::constructors(sort = BinaryOp, result = KResult)]
#[k::precedence((
    BinOpAdd,
    BinOpAddUnchecked,
    BinOpSub,
    BinOpSubUnchecked,
    BinOpMul,
    BinOpMulUnchecked,
    BinOpDiv,
    BinOpRem,
    BinOpBitXor,
    BinOpBitAnd,
    BinOpBitOr,
    BinOpShl,
    BinOpShlUnchecked,
    BinOpShr,
    BinOpShrUnchecked,
    BinOpEq,
    BinOpLt,
    BinOpLe,
    BinOpNe,
    BinOpGe,
    BinOpGt,
    BinOpOffset,
))]
pub enum MirBinaryOp {
    #[k::syntax("binOpAdd")]
    BinOpAdd(),
    #[k::syntax("binOpAddUnchecked")]
    BinOpAddUnchecked(),
    #[k::syntax("binOpSub")]
    BinOpSub(),
    #[k::syntax("binOpSubUnchecked")]
    BinOpSubUnchecked(),
    #[k::syntax("binOpMul")]
    BinOpMul(),
    #[k::syntax("binOpMulUnchecked")]
    BinOpMulUnchecked(),
    #[k::syntax("binOpDiv")]
    BinOpDiv(),
    #[k::syntax("binOpRem")]
    BinOpRem(),
    #[k::syntax("binOpBitXor")]
    BinOpBitXor(),
    #[k::syntax("binOpBitAnd")]
    BinOpBitAnd(),
    #[k::syntax("binOpBitOr")]
    BinOpBitOr(),
    #[k::syntax("binOpShl")]
    BinOpShl(),
    #[k::syntax("binOpShlUnchecked")]
    BinOpShlUnchecked(),
    #[k::syntax("binOpShr")]
    BinOpShr(),
    #[k::syntax("binOpShrUnchecked")]
    BinOpShrUnchecked(),
    #[k::syntax("binOpEq")]
    BinOpEq(),
    #[k::syntax("binOpLt")]
    BinOpLt(),
    #[k::syntax("binOpLe")]
    BinOpLe(),
    #[k::syntax("binOpNe")]
    BinOpNe(),
    #[k::syntax("binOpGe")]
    BinOpGe(),
    #[k::syntax("binOpGt")]
    BinOpGt(),
    #[k::syntax("binOpOffset")]
    BinOpOffset(),
}

#[k::constructors(sort = Operand, result = KResult)]
#[k::precedence((Constant, AllocatedConstant, ZeroSizedConstant, Copy, Move))]
pub enum MirOperand {
    #[k::syntax("const({value})")]
    Constant { value: MirValue },
    #[k::syntax(
        "operandConstant(constOperand(span({span}), noUserTypeAnnotationIndex, mirConst(constantKindAllocated({allocation}), {ty}, mirConstId({id}))))"
    )]
    AllocatedConstant {
        span: Int,
        allocation: Allocation,
        ty: Ty,
        id: Int,
    },
    #[k::syntax(
        "operandConstant(constOperand(span({span}), mirConst(constantKindZeroSized, {ty}, mirConstId({id}))))"
    )]
    ZeroSizedConstant { span: Int, ty: Ty, id: Int },
    #[k::syntax("copy({place})")]
    Copy { place: Place },
    #[k::syntax("move({place})")]
    Move { place: Place },
}

#[k::constructors(sort = UnaryOp, result = KResult)]
#[k::precedence((UnOpNot, UnOpNeg, UnOpPtrMetadata))]
pub enum MirUnaryOp {
    #[k::syntax("unOpNot")]
    UnOpNot(),
    #[k::syntax("unOpNeg")]
    UnOpNeg(),
    #[k::syntax("unOpPtrMetadata")]
    UnOpPtrMetadata(),
}

#[k::constructors(sort = NullOp, result = KResult)]
#[k::precedence((SizeOf, AlignOf, UbChecks))]
pub enum MirNullOp {
    #[k::syntax("nullOpSizeOf")]
    SizeOf(),
    #[k::syntax("nullOpAlignOf")]
    AlignOf(),
    #[k::syntax("nullOpUbChecks")]
    UbChecks(),
}

#[k::constructors(sort = Rvalue, result = KResult)]
#[k::precedence((
    Use,
    Cast,
    Ref,
    AddressOf,
    Unary,
    Nullary,
    Binary,
    CheckedBinary,
    AggregateRvalue,
    Repeat,
    Len,
    CopyForDeref,
    DiscriminantRvalue,
))]
pub enum MirRvalue {
    #[k::syntax("rvalueUse({operand})")]
    Use { operand: Operand },
    #[k::syntax("rvalueCast({kind}, {operand}, {target})")]
    Cast {
        kind: CastKind,
        operand: Operand,
        target: Ty,
    },
    #[k::syntax("rvalueRef({region}, {kind}, {place})")]
    Ref {
        region: Region,
        kind: BorrowKind,
        place: Place,
    },
    #[k::syntax("rvalueAddressOf({mutability}, {place})")]
    AddressOf {
        mutability: Mutability,
        place: Place,
    },
    #[k::syntax("rvalueUnaryOp({operation}, {operand})")]
    Unary {
        operation: UnaryOp,
        operand: Operand,
    },
    #[k::syntax("rvalueNullaryOp({operation}, {ty})")]
    Nullary { operation: NullOp, ty: Ty },
    #[k::syntax("rvalueBinaryOp({operation}, {lhs}, {rhs})")]
    Binary {
        operation: BinaryOp,
        lhs: Operand,
        rhs: Operand,
    },
    #[k::syntax("rvalueCheckedBinaryOp({operation}, {lhs}, {rhs})")]
    CheckedBinary {
        operation: BinaryOp,
        lhs: Operand,
        rhs: Operand,
    },
    #[k::syntax("rvalueAggregate({kind}, {operands})")]
    AggregateRvalue {
        kind: AggregateKind,
        operands: Operands,
    },
    #[k::syntax("rvalueRepeat({element}, {count})")]
    Repeat { element: Operand, count: TyConst },
    #[k::syntax("rvalueLen({place})")]
    Len { place: Place },
    #[k::syntax("rvalueCopyForDeref({place})")]
    CopyForDeref { place: Place },
    #[k::syntax("rvalueDiscriminant({place})")]
    DiscriminantRvalue { place: Place },
}

#[k::constructors(sort = Statement, result = KResult)]
#[k::precedence((Assign))]
pub enum MirStatement {
    #[k::syntax("assign({place}, {value})")]
    Assign { place: Place, value: Rvalue },
}

#[k::constructors(sort = Statements, result = KResult)]
#[k::precedence((StatementsEmpty, StatementsCons))]
pub enum StatementList {
    #[k::syntax(".Statements")]
    StatementsEmpty(),
    #[k::syntax("{head} ; {tail}")]
    StatementsCons { head: Statement, tail: Statements },
}

#[k::constructors(sort = Branch, result = KResult)]
#[k::precedence((Branch))]
pub enum MirBranch {
    #[k::syntax("branch({value}, {target})")]
    Branch { value: Int, target: Int },
}

#[k::constructors(sort = Branches, result = KResult)]
#[k::precedence((BranchesEmpty, BranchesCons))]
pub enum BranchList {
    #[k::syntax(".Branches")]
    BranchesEmpty(),
    #[k::syntax("{head} {tail}")]
    BranchesCons { head: Branch, tail: Branches },
}

#[k::constructors(sort = SwitchTargets, result = KResult)]
#[k::precedence((SwitchTargets))]
pub enum MirSwitchTargets {
    #[k::syntax("switchTargets({branches}, {otherwise})")]
    SwitchTargets { branches: Branches, otherwise: Int },
}

#[k::constructors(sort = MaybeBasicBlockIdx, result = KResult)]
#[k::precedence((NoBasicBlockIdx, SomeBasicBlockIdx))]
pub enum MirMaybeBasicBlockIdx {
    #[k::syntax("noBasicBlockIdx")]
    NoBasicBlockIdx(),
    #[k::syntax("someBasicBlockIdx({target})")]
    SomeBasicBlockIdx { target: Int },
}

/// Call and aggregate operands, written one after another with no separator:
/// `copy(place(local(1), .ProjectionElems)) move(place(local(2), .ProjectionElems))`.
/// K's `List{Operand, ""}`: the empty program text is the empty list, which
/// rules print as `.Operands`.
#[k::syntax_list(separator = "")]
pub enum Operands {
    Cons { head: Operand, tail: Operands },
    Nil(),
}

#[k::constructors(sort = LocalDecl, result = KResult)]
#[k::precedence((LocalDecl))]
pub enum MirLocalDecl {
    #[k::syntax("localDecl({ty}, span({span}), {mutability})")]
    LocalDecl {
        ty: Ty,
        span: Int,
        mutability: Mutability,
    },
}

#[k::constructors(sort = LocalDecls, result = KResult)]
#[k::precedence((LocalDeclsEmpty, LocalDeclsCons))]
pub enum MirLocalDecls {
    #[k::syntax(".LocalDecls")]
    LocalDeclsEmpty(),
    #[k::syntax("{head} {tail}")]
    LocalDeclsCons { head: LocalDecl, tail: LocalDecls },
}

#[k::constructors(sort = FunctionBody, result = KResult)]
#[k::precedence((Body))]
pub enum MirFunctionBody {
    #[k::syntax("body({blocks}, {locals}, {arg_count})")]
    Body {
        blocks: List,
        locals: LocalDecls,
        arg_count: Int,
    },
}

#[k::constructors(sort = Function, result = KResult)]
#[k::precedence((MonoItemFn))]
pub enum MirFunction {
    #[k::syntax("monoItemFn(defId({id}), someBody({body}))")]
    MonoItemFn { id: Int, body: FunctionBody },
}

#[k::constructors(sort = CallTarget, result = KResult)]
#[k::precedence((ConstantFunction))]
pub enum MirCallTarget {
    #[k::syntax(
        "operandConstant(constOperand(span({span}), mirConst(constantKindZeroSized, {ty}, mirConstId({id}))))"
    )]
    ConstantFunction { span: Int, ty: Ty, id: Int },
}

#[k::constructors(sort = StackFrame, result = KResult)]
#[k::precedence((StackFrame))]
pub enum MirStackFrame {
    #[k::syntax("StackFrame({caller}, {dest}, {target}, {unwind}, {locals}, span({span}))")]
    StackFrame {
        caller: Ty,
        dest: Place,
        target: MaybeBasicBlockIdx,
        unwind: UnwindAction,
        locals: List,
        span: Int,
    },
}

#[k::constructors(sort = AssertMessage, result = KResult)]
#[k::precedence((Overflow))]
pub enum MirAssertMessage {
    #[k::syntax("assertMessageOverflow({operation}, {lhs}, {rhs})")]
    Overflow {
        operation: BinaryOp,
        lhs: Operand,
        rhs: Operand,
    },
}

#[k::constructors(sort = UnwindAction, result = KResult)]
#[k::precedence((UnwindContinue))]
pub enum MirUnwindAction {
    #[k::syntax("unwindActionContinue")]
    UnwindContinue(),
}

#[k::constructors(sort = MirError, result = k::KItem)]
#[k::precedence((AssertError, ReachedUnreachable))]
pub enum MirExecutionError {
    #[k::syntax("AssertError({message})")]
    AssertError { message: AssertMessage },
    #[k::syntax("ReachedUnreachable")]
    ReachedUnreachable(),
}

#[k::constructors(sort = Terminator, result = KResult)]
#[k::precedence((Goto, SwitchInt, Assert, Call, Drop, Unreachable, Return))]
pub enum MirTerminator {
    #[k::syntax("goto({target})")]
    Goto { target: Int },
    #[k::syntax("switchInt({discr}, {targets})")]
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    #[k::syntax("assert({condition}, {expected}, {message}, {target}, {unwind})")]
    Assert {
        condition: Operand,
        expected: Bool,
        message: AssertMessage,
        target: Int,
        unwind: UnwindAction,
    },
    #[k::syntax(
        "terminatorKindCall({function}, {args}, {destination}, someBasicBlockIdx({target}), {unwind})"
    )]
    Call {
        function: CallTarget,
        args: Operands,
        destination: Place,
        target: Int,
        unwind: UnwindAction,
    },
    #[k::syntax("terminatorKindDrop({place}, {target}, {unwind})")]
    Drop {
        place: Place,
        target: Int,
        unwind: UnwindAction,
    },
    #[k::syntax("terminatorKindUnreachable")]
    Unreachable(),
    #[k::syntax("return")]
    Return(),
}

#[k::constructors(sort = BasicBlock, result = KResult)]
#[k::precedence((Block))]
pub enum BlockSyntax {
    #[k::syntax("basicBlock({statements}, {terminator})")]
    Block {
        statements: Statements,
        terminator: Terminator,
    },
}

#[k::constructors(sort = RetVal, result = KResult)]
#[k::precedence((NoReturn, Returned))]
pub enum ReturnValue {
    #[k::syntax("noReturn")]
    NoReturn(),
    #[k::syntax("return({value})")]
    Returned { value: MirValue },
}

#[k::function(total, sort = Int, syntax = "#truncateUnsigned({value}, {width})")]
pub struct TruncateUnsigned {
    pub value: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#truncateSigned({value}, {width})")]
pub struct TruncateSigned {
    pub value: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#truncateInteger({value}, {width}, {signed})"
)]
pub struct TruncateInteger {
    pub value: k::Term<Int>,
    pub width: k::Term<Int>,
    pub signed: k::Term<Bool>,
}

#[k::requires(int::le(width, 0))]
#[k::equation]
fn truncate_unsigned_nonpositive(
    k::term![TruncateUnsigned { value, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(int::gt(width, 0))]
#[k::equation]
fn truncate_unsigned_positive(
    k::term![TruncateUnsigned { value, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::rem_euclid(value, int::shift_left(1, width))]
}

#[k::requires(int::le(width, 0))]
#[k::equation]
fn truncate_signed_nonpositive(
    k::term![TruncateSigned { value, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(bool::and(
    int::gt(width, 0),
    int::lt(
        TruncateUnsigned { value, width },
        int::shift_left(1, int::sub(width, 1)),
    ),
))]
#[k::equation]
fn truncate_signed_nonnegative(
    k::term![TruncateSigned { value, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![TruncateUnsigned { value, width }]
}

#[k::requires(bool::and(
    int::gt(width, 0),
    int::ge(
        TruncateUnsigned { value, width },
        int::shift_left(1, int::sub(width, 1)),
    ),
))]
#[k::equation]
fn truncate_signed_negative(
    k::term![TruncateSigned { value, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(
        TruncateUnsigned { value, width },
        int::shift_left(1, width),
    )]
}

#[k::equation]
fn truncate_integer_unsigned(
    k::term![TruncateInteger {
        value,
        width,
        signed: false,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![TruncateUnsigned { value, width }]
}

#[k::equation]
fn truncate_integer_signed(
    k::term![TruncateInteger {
        value,
        width,
        signed: true,
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![TruncateSigned { value, width }]
}

#[k::function(partial, sort = MirValue, syntax = "#localValue({entry})")]
pub struct LocalValueOf {
    pub entry: k::Term<TypedLocal>,
}

#[k::equation]
fn local_value_of(
    k::term![LocalValueOf {
        entry: LocalValue::TypedValue {
            value,
            ty: _,
            mutability: _,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![value]
}

#[k::function(partial, sort = TypedLocal, syntax = "#movedEntry({entry})")]
pub struct MovedEntry {
    pub entry: k::Term<TypedLocal>,
}

#[k::equation]
fn moved_entry(
    k::term![MovedEntry {
        entry: LocalValue::TypedValue {
            value: _,
            ty,
            mutability,
        },
    }]: k::Term<TypedLocal>,
) -> k::Term<TypedLocal> {
    k::term![LocalValue::TypedValue {
        value: Value::Moved(),
        ty,
        mutability,
    }]
}

#[k::function(total, sort = List, syntax = "#reserveFor({locals})")]
pub struct ReserveFor {
    pub locals: k::Term<LocalDecls>,
}

#[k::equation]
fn reserve_for_done(
    k::term![ReserveFor {
        locals: MirLocalDecls::LocalDeclsEmpty(),
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::equation]
fn reserve_for_cons(
    k::term![ReserveFor {
        locals: MirLocalDecls::LocalDeclsCons {
            head: MirLocalDecl::LocalDecl {
                ty,
                span: _,
                mutability,
            },
            tail,
        },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(LocalValue::NewLocal { ty, mutability }),
        ReserveFor { locals: tail },
    )]
}

#[k::function(total, sort = List, syntax = "#functionBlocks({function})")]
pub struct FunctionBlocks {
    pub function: k::Term<Function>,
}

#[k::equation]
fn function_blocks(
    k::term![FunctionBlocks {
        function: MirFunction::MonoItemFn {
            id: _,
            body: MirFunctionBody::Body {
                blocks,
                locals: _,
                arg_count: _,
            },
        },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![blocks]
}

#[k::function(total, sort = List, syntax = "#functionLocals({function})")]
pub struct FunctionLocals {
    pub function: k::Term<Function>,
}

#[k::equation]
fn function_locals(
    k::term![FunctionLocals {
        function: MirFunction::MonoItemFn {
            id: _,
            body: MirFunctionBody::Body {
                blocks: _,
                locals,
                arg_count: _,
            },
        },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![ReserveFor { locals }]
}

#[k::function(total, sort = MirValue, syntax = "#adjustRef({value}, {offset})")]
pub struct AdjustRef {
    pub value: k::Term<MirValue>,
    pub offset: k::Term<Int>,
}

#[k::function(partial, sort = List, syntax = "#mapRefOffset({values}, {offset})")]
pub struct MapRefOffset {
    pub values: k::Term<List>,
    pub offset: k::Term<Int>,
}

#[k::equation]
fn map_ref_offset_done(
    k::term![MapRefOffset {
        values: list::empty(),
        offset: _,
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::equation]
fn map_ref_offset_cons(
    k::term![MapRefOffset {
        values: list::concat(list::item(value), tail),
        offset,
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(AdjustRef { value, offset }),
        MapRefOffset {
            values: tail,
            offset,
        },
    )]
}

#[k::equation]
fn adjust_ref_reference(
    k::term![AdjustRef {
        value: Value::Reference {
            height,
            place,
            mutability,
            metadata,
        },
        offset,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Reference {
        height: int::add(height, offset),
        place,
        mutability,
        metadata,
    }]
}

#[k::equation]
fn adjust_ref_pointer(
    k::term![AdjustRef {
        value: Value::Pointer {
            height,
            place,
            mutability,
            metadata,
        },
        offset,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Pointer {
        height: int::add(height, offset),
        place,
        mutability,
        metadata,
    }]
}

#[k::equation]
fn adjust_ref_aggregate(
    k::term![AdjustRef {
        value: Value::Aggregate { variant, fields },
        offset,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant,
        fields: MapRefOffset {
            values: fields,
            offset,
        },
    }]
}

#[k::equation]
fn adjust_ref_union(
    k::term![AdjustRef {
        value: Value::Union { field, value },
        offset: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Union { field, value }]
}

#[k::equation]
fn adjust_ref_range(
    k::term![AdjustRef {
        value: Value::Range { elements },
        offset,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: MapRefOffset {
            values: elements,
            offset,
        },
    }]
}

#[k::equation]
fn adjust_ref_integer(
    k::term![AdjustRef {
        value: Value::Integer {
            value,
            width,
            signed,
        },
        offset: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Integer {
        value,
        width,
        signed,
    }]
}

#[k::equation]
fn adjust_ref_boolean(
    k::term![AdjustRef {
        value: Value::Boolean(value),
        offset: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Boolean(value)]
}

#[k::equation]
fn adjust_ref_moved(
    k::term![AdjustRef {
        value: Value::Moved(),
        offset: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Moved()]
}

#[k::function(partial, sort = List, syntax = "#frameLocals({frame})")]
pub struct FrameLocals {
    pub frame: k::Term<StackFrame>,
}

#[k::equation]
fn frame_locals(
    k::term![FrameLocals {
        frame: MirStackFrame::StackFrame {
            caller: _,
            dest: _,
            target: _,
            unwind: _,
            locals,
            span: _,
        },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![locals]
}

#[k::function(partial, sort = MirValue, syntax = "#localFromFrame({frame}, {local}, {offset})")]
pub struct LocalFromFrame {
    pub frame: k::Term<StackFrame>,
    pub local: k::Term<Int>,
    pub offset: k::Term<Int>,
}

#[k::equation]
fn local_from_frame(
    k::term![LocalFromFrame {
        frame: MirStackFrame::StackFrame {
            caller: _,
            dest: _,
            target: _,
            unwind: _,
            locals,
            span: _,
        },
        local,
        offset,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![AdjustRef {
        value: LocalValueOf {
            entry: list::get(locals, local),
        },
        offset,
    }]
}

#[k::function(
    partial,
    sort = TypedLocal,
    syntax = "#writeProjectedEntry({entry}, {projections}, {value}, {locals})"
)]
pub struct WriteProjectedEntry {
    pub entry: k::Term<TypedLocal>,
    pub projections: k::Term<ProjectionElems>,
    pub value: k::Term<MirValue>,
    pub locals: k::Term<List>,
}

#[k::equation]
fn write_projected_entry(
    k::term![WriteProjectedEntry {
        entry: LocalValue::TypedValue {
            value: original,
            ty,
            mutability,
        },
        projections,
        value,
        locals,
    }]: k::Term<TypedLocal>,
) -> k::Term<TypedLocal> {
    k::term![LocalValue::TypedValue {
        value: WriteProjection {
            value: original,
            projections,
            replacement: value,
            locals,
        },
        ty,
        mutability,
    }]
}

#[k::function(
    partial,
    sort = StackFrame,
    syntax = "#updateProjectedStackLocal({frame}, {local}, {projections}, {value}, {locals})"
)]
pub struct UpdateProjectedStackLocal {
    pub frame: k::Term<StackFrame>,
    pub local: k::Term<Int>,
    pub projections: k::Term<ProjectionElems>,
    pub value: k::Term<MirValue>,
    pub locals: k::Term<List>,
}

#[k::equation]
fn update_projected_stack_local(
    k::term![UpdateProjectedStackLocal {
        frame: MirStackFrame::StackFrame {
            caller,
            dest,
            target,
            unwind,
            locals: frame_locals,
            span,
        },
        local,
        projections,
        value,
        locals,
    }]: k::Term<StackFrame>,
) -> k::Term<StackFrame> {
    k::term![MirStackFrame::StackFrame {
        caller,
        dest,
        target,
        unwind,
        locals: list::update(
            frame_locals,
            local,
            WriteProjectedEntry {
                entry: list::get(frame_locals, local),
                projections,
                value,
                locals,
            },
        ),
        span,
    }]
}

#[k::function(partial, sort = Mutability, syntax = "#borrowMutability({kind})")]
pub struct BorrowMutability {
    pub kind: k::Term<BorrowKind>,
}

#[k::equation]
fn borrow_mutability_shared(
    k::term![BorrowMutability {
        kind: MirBorrowKind::SharedBorrow(),
    }]: k::Term<Mutability>,
) -> k::Term<Mutability> {
    k::term![LocalMutability::NotMutable()]
}

#[k::equation]
fn borrow_mutability_mutable(
    k::term![BorrowMutability {
        kind: MirBorrowKind::MutableBorrow(),
    }]: k::Term<Mutability>,
) -> k::Term<Mutability> {
    k::term![LocalMutability::Mutable()]
}

#[k::function(
    total,
    sort = ProjectionElems,
    syntax = "#appendProjections({first}, {second})"
)]
pub struct AppendProjections {
    pub first: k::Term<ProjectionElems>,
    pub second: k::Term<ProjectionElems>,
}

#[k::equation]
fn append_projections_done(
    k::term![AppendProjections {
        first: Projections::ProjectionsEmpty(),
        second,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![second]
}

#[k::equation]
fn append_projections_cons(
    k::term![AppendProjections {
        first: Projections::ProjectionsCons { head, tail },
        second,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head,
        tail: AppendProjections {
            first: tail,
            second,
        },
    }]
}

#[k::function(
    total,
    sort = ProjectionElems,
    syntax = "#appendCastProjections({first}, {second})"
)]
pub struct AppendCastProjections {
    pub first: k::Term<ProjectionElems>,
    pub second: k::Term<ProjectionElems>,
}

#[k::equation]
fn append_cast_projections_done(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsEmpty(),
        second,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![second]
}

#[k::equation(priority = 40)]
fn append_cast_projections_cancel_singleton(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons {
            head: Projection::SingletonArray(),
            tail: Projections::ProjectionsEmpty(),
        },
        second: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: 0,
                min_length: 0,
                from_end: false,
            },
            tail,
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![tail]
}

#[k::equation(priority = 40)]
fn append_cast_projections_cancel_element(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset: 0,
                min_length: 0,
                from_end: false,
            },
            tail: Projections::ProjectionsEmpty(),
        },
        second: Projections::ProjectionsCons {
            head: Projection::SingletonArray(),
            tail,
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![tail]
}

#[k::equation(priority = 40)]
fn append_cast_projections_cancel_wrapped_field(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons {
            head: Projection::WrapStruct(),
            tail: Projections::ProjectionsEmpty(),
        },
        second: Projections::ProjectionsCons {
            head: Projection::Field { field: 0, ty: _ },
            tail,
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![tail]
}

#[k::equation(priority = 40)]
fn append_cast_projections_cancel_to_zst(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons {
            head: Projection::ToZst(),
            tail: Projections::ProjectionsEmpty(),
        },
        second: Projections::ProjectionsCons {
            head: Projection::FromZst(),
            tail,
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![tail]
}

#[k::equation(priority = 40)]
fn append_cast_projections_cancel_from_zst(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons {
            head: Projection::FromZst(),
            tail: Projections::ProjectionsEmpty(),
        },
        second: Projections::ProjectionsCons {
            head: Projection::ToZst(),
            tail,
        },
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![tail]
}

#[k::equation]
fn append_cast_projections_cons(
    k::term![AppendCastProjections {
        first: Projections::ProjectionsCons { head, tail },
        second,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head,
        tail: AppendCastProjections {
            first: tail,
            second,
        },
    }]
}

#[k::function(total, sort = Int, syntax = "#originSize({size})")]
pub struct OriginSize {
    pub size: k::Term<MetadataSize>,
}

#[k::equation]
fn origin_size_none(
    k::term![OriginSize {
        size: MirMetadataSize::NoMetadataSize(),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn origin_size_static(
    k::term![OriginSize {
        size: MirMetadataSize::StaticSize(size),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![size]
}

#[k::equation]
fn origin_size_dynamic(
    k::term![OriginSize {
        size: MirMetadataSize::DynamicSize(size),
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![size]
}

#[k::function(
    partial,
    sort = ProjectionElems,
    syntax = "#derefProjectionPath({referenced}, {size}, {offset}, {origin_size}, {tail})"
)]
pub struct DerefProjectionPath {
    pub referenced: k::Term<ProjectionElems>,
    pub size: k::Term<MetadataSize>,
    pub offset: k::Term<Int>,
    pub origin_size: k::Term<MetadataSize>,
    pub tail: k::Term<ProjectionElems>,
}

#[k::equation]
#[k::requires(int::eq(offset, 0))]
fn deref_projection_path_zero_offset(
    k::term![DerefProjectionPath {
        referenced,
        size,
        offset,
        origin_size: _,
        tail,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![AppendProjections {
        first: referenced,
        second: Projections::ProjectionsCons {
            head: Projection::DerefTruncate { size },
            tail,
        },
    }]
}

#[k::equation]
#[k::requires(int::gt(offset, 0))]
fn deref_projection_path_positive_offset(
    k::term![DerefProjectionPath {
        referenced,
        size,
        offset,
        origin_size,
        tail,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![AppendProjections {
        first: referenced,
        second: Projections::ProjectionsCons {
            head: Projection::PointerOffset {
                offset,
                origin_size: OriginSize { size: origin_size },
            },
            tail: Projections::ProjectionsCons {
                head: Projection::DerefTruncate { size },
                tail,
            },
        },
    }]
}

#[k::function(
    partial,
    sort = ProjectionElems,
    syntax = "#freezeProjections({projections}, {locals})"
)]
pub struct FreezeProjections {
    pub projections: k::Term<ProjectionElems>,
    pub locals: k::Term<List>,
}

#[k::equation]
fn freeze_projections_done(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsEmpty(),
        locals: _,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsEmpty()]
}

#[k::equation]
fn freeze_projections_field(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field, ty },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::Field { field, ty },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_wrap_struct(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::WrapStruct(),
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::WrapStruct(),
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_index(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::Index { local },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::ConstantIndex {
            offset: ExpectUsize {
                entry: list::get(locals, local),
            },
            min_length: 0,
            from_end: false,
        },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_constant_index(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset,
                min_length,
                from_end,
            },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::ConstantIndex {
            offset,
            min_length,
            from_end,
        },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_subslice(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice { from, to, from_end },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::Subslice { from, to, from_end },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_downcast(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::Downcast { variant },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::Downcast { variant },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::equation]
fn freeze_projections_pointer_offset(
    k::term![FreezeProjections {
        projections: Projections::ProjectionsCons {
            head: Projection::PointerOffset {
                offset,
                origin_size,
            },
            tail,
        },
        locals,
    }]: k::Term<ProjectionElems>,
) -> k::Term<ProjectionElems> {
    k::term![Projections::ProjectionsCons {
        head: Projection::PointerOffset {
            offset,
            origin_size,
        },
        tail: FreezeProjections {
            projections: tail,
            locals,
        },
    }]
}

#[k::function(partial, sort = Place, syntax = "#freezePlace({place}, {locals})")]
pub struct FreezePlace {
    pub place: k::Term<Place>,
    pub locals: k::Term<List>,
}

#[k::equation]
fn freeze_place(
    k::term![FreezePlace {
        place: MirPlace::Place { local, projections },
        locals,
    }]: k::Term<Place>,
) -> k::Term<Place> {
    k::term![MirPlace::Place {
        local,
        projections: FreezeProjections {
            projections,
            locals,
        },
    }]
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#expectUsize({entry})"
)]
pub struct ExpectUsize {
    pub entry: k::Term<TypedLocal>,
}

#[k::equation]
fn expect_usize(
    k::term![ExpectUsize {
        entry: LocalValue::TypedValue {
            value: Value::Integer {
                value,
                width: 64,
                signed: false,
            },
            ty: _,
            mutability: _,
        },
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![value]
}

#[k::function(partial, sort = List, syntax = "#rangeElements({value})")]
pub struct RangeElements {
    pub value: k::Term<MirValue>,
}

#[k::equation]
fn range_elements(
    k::term![RangeElements {
        value: Value::Range { elements },
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![elements]
}

#[k::function(
    partial,
    sort = List,
    syntax = "#replaceSubslice({elements}, {start}, {from_back}, {replacement})"
)]
pub struct ReplaceSubslice {
    pub elements: k::Term<List>,
    pub start: k::Term<Int>,
    pub from_back: k::Term<Int>,
    pub replacement: k::Term<List>,
}

#[k::equation]
#[k::requires(int::eq(
    list::size(replacement),
    int::sub(list::size(elements), int::add(start, from_back)),
))]
fn replace_subslice(
    k::term![ReplaceSubslice {
        elements,
        start,
        from_back,
        replacement,
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::update_all(elements, start, replacement)]
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#readProjection({value}, {projections}, {locals})"
)]
pub struct ReadProjection {
    pub value: k::Term<MirValue>,
    pub projections: k::Term<ProjectionElems>,
    pub locals: k::Term<List>,
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#writeProjection({value}, {projections}, {replacement}, {locals})"
)]
pub struct WriteProjection {
    pub value: k::Term<MirValue>,
    pub projections: k::Term<ProjectionElems>,
    pub replacement: k::Term<MirValue>,
    pub locals: k::Term<List>,
}

#[k::equation]
fn read_projection_done(
    k::term![ReadProjection {
        value,
        projections: Projections::ProjectionsEmpty(),
        locals: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![value]
}

#[k::equation]
fn read_projection_field(
    k::term![ReadProjection {
        value: Value::Aggregate { variant: _, fields },
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field, ty: _ },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: list::get(fields, field),
        projections: tail,
        locals,
    }]
}

#[k::equation]
fn read_projection_downcast(
    k::term![ReadProjection {
        value: Value::Aggregate { variant: _, fields },
        projections: Projections::ProjectionsCons {
            head: Projection::Downcast { variant },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: Value::Aggregate { variant, fields },
        projections: tail,
        locals,
    }]
}

#[k::equation]
fn read_projection_index(
    k::term![ReadProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Index { local },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: list::get(
            elements,
            ExpectUsize {
                entry: list::get(locals, local),
            },
        ),
        projections: tail,
        locals,
    }]
}

#[k::equation]
fn read_projection_deref(
    k::term![ReadProjection {
        value: Value::Reference {
            height: 0,
            place: MirPlace::Place {
                local,
                projections: referenced,
            },
            mutability: _,
            metadata: _,
        },
        projections: Projections::ProjectionsCons {
            head: Projection::Deref(),
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: LocalValueOf {
            entry: list::get(locals, local),
        },
        projections: AppendProjections {
            first: referenced,
            second: tail,
        },
        locals,
    }]
}

#[k::equation]
fn read_projection_pointer_deref(
    k::term![ReadProjection {
        value: Value::Pointer {
            height: 0,
            place: MirPlace::Place {
                local,
                projections: referenced,
            },
            mutability: _,
            metadata: _,
        },
        projections: Projections::ProjectionsCons {
            head: Projection::Deref(),
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: LocalValueOf {
            entry: list::get(locals, local),
        },
        projections: AppendProjections {
            first: referenced,
            second: tail,
        },
        locals,
    }]
}

#[k::equation]
#[k::requires(bool::and(int::ge(offset, 0), int::lt(offset, list::size(elements))))]
fn read_projection_constant_index_front(
    k::term![ReadProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: list::get(elements, offset),
        projections: tail,
        locals,
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::gt(offset, 0),
    bool::and(int::le(offset, min_length), int::eq(min_length, list::size(elements)),),
))]
fn read_projection_constant_index_end(
    k::term![ReadProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset,
                min_length,
                from_end: true,
            },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: list::get(elements, int::sub(min_length, offset)),
        projections: tail,
        locals,
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(from, 0),
    bool::and(
        int::le(from, list::size(elements)),
        bool::and(
            int::gt(to, 0),
            bool::and(int::le(to, list::size(elements)), int::lt(from, to)),
        ),
    ),
))]
fn read_projection_subslice_front(
    k::term![ReadProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from,
                to,
                from_end: false,
            },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: Value::Range {
            elements: list::range(elements, from, int::sub(list::size(elements), to)),
        },
        projections: tail,
        locals,
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(from, 0),
    bool::and(
        int::ge(to, 0),
        bool::and(
            int::lt(to, list::size(elements)),
            int::le(from, int::sub(list::size(elements), to)),
        ),
    ),
))]
fn read_projection_subslice_end(
    k::term![ReadProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from,
                to,
                from_end: true,
            },
            tail,
        },
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![ReadProjection {
        value: Value::Range {
            elements: list::range(elements, from, to),
        },
        projections: tail,
        locals,
    }]
}

#[k::equation]
fn write_projection_done(
    k::term![WriteProjection {
        value: _,
        projections: Projections::ProjectionsEmpty(),
        replacement,
        locals: _,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![replacement]
}

#[k::equation]
fn write_projection_field(
    k::term![WriteProjection {
        value: Value::Aggregate { variant, fields },
        projections: Projections::ProjectionsCons {
            head: Projection::Field { field, ty: _ },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Aggregate {
        variant,
        fields: list::update(
            fields,
            field,
            WriteProjection {
                value: list::get(fields, field),
                projections: tail,
                replacement,
                locals,
            },
        ),
    }]
}

#[k::equation]
fn write_projection_downcast(
    k::term![WriteProjection {
        value: Value::Aggregate { variant: _, fields },
        projections: Projections::ProjectionsCons {
            head: Projection::Downcast { variant },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![WriteProjection {
        value: Value::Aggregate { variant, fields },
        projections: tail,
        replacement,
        locals,
    }]
}

#[k::equation]
fn write_projection_index(
    k::term![WriteProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Index { local },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: list::update(
            elements,
            ExpectUsize {
                entry: list::get(locals, local),
            },
            WriteProjection {
                value: list::get(
                    elements,
                    ExpectUsize {
                        entry: list::get(locals, local),
                    },
                ),
                projections: tail,
                replacement,
                locals,
            },
        ),
    }]
}

#[k::equation]
#[k::requires(bool::and(int::ge(offset, 0), int::lt(offset, list::size(elements))))]
fn write_projection_constant_index_front(
    k::term![WriteProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset,
                min_length: _,
                from_end: false,
            },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: list::update(
            elements,
            offset,
            WriteProjection {
                value: list::get(elements, offset),
                projections: tail,
                replacement,
                locals,
            },
        ),
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::gt(offset, 0),
    bool::and(int::le(offset, min_length), int::eq(min_length, list::size(elements)),),
))]
fn write_projection_constant_index_end(
    k::term![WriteProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::ConstantIndex {
                offset,
                min_length,
                from_end: true,
            },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: list::update(
            elements,
            int::sub(min_length, offset),
            WriteProjection {
                value: list::get(elements, int::sub(min_length, offset)),
                projections: tail,
                replacement,
                locals,
            },
        ),
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(from, 0),
    bool::and(
        int::le(from, list::size(elements)),
        bool::and(
            int::gt(to, 0),
            bool::and(int::le(to, list::size(elements)), int::lt(from, to)),
        ),
    ),
))]
fn write_projection_subslice_front(
    k::term![WriteProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from,
                to,
                from_end: false,
            },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: ReplaceSubslice {
            elements,
            start: from,
            from_back: int::sub(list::size(elements), to),
            replacement: RangeElements {
                value: WriteProjection {
                    value: Value::Range {
                        elements: list::range(elements, from, int::sub(list::size(elements), to),),
                    },
                    projections: tail,
                    replacement,
                    locals,
                },
            },
        },
    }]
}

#[k::equation]
#[k::requires(bool::and(
    int::ge(from, 0),
    bool::and(
        int::ge(to, 0),
        bool::and(
            int::lt(to, list::size(elements)),
            int::le(from, int::sub(list::size(elements), to)),
        ),
    ),
))]
fn write_projection_subslice_end(
    k::term![WriteProjection {
        value: Value::Range { elements },
        projections: Projections::ProjectionsCons {
            head: Projection::Subslice {
                from,
                to,
                from_end: true,
            },
            tail,
        },
        replacement,
        locals,
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![Value::Range {
        elements: ReplaceSubslice {
            elements,
            start: from,
            from_back: to,
            replacement: RangeElements {
                value: WriteProjection {
                    value: Value::Range {
                        elements: list::range(elements, from, to),
                    },
                    projections: tail,
                    replacement,
                    locals,
                },
            },
        },
    }]
}

#[k::function(
    partial,
    sort = MirValue,
    syntax = "#buildProjectionUpdate({value}, {contexts})"
)]
pub struct BuildProjectionUpdate {
    pub value: k::Term<MirValue>,
    pub contexts: k::Term<ProjectionContexts>,
}

#[k::equation]
fn build_projection_update_done(
    k::term![BuildProjectionUpdate {
        value,
        contexts: MirProjectionContexts::ContextsEmpty(),
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![value]
}

#[k::equation]
fn build_projection_update_field(
    k::term![BuildProjectionUpdate {
        value,
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::FieldContext {
                variant,
                fields,
                field,
                ty: _,
            },
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value: Value::Aggregate {
            variant,
            fields: list::update(fields, field, value),
        },
        contexts: tail,
    }]
}

#[k::equation]
fn build_projection_update_union_field(
    k::term![BuildProjectionUpdate {
        value,
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::UnionFieldContext {
                field,
                value: _,
                ty: _,
            },
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value: Value::Union { field, value },
        contexts: tail,
    }]
}

#[k::equation]
fn build_projection_update_wrap_struct(
    k::term![BuildProjectionUpdate {
        value: Value::Aggregate {
            variant: 0,
            fields: list::concat(list::item(value), list::empty()),
        },
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::WrapStructContext(),
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value,
        contexts: tail,
    }]
}

#[k::equation]
fn build_projection_update_index(
    k::term![BuildProjectionUpdate {
        value,
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::IndexContext { elements, index },
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value: Value::Range {
            elements: list::update(elements, index, value),
        },
        contexts: tail,
    }]
}

#[k::equation]
fn build_projection_update_subslice(
    k::term![BuildProjectionUpdate {
        value: Value::Range {
            elements: replacement,
        },
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::SubsliceContext {
                elements,
                start,
                from_back,
            },
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value: Value::Range {
            elements: ReplaceSubslice {
                elements,
                start,
                from_back,
                replacement,
            },
        },
        contexts: tail,
    }]
}

#[k::equation]
fn build_projection_update_pointer_offset(
    k::term![BuildProjectionUpdate {
        value: Value::Range {
            elements: replacement,
        },
        contexts: MirProjectionContexts::ContextsCons {
            head: MirProjectionContext::PointerOffsetContext {
                elements,
                offset,
                origin_size: _,
            },
            tail,
        },
    }]: k::Term<MirValue>,
) -> k::Term<MirValue> {
    k::term![BuildProjectionUpdate {
        value: Value::Range {
            elements: ReplaceSubslice {
                elements,
                start: offset,
                from_back: 0,
                replacement,
            },
        },
        contexts: tail,
    }]
}

#[k::constructors(sort = Continuation, result = KResult)]
#[k::precedence((
    StoreAt,
    FinishCast,
    FinishPtrCast,
    FinishTransmute,
    FinishUnary,
    BinaryRight,
    FinishBinary,
    AggregateNext,
    FinishRepeat,
    FinishLen,
    FinishDiscriminant,
    SelectBlock,
    FinishAssert,
))]
pub enum EvaluationContinuation {
    #[k::syntax("#storeAt({place})")]
    StoreAt { place: Place },
    #[k::syntax("#finishCast({place}, {kind})")]
    FinishCast { place: Place, kind: CastKind },
    #[k::syntax("#finishPtrCast({place}, {source}, {target})")]
    FinishPtrCast {
        place: Place,
        source: TypeInfo,
        target: TypeInfo,
    },
    #[k::syntax("#finishTransmute({place}, {source}, {target})")]
    FinishTransmute {
        place: Place,
        source: TypeInfo,
        target: TypeInfo,
    },
    #[k::syntax("#finishUnary({place}, {operation})")]
    FinishUnary { place: Place, operation: UnaryOp },
    #[k::syntax("#binaryRight({place}, {operation}, {rhs}, {checked})")]
    BinaryRight {
        place: Place,
        operation: BinaryOp,
        rhs: Operand,
        checked: Bool,
    },
    #[k::syntax("#finishBinary({place}, {operation}, {lhs}, {checked})")]
    FinishBinary {
        place: Place,
        operation: BinaryOp,
        lhs: MirValue,
        checked: Bool,
    },
    #[k::syntax("#aggregateNext({place}, {kind}, {values}, {remaining})")]
    AggregateNext {
        place: Place,
        kind: AggregateKind,
        values: List,
        remaining: Operands,
    },
    #[k::syntax("#finishRepeat({place}, {count})")]
    FinishRepeat { place: Place, count: Int },
    #[k::syntax("#finishLen({place})")]
    FinishLen { place: Place },
    #[k::syntax("#finishDiscriminant({place}, {info})")]
    FinishDiscriminant { place: Place, info: TypeInfo },
    #[k::syntax("#selectBlock({targets})")]
    SelectBlock { targets: SwitchTargets },
    #[k::syntax("#finishAssert({expected}, {message})")]
    FinishAssert {
        expected: Bool,
        message: AssertMessage,
    },
}

#[k::constructors(sort = Command, result = KResult)]
#[k::precedence((
    Run,
    ExecBlockIdx,
    ExecBlock,
    ExecStmts,
    ExecStmt,
    EvalRvalue,
    ResolveAddressOf,
    ResolvePtrCast,
    EvalOperand,
    ReadLocal,
    ReadProjectedLocal,
    TraverseProjection,
    ReadMovedProjectedLocal,
    Continue,
    SetLocalValue,
    WriteLocal,
    WriteProjectedLocal,
    ReturnLocal,
    ExecTerminator,
    SetArgsFromStack,
    SetArgFromStack,
    Expect,
    ProgramError,
    EndProgram,
))]
pub enum Execution {
    #[k::syntax("run")]
    Run(),
    #[k::syntax("#execBlockIdx({index})")]
    ExecBlockIdx { index: Int },
    #[k::syntax("#execBlock({block})")]
    ExecBlock { block: BasicBlock },
    #[k::syntax("#execStmts({statements})")]
    ExecStmts { statements: Statements },
    #[k::syntax("#execStmt({statement})")]
    ExecStmt { statement: Statement },
    #[k::syntax("#evalRvalue({value}, {place})")]
    EvalRvalue { value: Rvalue, place: Place },
    #[k::syntax("#addressOf({entry}, {mutability}, {referenced}, {destination})")]
    ResolveAddressOf {
        entry: TypedLocal,
        mutability: Mutability,
        referenced: Place,
        destination: Place,
    },
    #[k::syntax(
        "#resolvePtrCast({phase}, {height}, {pointer_place}, {mutability}, {metadata}, {destination}, {source}, {target}, {projections}, {target_size})"
    )]
    ResolvePtrCast {
        phase: PtrCastPhase,
        height: Int,
        pointer_place: Place,
        mutability: Mutability,
        metadata: Metadata,
        destination: Place,
        source: TypeInfo,
        target: TypeInfo,
        projections: ProjectionElems,
        target_size: MetadataSize,
    },
    #[k::syntax("#evalOperand({operand}, {continuation})")]
    EvalOperand {
        operand: Operand,
        continuation: Continuation,
    },
    #[k::syntax("#readLocal({entry}, {move_after}, {index}, {continuation})")]
    ReadLocal {
        entry: TypedLocal,
        move_after: Bool,
        index: Int,
        continuation: Continuation,
    },
    #[k::syntax("#readProjectedLocal({entry}, {local}, {projections}, {continuation})")]
    ReadProjectedLocal {
        entry: TypedLocal,
        local: Int,
        projections: ProjectionElems,
        continuation: Continuation,
    },
    #[k::syntax(
        "#traverseProjection({target}, {value}, {projections}, {contexts}, {locals}, {action})"
    )]
    TraverseProjection {
        target: ProjectionTarget,
        value: MirValue,
        projections: ProjectionElems,
        contexts: ProjectionContexts,
        locals: List,
        action: ProjectionAction,
    },
    #[k::syntax("#readMovedProjectedLocal({entry}, {local}, {projections}, {continuation})")]
    ReadMovedProjectedLocal {
        entry: TypedLocal,
        local: Int,
        projections: ProjectionElems,
        continuation: Continuation,
    },
    #[k::syntax("#continue({value}, {continuation})")]
    Continue {
        value: MirValue,
        continuation: Continuation,
    },
    #[k::syntax("#setLocalValue({place}, {value})")]
    SetLocalValue { place: Place, value: MirValue },
    #[k::syntax("#writeLocal({entry}, {index}, {value})")]
    WriteLocal {
        entry: TypedLocal,
        index: Int,
        value: MirValue,
    },
    #[k::syntax("#writeProjectedLocal({entry}, {local}, {projections}, {value})")]
    WriteProjectedLocal {
        entry: TypedLocal,
        local: Int,
        projections: ProjectionElems,
        value: MirValue,
    },
    #[k::syntax("#returnLocal({entry})")]
    ReturnLocal { entry: TypedLocal },
    #[k::syntax("#execTerminator({terminator})")]
    ExecTerminator { terminator: Terminator },
    #[k::syntax("#setArgsFromStack({index}, {args})")]
    SetArgsFromStack { index: Int, args: Operands },
    #[k::syntax("#setArgFromStack({index}, {operand})")]
    SetArgFromStack { index: Int, operand: Operand },
    #[k::syntax("#expect({condition}, {expected}, {message})")]
    Expect {
        condition: Operand,
        expected: Bool,
        message: AssertMessage,
    },
    #[k::syntax("#ProgramError({error})")]
    ProgramError { error: MirError },
    #[k::syntax("#EndProgram")]
    EndProgram(),
}

#[k::cell]
pub struct CurrentFrame {
    #[k::cell(name = "currentBody")]
    pub current_body: List<BasicBlock>,
    #[k::cell(name = "caller")]
    pub caller: Ty,
    #[k::cell(name = "dest")]
    pub dest: Place,
    #[k::cell(name = "target")]
    pub target: MaybeBasicBlockIdx,
    #[k::cell(name = "unwind")]
    pub unwind: UnwindAction,
    #[k::cell(name = "locals")]
    pub locals: List<TypedLocal>,
}

/// Operational state selected from KMIR's nested configuration.
#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "retVal")]
    pub ret_val: RetVal,
    #[k::cell(name = "currentFunc")]
    pub current_func: Ty,
    #[k::cell(name = "currentFrame", nested)]
    pub current_frame: CurrentFrame,
    #[k::cell(name = "stack")]
    pub stack: List<StackFrame>,
    #[k::cell(name = "functions")]
    pub functions: Map<Ty, Function>,
    #[k::cell(name = "types")]
    pub types: Map<Ty, TypeInfo>,
    #[k::cell(name = "memory")]
    pub memory: Map<AllocId, MirValue>,
}

#[allow(clippy::too_many_arguments)] // Initializer arguments are source configuration variables.
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] command: KSequence,
        #[k::config_var(name = "PROGRAM")] program: List<BasicBlock>,
        #[k::config_var(name = "LOCALS")] locals: List<TypedLocal>,
        #[k::config_var(name = "RETVAL")] ret_val: RetVal,
        #[k::config_var(name = "CURRENTFUNC")] current_func: Ty,
        #[k::config_var(name = "CALLER")] caller: Ty,
        #[k::config_var(name = "DEST")] dest: Place,
        #[k::config_var(name = "TARGET")] target: MaybeBasicBlockIdx,
        #[k::config_var(name = "UNWIND")] unwind: UnwindAction,
        #[k::config_var(name = "STACK")] stack: List<StackFrame>,
        #[k::config_var(name = "FUNCTIONS")] functions: Map<Ty, Function>,
        #[k::config_var(name = "TYPES")] types: Map<Ty, TypeInfo>,
        #[k::config_var(name = "MEMORY")] memory: Map<AllocId, MirValue>,
    ) -> Self {
        Self {
            k: k::k![command],
            ret_val,
            current_func,
            current_frame: CurrentFrame {
                current_body: program,
                caller,
                dest,
                target,
                unwind,
                locals,
            },
            stack,
            functions,
            types,
            memory,
        }
    }
}

k::rules! {
    for Machine;

    begin: {
        k: [Execution::Run(), ..],
        current_body: program,
    } => {
        k: [Execution::ExecBlockIdx(0), ..],
        current_body: program,
    }
    where program: List;

    lookup_block: {
        k: [Execution::ExecBlockIdx(index), ..],
        current_body: program,
    } => {
        k: [Execution::ExecBlock(list::get(program, index)), ..],
        current_body: program,
    }
    where index: Int, program: List;

    exec_block: {
        k: [Execution::ExecBlock(BlockSyntax::Block { statements, terminator }), ..],
    } => {
        k: [Execution::ExecStmts(statements), Execution::ExecTerminator(terminator), ..],
    }
    where statements: Statements, terminator: Terminator;

    statements_done: {
        k: [Execution::ExecStmts(StatementList::StatementsEmpty()), ..],
    } => {
        k: [..],
    };

    statements_cons: {
        k: [Execution::ExecStmts(StatementList::StatementsCons { head, tail }), ..],
    } => {
        k: [Execution::ExecStmt(head), Execution::ExecStmts(tail), ..],
    }
    where head: Statement, tail: Statements;

    assign: {
        k: [Execution::ExecStmt(MirStatement::Assign { place, value }), ..],
    } => {
        k: [Execution::EvalRvalue { value, place }, ..],
    }
    where place: Place, value: Rvalue;
}

k::rules! {
    for Machine;

    eval_use: {
        k: [Execution::EvalRvalue { value: MirRvalue::Use(operand), place }, ..],
    } => {
        k: [Execution::EvalOperand { operand, continuation: EvaluationContinuation::StoreAt(place) }, ..],
    }
    where operand: Operand, place: Place;

    eval_cast: {
        k: [Execution::EvalRvalue { value: MirRvalue::Cast { kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() }, operand, target: _ }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand, continuation: EvaluationContinuation::FinishCast { place, kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() } } }, ..],
    }
    where operand: Operand, place: Place;

    eval_ptr_cast_copy: {
        k: [Execution::EvalRvalue { value: MirRvalue::Cast { kind: MirCastKind::PtrToPtr(), operand: MirOperand::Copy(MirPlace::Place { local, projections }), target }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(MirPlace::Place { local, projections }), continuation: EvaluationContinuation::FinishPtrCast { place, source: LookupMaybeTy { types, ty: GetTyOf { types, ty: LocalTy { entry: list::get(locals, local) }, projections } }, target: map::get(types, target) } }, ..],
        locals: locals,
        types: types,
    }
    where local: Int, projections: ProjectionElems, target: Ty, place: Place, locals: List, types: Map;

    eval_ptr_cast_move: {
        k: [Execution::EvalRvalue { value: MirRvalue::Cast { kind: MirCastKind::PtrToPtr(), operand: MirOperand::Move(MirPlace::Place { local, projections }), target }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Move(MirPlace::Place { local, projections }), continuation: EvaluationContinuation::FinishPtrCast { place, source: LookupMaybeTy { types, ty: GetTyOf { types, ty: LocalTy { entry: list::get(locals, local) }, projections } }, target: map::get(types, target) } }, ..],
        locals: locals,
        types: types,
    }
    where local: Int, projections: ProjectionElems, target: Ty, place: Place, locals: List, types: Map;

    eval_transmute_copy: {
        k: [Execution::EvalRvalue { value: MirRvalue::Cast { kind: MirCastKind::Transmute(), operand: MirOperand::Copy(MirPlace::Place { local, projections }), target }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(MirPlace::Place { local, projections }), continuation: EvaluationContinuation::FinishTransmute { place, source: LookupMaybeTy { types, ty: GetTyOf { types, ty: LocalTy { entry: list::get(locals, local) }, projections } }, target: map::get(types, target) } }, ..],
        locals: locals,
        types: types,
    }
    where local: Int, projections: ProjectionElems, target: Ty, place: Place, locals: List, types: Map;

    eval_transmute_move: {
        k: [Execution::EvalRvalue { value: MirRvalue::Cast { kind: MirCastKind::Transmute(), operand: MirOperand::Move(MirPlace::Place { local, projections }), target }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Move(MirPlace::Place { local, projections }), continuation: EvaluationContinuation::FinishTransmute { place, source: LookupMaybeTy { types, ty: GetTyOf { types, ty: LocalTy { entry: list::get(locals, local) }, projections } }, target: map::get(types, target) } }, ..],
        locals: locals,
        types: types,
    }
    where local: Int, projections: ProjectionElems, target: Ty, place: Place, locals: List, types: Map;

    eval_ref: {
        k: [Execution::EvalRvalue { value: MirRvalue::Ref { region: _, kind, place: MirPlace::Place { local, projections } }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value: LocalValueOf { entry: list::get(locals, local) }, projections, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::ReferenceAction { place, mutability: BorrowMutability { kind }, metadata: MirMetadata::Metadata { size: ProjectionMetadataSize { ty: LocalTy { entry: list::get(locals, local) }, projections, types }, offset: 0, origin_size: MirMetadataSize::NoMetadataSize() } } }, ..],
        locals: locals,
        types: types,
    }
    where kind: BorrowKind, local: Int, projections: ProjectionElems, place: Place, locals: List, types: Map;

    eval_address_of: {
        k: [Execution::EvalRvalue { value: MirRvalue::AddressOf { mutability, place: MirPlace::Place { local, projections } }, place: destination }, ..],
        locals: locals,
    } => {
        k: [Execution::ResolveAddressOf { entry: list::get(locals, local), mutability, referenced: MirPlace::Place { local, projections }, destination }, ..],
        locals: locals,
    }
    where mutability: Mutability, local: Int, projections: ProjectionElems, destination: Place, locals: List;

    address_of_reference_deref: {
        k: [Execution::ResolveAddressOf { entry: LocalValue::TypedValue { value: Value::Reference { height, place: referenced, mutability: _, metadata }, ty: _, mutability: _ }, mutability, referenced: MirPlace::Place { local: _, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail: Projections::ProjectionsEmpty() } }, destination }, ..],
    } => {
        k: [Execution::SetLocalValue { place: destination, value: Value::Pointer { height, place: referenced, mutability, metadata } }, ..],
    }
    where height: Int, referenced: Place, metadata: Metadata, mutability: Mutability, destination: Place;

    #[k::rule(owise)]
    address_of_local: {
        k: [Execution::ResolveAddressOf { entry: LocalValue::TypedValue { value: _, ty: _, mutability: _ }, mutability, referenced, destination }, ..],
        locals: locals,
    } => {
        k: [Execution::SetLocalValue { place: destination, value: Value::Pointer { height: 0, place: FreezePlace { place: referenced, locals }, mutability, metadata: MirMetadata::Metadata { size: MirMetadataSize::NoMetadataSize(), offset: 0, origin_size: MirMetadataSize::NoMetadataSize() } } }, ..],
        locals: locals,
    }
    where mutability: Mutability, referenced: Place, destination: Place, locals: List;

    eval_unary: {
        k: [Execution::EvalRvalue { value: MirRvalue::Unary { operation, operand }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand, continuation: EvaluationContinuation::FinishUnary { place, operation } }, ..],
    }
    where operation: UnaryOp, operand: Operand, place: Place;

    eval_ub_checks: {
        k: [Execution::EvalRvalue { value: MirRvalue::Nullary { operation: MirNullOp::UbChecks(), ty: _ }, place }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    }
    where place: Place;

    #[k::requires(bool::not(IsVoidType { info: map::get(types, ty) }))]
    eval_size_of: {
        k: [Execution::EvalRvalue { value: MirRvalue::Nullary { operation: MirNullOp::SizeOf(), ty }, place }, ..],
        types: types,
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: SizeOfTypeInfo { types, info: map::get(types, ty) }, width: 64, signed: false } }, ..],
        types: types,
    }
    where ty: Ty, place: Place, types: Map;

    #[k::requires(bool::not(IsVoidType { info: map::get(types, ty) }))]
    eval_align_of: {
        k: [Execution::EvalRvalue { value: MirRvalue::Nullary { operation: MirNullOp::AlignOf(), ty }, place }, ..],
        types: types,
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: AlignOfTypeInfo { types, info: map::get(types, ty) }, width: 64, signed: false } }, ..],
        types: types,
    }
    where ty: Ty, place: Place, types: Map;

    eval_binary: {
        k: [Execution::EvalRvalue { value: MirRvalue::Binary { operation, lhs, rhs }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: lhs, continuation: EvaluationContinuation::BinaryRight { place, operation, rhs, checked: false } }, ..],
    }
    where operation: BinaryOp, lhs: Operand, rhs: Operand, place: Place;

    eval_checked_binary: {
        k: [Execution::EvalRvalue { value: MirRvalue::CheckedBinary { operation, lhs, rhs }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: lhs, continuation: EvaluationContinuation::BinaryRight { place, operation, rhs, checked: true } }, ..],
    }
    where operation: BinaryOp, lhs: Operand, rhs: Operand, place: Place;

    eval_aggregate_empty: {
        k: [Execution::EvalRvalue { value: MirRvalue::AggregateRvalue { kind, operands: Operands::Nil() }, place }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: MaterializeAggregate { kind, values: list::empty() } }, ..],
    }
    where kind: AggregateKind, place: Place;

    eval_aggregate_cons: {
        k: [Execution::EvalRvalue { value: MirRvalue::AggregateRvalue { kind, operands: Operands::Cons { head, tail } }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: head, continuation: EvaluationContinuation::AggregateNext { place, kind, values: list::empty(), remaining: tail } }, ..],
    }
    where kind: AggregateKind, head: Operand, tail: Operands, place: Place;

    eval_repeat: {
        k: [Execution::EvalRvalue { value: MirRvalue::Repeat { element, count: MirTyConst::TyConst { kind: MirTyConstKind::Value { ty: _, allocation: MirAllocation::Allocation { bytes, provenance: _, align: _, mutability: _ } }, id: _ } }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: element, continuation: EvaluationContinuation::FinishRepeat { place, count: ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 } } }, ..],
    }
    where element: Operand, place: Place, bytes: Bytes;

    eval_len: {
        k: [Execution::EvalRvalue { value: MirRvalue::Len { place: source }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(source), continuation: EvaluationContinuation::FinishLen { place } }, ..],
    }
    where source: Place, place: Place;

    eval_copy_for_deref: {
        k: [Execution::EvalRvalue { value: MirRvalue::CopyForDeref { place: source }, place }, ..],
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(source), continuation: EvaluationContinuation::StoreAt(place) }, ..],
    }
    where source: Place, place: Place;

    eval_discriminant: {
        k: [Execution::EvalRvalue { value: MirRvalue::DiscriminantRvalue { place: MirPlace::Place { local, projections } }, place }, ..],
        locals: locals,
        types: types,
    } => {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(MirPlace::Place { local, projections }), continuation: EvaluationContinuation::FinishDiscriminant { place, info: LookupMaybeTy { types, ty: GetTyOf { types, ty: LocalTy { entry: list::get(locals, local) }, projections } } } }, ..],
        locals: locals,
        types: types,
    }
    where local: Int, projections: ProjectionElems, place: Place, locals: List, types: Map;

    eval_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::Constant(value), continuation }, ..],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    }
    where value: MirValue, continuation: Continuation;

    eval_allocated_reference_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::AllocatedConstant { span: _, allocation: MirAllocation::Allocation { bytes, provenance: MirProvenanceMap::SingletonProvenanceMap { offset: 0, allocation }, align: _, mutability: _ }, ty, id: _ }, continuation }, ..],
        types: types,
        memory: memory,
    } => {
        k: [Execution::Continue { value: DecodeAllocatedReference { allocation, bytes, stored: map::get(memory, allocation), info: map::get(types, ty), types }, continuation }, ..],
        types: types,
        memory: memory,
    }
    where allocation: AllocId, bytes: Bytes, ty: Ty, continuation: Continuation, types: Map, memory: Map;

    eval_allocated_value_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::AllocatedConstant { span: _, allocation: MirAllocation::Allocation { bytes, provenance: MirProvenanceMap::EmptyProvenanceMap(), align: _, mutability: _ }, ty, id: _ }, continuation }, ..],
        types: types,
    } => {
        k: [Execution::Continue { value: DecodeAllocatedValue { bytes, info: map::get(types, ty), types }, continuation }, ..],
        types: types,
    }
    where bytes: Bytes, ty: Ty, continuation: Continuation, types: Map;

    eval_zero_sized_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::ZeroSizedConstant { span: _, ty, id: _ }, continuation }, ..],
        types: types,
    } => {
        k: [Execution::Continue { value: DecodeZeroSizedConstant { info: map::get(types, ty) }, continuation }, ..],
        types: types,
    }
    where ty: Ty, continuation: Continuation, types: Map;

    eval_copy: {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }), continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::ReadLocal { entry: list::get(locals, local), move_after: false, index: local, continuation }, ..],
        locals: locals,
    }
    where local: Int, continuation: Continuation, locals: List;

    eval_copy_field: {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(MirPlace::Place { local, projections: Projections::ProjectionsCons { head, tail } }), continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::ReadProjectedLocal { entry: list::get(locals, local), local, projections: Projections::ProjectionsCons { head, tail }, continuation }, ..],
        locals: locals,
    }
    where local: Int, head: ProjectionElem, tail: ProjectionElems, continuation: Continuation, locals: List;

    eval_move: {
        k: [Execution::EvalOperand { operand: MirOperand::Move(MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }), continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::ReadLocal { entry: list::get(locals, local), move_after: true, index: local, continuation }, ..],
        locals: locals,
    }
    where local: Int, continuation: Continuation, locals: List;

    eval_move_projected: {
        k: [Execution::EvalOperand { operand: MirOperand::Move(MirPlace::Place { local, projections: Projections::ProjectionsCons { head, tail } }), continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::ReadMovedProjectedLocal { entry: list::get(locals, local), local, projections: Projections::ProjectionsCons { head, tail }, continuation }, ..],
        locals: locals,
    }
    where local: Int, head: ProjectionElem, tail: ProjectionElems, continuation: Continuation, locals: List;

    read_local_copy: {
        k: [Execution::ReadLocal { entry: LocalValue::TypedValue { value, ty: _, mutability: _ }, move_after: false, index: _, continuation }, ..],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    }
    where value: MirValue, continuation: Continuation;

    read_local_move: {
        k: [Execution::ReadLocal { entry: LocalValue::TypedValue { value, ty, mutability }, move_after: true, index, continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::Continue { value, continuation }, ..],
        locals: list::update(locals, index, LocalValue::TypedValue { value: Value::Moved(), ty, mutability }),
    }
    where value: MirValue, ty: Ty, mutability: Mutability, index: Int, continuation: Continuation, locals: List;

    read_projected_local: {
        k: [Execution::ReadProjectedLocal { entry: LocalValue::TypedValue { value, ty: _, mutability: _ }, local, projections, continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value, projections, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::ReadAction(continuation) }, ..],
        locals: locals,
    }
    where value: MirValue, local: Int, projections: ProjectionElems, continuation: Continuation, locals: List;

    read_moved_projected_local: {
        k: [Execution::ReadMovedProjectedLocal { entry: LocalValue::TypedValue { value, ty: _, mutability: _ }, local, projections, continuation }, ..],
        locals: locals,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value, projections, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::MoveAction(continuation) }, ..],
        locals: locals,
    }
    where value: MirValue, local: Int, projections: ProjectionElems, continuation: Continuation, locals: List;

    traverse_projection_read_done: {
        k: [Execution::TraverseProjection { target: _, value, projections: Projections::ProjectionsEmpty(), contexts: _, locals: _, action: MirProjectionAction::ReadAction(continuation) }, ..],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    }
    where value: MirValue, continuation: Continuation;

    traverse_projection_reference_local_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value, projections: Projections::ProjectionsEmpty(), contexts, locals: _, action: MirProjectionAction::ReferenceAction { place, mutability, metadata: MirMetadata::Metadata { size, offset, origin_size } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Reference { height: 0, place: MirPlace::Place { local, projections: ProjectionsFor { contexts, projections: Projections::ProjectionsEmpty() } }, mutability, metadata: MirMetadata::Metadata { size: MaybeDynamicSize { size, value }, offset, origin_size } } }, ..],
    }
    where local: Int, value: MirValue, contexts: ProjectionContexts, place: Place, mutability: Mutability, size: MetadataSize, offset: Int, origin_size: MetadataSize;

    traverse_projection_reference_stack_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToStack { height, local }, value, projections: Projections::ProjectionsEmpty(), contexts, locals: _, action: MirProjectionAction::ReferenceAction { place, mutability, metadata: MirMetadata::Metadata { size, offset, origin_size } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Reference { height, place: MirPlace::Place { local, projections: ProjectionsFor { contexts, projections: Projections::ProjectionsEmpty() } }, mutability, metadata: MirMetadata::Metadata { size: MaybeDynamicSize { size, value }, offset, origin_size } } }, ..],
    }
    where height: Int, local: Int, value: MirValue, contexts: ProjectionContexts, place: Place, mutability: Mutability, size: MetadataSize, offset: Int, origin_size: MetadataSize;

    traverse_projection_reference_allocation_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToAllocation(allocation), value, projections: Projections::ProjectionsEmpty(), contexts, locals: _, action: MirProjectionAction::ReferenceAction { place, mutability: _, metadata: MirMetadata::Metadata { size, offset, origin_size } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::AllocationReference { allocation, projections: ProjectionsFor { contexts, projections: Projections::ProjectionsEmpty() }, metadata: MirMetadata::Metadata { size: MaybeDynamicSize { size, value }, offset, origin_size } } }, ..],
    }
    where allocation: AllocId, value: MirValue, contexts: ProjectionContexts, place: Place, size: MetadataSize, offset: Int, origin_size: MetadataSize;

    traverse_projection_write_local_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value: _, projections: Projections::ProjectionsEmpty(), contexts, locals: _, action: MirProjectionAction::WriteAction(replacement) }, ..],
    } => {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }, value: BuildProjectionUpdate { value: replacement, contexts } }, ..],
    }
    where local: Int, contexts: ProjectionContexts, replacement: MirValue;

    traverse_projection_write_stack_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToStack { height, local }, value: _, projections: Projections::ProjectionsEmpty(), contexts, locals, action: MirProjectionAction::WriteAction(replacement) }, ..],
        stack: stack,
    } => {
        k: [..],
        stack: list::update(stack, int::sub(height, 1), UpdateProjectedStackLocal { frame: list::get(stack, int::sub(height, 1)), local, projections: Projections::ProjectionsEmpty(), value: AdjustRef { value: BuildProjectionUpdate { value: replacement, contexts }, offset: int::sub(0, height) }, locals }),
    }
    where height: Int, local: Int, contexts: ProjectionContexts, locals: List, replacement: MirValue, stack: List;

    traverse_projection_move_local_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value, projections: Projections::ProjectionsEmpty(), contexts, locals: _, action: MirProjectionAction::MoveAction(continuation) }, ..],
    } => {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }, value: BuildProjectionUpdate { value: Value::Moved(), contexts } }, Execution::Continue { value, continuation }, ..],
    }
    where value: MirValue, local: Int, contexts: ProjectionContexts, continuation: Continuation;

    traverse_projection_move_stack_done: {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToStack { height, local }, value, projections: Projections::ProjectionsEmpty(), contexts, locals, action: MirProjectionAction::MoveAction(continuation) }, ..],
        stack: stack,
    } => {
        k: [Execution::Continue { value, continuation }, ..],
        stack: list::update(stack, int::sub(height, 1), UpdateProjectedStackLocal { frame: list::get(stack, int::sub(height, 1)), local, projections: Projections::ProjectionsEmpty(), value: AdjustRef { value: BuildProjectionUpdate { value: Value::Moved(), contexts }, offset: int::sub(0, height) }, locals }),
    }
    where height: Int, local: Int, value: MirValue, contexts: ProjectionContexts, locals: List, continuation: Continuation, stack: List;

    traverse_projection_field: {
        k: [Execution::TraverseProjection { target, value: Value::Aggregate { variant, fields }, projections: Projections::ProjectionsCons { head: Projection::Field { field, ty }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: list::get(fields, field), projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::FieldContext { variant, fields, field, ty }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, variant: Int, fields: List, field: Int, ty: Ty, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    traverse_projection_union_field: {
        k: [Execution::TraverseProjection { target, value: Value::Union { field, value }, projections: Projections::ProjectionsCons { head: Projection::Field { field, ty }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value, projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::UnionFieldContext { field, value, ty }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, field: Int, value: MirValue, ty: Ty, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    traverse_projection_wrap_struct: {
        k: [Execution::TraverseProjection { target, value, projections: Projections::ProjectionsCons { head: Projection::WrapStruct(), tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Aggregate { variant: 0, fields: list::concat(list::item(value), list::empty()) }, projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::WrapStructContext(), tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, value: MirValue, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    traverse_projection_downcast: {
        k: [Execution::TraverseProjection { target, value: Value::Aggregate { variant: _, fields }, projections: Projections::ProjectionsCons { head: Projection::Downcast { variant }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Aggregate { variant, fields }, projections: tail, contexts, locals, action }, ..],
    }
    where target: ProjectionTarget, variant: Int, fields: List, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    traverse_projection_index: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::Index { local }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: list::get(elements, ExpectUsize { entry: list::get(locals, local) }), projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::IndexContext { elements, index: ExpectUsize { entry: list::get(locals, local) } }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, local: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(offset, 0), int::lt(offset, list::size(elements))))]
    traverse_projection_constant_index_front: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::ConstantIndex { offset, min_length: _, from_end: false }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: list::get(elements, offset), projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::IndexContext { elements, index: offset }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, offset: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::gt(offset, 0), bool::and(int::le(offset, min_length), int::eq(min_length, list::size(elements)))))]
    traverse_projection_constant_index_end: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::ConstantIndex { offset, min_length, from_end: true }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: list::get(elements, int::sub(min_length, offset)), projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::IndexContext { elements, index: int::sub(min_length, offset) }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, offset: Int, min_length: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(from, 0), bool::and(int::le(from, list::size(elements)), bool::and(int::gt(to, 0), bool::and(int::le(to, list::size(elements)), int::lt(from, to))))))]
    traverse_projection_subslice_front: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::Subslice { from, to, from_end: false }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Range { elements: list::range(elements, from, int::sub(list::size(elements), to)) }, projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::SubsliceContext { elements, start: from, from_back: int::sub(list::size(elements), to) }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, from: Int, to: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(from, 0), bool::and(int::ge(to, 0), bool::and(int::lt(to, list::size(elements)), int::le(from, int::sub(list::size(elements), to))))))]
    traverse_projection_subslice_end: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::Subslice { from, to, from_end: true }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Range { elements: list::range(elements, from, to) }, projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::SubsliceContext { elements, start: from, from_back: to }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, from: Int, to: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(offset, 0), int::le(offset, list::size(elements))))]
    traverse_projection_pointer_offset: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::PointerOffset { offset, origin_size }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Range { elements: list::range(elements, offset, 0) }, projections: tail, contexts: MirProjectionContexts::ContextsCons { head: MirProjectionContext::PointerOffsetContext { elements, offset, origin_size }, tail: contexts }, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, offset: Int, origin_size: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(size, 0), int::le(size, list::size(elements))))]
    traverse_projection_truncate_static: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::DerefTruncate { size: MirMetadataSize::StaticSize(size) }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Range { elements: list::range(elements, 0, int::sub(list::size(elements), size)) }, projections: tail, contexts, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, size: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::requires(bool::and(int::ge(size, 0), int::le(size, list::size(elements))))]
    traverse_projection_truncate_dynamic: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::DerefTruncate { size: MirMetadataSize::DynamicSize(size) }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: Value::Range { elements: list::range(elements, 0, int::sub(list::size(elements), size)) }, projections: tail, contexts, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, size: Int, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    traverse_projection_truncate_array_head: {
        k: [Execution::TraverseProjection { target, value: Value::Range(elements), projections: Projections::ProjectionsCons { head: Projection::DerefTruncate { size: MirMetadataSize::NoMetadataSize() }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value: list::get(elements, 0), projections: tail, contexts, locals, action }, ..],
    }
    where target: ProjectionTarget, elements: List, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::rule(owise)]
    traverse_projection_truncate_non_range: {
        k: [Execution::TraverseProjection { target, value, projections: Projections::ProjectionsCons { head: Projection::DerefTruncate { size: MirMetadataSize::NoMetadataSize() }, tail }, contexts, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target, value, projections: tail, contexts, locals, action }, ..],
    }
    where target: ProjectionTarget, value: MirValue, tail: ProjectionElems, contexts: ProjectionContexts, locals: List, action: ProjectionAction;

    #[k::rule(owise)]
    traverse_projection_current_reference: {
        k: [Execution::TraverseProjection { target: _, value: Value::Reference { height: 0, place: MirPlace::Place { local, projections: referenced }, mutability: _, metadata: MirMetadata::Metadata { size, offset, origin_size } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value: LocalValueOf { entry: list::get(locals, local) }, projections: DerefProjectionPath { referenced, size, offset, origin_size, tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action }, ..],
    }
    where local: Int, referenced: ProjectionElems, size: MetadataSize, offset: Int, origin_size: MetadataSize, tail: ProjectionElems, locals: List, action: ProjectionAction;

    #[k::requires(int::gt(height, 0))]
    traverse_projection_stack_reference: {
        k: [Execution::TraverseProjection { target: _, value: Value::Reference { height, place: MirPlace::Place { local, projections: referenced }, mutability: _, metadata: MirMetadata::Metadata { size, offset, origin_size } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action }, ..],
        stack: stack,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToStack { height, local }, value: LocalFromFrame { frame: list::get(stack, int::sub(height, 1)), local, offset: height }, projections: DerefProjectionPath { referenced, size, offset, origin_size, tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action }, ..],
        stack: stack,
    }
    where height: Int, local: Int, referenced: ProjectionElems, size: MetadataSize, offset: Int, origin_size: MetadataSize, tail: ProjectionElems, locals: List, action: ProjectionAction, stack: List;

    #[k::rule(owise)]
    traverse_projection_current_pointer: {
        k: [Execution::TraverseProjection { target: _, value: Value::Pointer { height: 0, place: MirPlace::Place { local, projections: referenced }, mutability: _, metadata: MirMetadata::Metadata { size, offset, origin_size } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action }, ..],
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value: LocalValueOf { entry: list::get(locals, local) }, projections: DerefProjectionPath { referenced, size, offset, origin_size, tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action }, ..],
    }
    where local: Int, referenced: ProjectionElems, size: MetadataSize, offset: Int, origin_size: MetadataSize, tail: ProjectionElems, locals: List, action: ProjectionAction;

    #[k::requires(int::gt(height, 0))]
    traverse_projection_stack_pointer: {
        k: [Execution::TraverseProjection { target: _, value: Value::Pointer { height, place: MirPlace::Place { local, projections: referenced }, mutability: _, metadata: MirMetadata::Metadata { size, offset, origin_size } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action }, ..],
        stack: stack,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToStack { height, local }, value: LocalFromFrame { frame: list::get(stack, int::sub(height, 1)), local, offset: height }, projections: DerefProjectionPath { referenced, size, offset, origin_size, tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action }, ..],
        stack: stack,
    }
    where height: Int, local: Int, referenced: ProjectionElems, size: MetadataSize, offset: Int, origin_size: MetadataSize, tail: ProjectionElems, locals: List, action: ProjectionAction, stack: List;

    traverse_projection_allocation_reference_read: {
        k: [Execution::TraverseProjection { target: _, value: Value::AllocationReference { allocation, projections: referenced, metadata: MirMetadata::Metadata { size, offset: _, origin_size: _ } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action: MirProjectionAction::ReadAction(continuation) }, ..],
        memory: memory,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToAllocation(allocation), value: map::get(memory, allocation), projections: DerefProjectionPath { referenced, size, offset: 0, origin_size: MirMetadataSize::NoMetadataSize(), tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::ReadAction(continuation) }, ..],
        memory: memory,
    }
    where allocation: AllocId, referenced: ProjectionElems, size: MetadataSize, tail: ProjectionElems, locals: List, continuation: Continuation, memory: Map;

    traverse_projection_allocation_reference_reborrow: {
        k: [Execution::TraverseProjection { target: _, value: Value::AllocationReference { allocation, projections: referenced, metadata: MirMetadata::Metadata { size, offset: _, origin_size: _ } }, projections: Projections::ProjectionsCons { head: Projection::Deref(), tail }, contexts: _, locals, action: MirProjectionAction::ReferenceAction { place, mutability, metadata } }, ..],
        memory: memory,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToAllocation(allocation), value: map::get(memory, allocation), projections: DerefProjectionPath { referenced, size, offset: 0, origin_size: MirMetadataSize::NoMetadataSize(), tail }, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::ReferenceAction { place, mutability, metadata } }, ..],
        memory: memory,
    }
    where allocation: AllocId, referenced: ProjectionElems, size: MetadataSize, tail: ProjectionElems, locals: List, place: Place, mutability: Mutability, metadata: Metadata, memory: Map;

    continue_store: {
        k: [Execution::Continue { value, continuation: EvaluationContinuation::StoreAt(place) }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value }, ..],
    }
    where value: MirValue, place: Place;

    continue_aggregate_done: {
        k: [Execution::Continue { value, continuation: EvaluationContinuation::AggregateNext { place, kind, values, remaining: Operands::Nil() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: MaterializeAggregate { kind, values: list::concat(values, list::item(value)) } }, ..],
    }
    where value: MirValue, place: Place, kind: AggregateKind, values: List;

    continue_aggregate_next: {
        k: [Execution::Continue { value, continuation: EvaluationContinuation::AggregateNext { place, kind, values, remaining: Operands::Cons { head, tail } } }, ..],
    } => {
        k: [Execution::EvalOperand { operand: head, continuation: EvaluationContinuation::AggregateNext { place, kind, values: list::concat(values, list::item(value)), remaining: tail } }, ..],
    }
    where value: MirValue, place: Place, kind: AggregateKind, values: List, head: Operand, tail: Operands;

    #[k::requires(int::ge(count, 0))]
    finish_repeat: {
        k: [Execution::Continue { value, continuation: EvaluationContinuation::FinishRepeat { place, count } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Range { elements: list::make(count, value) } }, ..],
    }
    where value: MirValue, place: Place, count: Int;

    finish_len: {
        k: [Execution::Continue { value: Value::Range(elements), continuation: EvaluationContinuation::FinishLen { place } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: list::size(elements), width: 64, signed: false } }, ..],
    }
    where elements: List, place: Place;

    finish_discriminant: {
        k: [Execution::Continue { value: Value::Aggregate { variant, fields: _ }, continuation: EvaluationContinuation::FinishDiscriminant { place, info: MirTypeInfo::EnumType { name: _, adt_def: _, discriminants, fields: _, layout: _ } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: LookupDiscriminant { discriminants, index: variant }, width: 0, signed: false } }, ..],
    }
    where variant: Int, place: Place, discriminants: Discriminants;

    finish_pointer_unsize: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size: MirMetadataSize::StaticSize(size), offset, origin_size } }, continuation: EvaluationContinuation::FinishCast { place, kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset, origin_size } } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, size: Int, offset: Int, origin_size: MetadataSize, place: Place;

    finish_reference_unsize: {
        k: [Execution::Continue { value: Value::Reference { height, place: referenced, mutability, metadata: MirMetadata::Metadata { size: MirMetadataSize::StaticSize(size), offset, origin_size } }, continuation: EvaluationContinuation::FinishCast { place, kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Reference { height, place: referenced, mutability, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset, origin_size } } }, ..],
    }
    where height: Int, referenced: Place, mutability: Mutability, size: Int, offset: Int, origin_size: MetadataSize, place: Place;

    finish_allocation_reference_unsize: {
        k: [Execution::Continue { value: Value::AllocationReference { allocation, projections, metadata: MirMetadata::Metadata { size: MirMetadataSize::StaticSize(size), offset, origin_size } }, continuation: EvaluationContinuation::FinishCast { place, kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::AllocationReference { allocation, projections, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset, origin_size } } }, ..],
    }
    where allocation: AllocId, projections: ProjectionElems, size: Int, offset: Int, origin_size: MetadataSize, place: Place;

    finish_reference_transmute_identity: {
        k: [Execution::Continue { value: Value::Reference { height, place: referenced, mutability, metadata }, continuation: EvaluationContinuation::FinishTransmute { place, source: info, target: info } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Reference { height, place: referenced, mutability, metadata } }, ..],
    }
    where height: Int, referenced: Place, mutability: Mutability, metadata: Metadata, place: Place, info: TypeInfo;

    finish_pointer_transmute_identity: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishTransmute { place, source: info, target: info } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, place: Place, info: TypeInfo;

    finish_allocation_reference_transmute_identity: {
        k: [Execution::Continue { value: Value::AllocationReference { allocation, projections, metadata }, continuation: EvaluationContinuation::FinishTransmute { place, source: info, target: info } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::AllocationReference { allocation, projections, metadata } }, ..],
    }
    where allocation: AllocId, projections: ProjectionElems, metadata: Metadata, place: Place, info: TypeInfo;

    finish_same_pointee_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place, source: MirTypeInfo::PointerType { pointee }, target: MirTypeInfo::PointerType { pointee } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, pointee: Ty, place: Place;

    finish_same_pointee_ref_to_ref_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place, source: MirTypeInfo::ReferenceType { pointee }, target: MirTypeInfo::ReferenceType { pointee } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, pointee: Ty, place: Place;

    finish_same_pointee_ref_to_ptr_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place, source: MirTypeInfo::ReferenceType { pointee }, target: MirTypeInfo::PointerType { pointee } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, pointee: Ty, place: Place;

    finish_same_pointee_ptr_to_ref_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place, source: MirTypeInfo::PointerType { pointee }, target: MirTypeInfo::ReferenceType { pointee } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, pointee: Ty, place: Place;

    #[k::rule(owise)]
    begin_projected_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place: destination, source: MirTypeInfo::PointerType { pointee: source }, target: MirTypeInfo::PointerType { pointee: target } } }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, source), target: map::get(types, target), projections: Projections::ProjectionsEmpty(), target_size: MetadataSizeOf { info: map::get(types, target) } }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: Ty, target: Ty, types: Map;

    #[k::rule(owise)]
    begin_projected_ref_to_ref_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place: destination, source: MirTypeInfo::ReferenceType { pointee: source }, target: MirTypeInfo::ReferenceType { pointee: target } } }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, source), target: map::get(types, target), projections: Projections::ProjectionsEmpty(), target_size: MetadataSizeOf { info: map::get(types, target) } }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: Ty, target: Ty, types: Map;

    #[k::rule(owise)]
    begin_projected_ref_to_ptr_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place: destination, source: MirTypeInfo::ReferenceType { pointee: source }, target: MirTypeInfo::PointerType { pointee: target } } }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, source), target: map::get(types, target), projections: Projections::ProjectionsEmpty(), target_size: MetadataSizeOf { info: map::get(types, target) } }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: Ty, target: Ty, types: Map;

    #[k::rule(owise)]
    begin_projected_ptr_to_ref_ptr_cast: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability, metadata }, continuation: EvaluationContinuation::FinishPtrCast { place: destination, source: MirTypeInfo::PointerType { pointee: source }, target: MirTypeInfo::ReferenceType { pointee: target } } }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, source), target: map::get(types, target), projections: Projections::ProjectionsEmpty(), target_size: MetadataSizeOf { info: map::get(types, target) } }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: Ty, target: Ty, types: Map;

    resolve_ptr_cast_done: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place: MirPlace::Place { local, projections: pointer_projections }, mutability, metadata, destination, source: info, target: info, projections, target_size }, ..],
    } => {
        k: [Execution::SetLocalValue { place: destination, value: Value::Pointer { height, place: MirPlace::Place { local, projections: AppendCastProjections { first: pointer_projections, second: projections } }, mutability, metadata: ConvertPointerMetadata { metadata, target_size } } }, ..],
    }
    where height: Int, local: Int, pointer_projections: ProjectionElems, mutability: Mutability, metadata: Metadata, destination: Place, info: TypeInfo, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_primitive_to_zst: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::PrimitiveType { primitive: _ }, target: MirTypeInfo::VoidType(), projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::VoidType(), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::ToZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_array_to_zst: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::ArrayType { element: _, size: _ }, target: MirTypeInfo::VoidType(), projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::VoidType(), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::ToZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_pointer_to_zst: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::PointerType { pointee: _ }, target: MirTypeInfo::VoidType(), projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::VoidType(), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::ToZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_zst_to_primitive: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::PrimitiveType { primitive }, projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::PrimitiveType { primitive }, target: MirTypeInfo::PrimitiveType { primitive }, projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::FromZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, primitive: PrimitiveType, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_zst_to_array: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::ArrayType { element, size }, projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::ArrayType { element, size }, target: MirTypeInfo::ArrayType { element, size }, projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::FromZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, element: Ty, size: MaybeTyConst, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_zst_to_pointer: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::VoidType(), target: MirTypeInfo::PointerType { pointee }, projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::PointerType { pointee }, target: MirTypeInfo::PointerType { pointee }, projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::FromZst(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, pointee: Ty, projections: ProjectionElems, target_size: MetadataSize;

    #[k::requires(bool::and(
    ZeroFieldOffset { layout },
    SameTypeInfo {
    first: MirTypeInfo::ArrayType { element: source_element, size: source_size },
    second: map::get(types, field),
    },
    ))]
    resolve_ptr_cast_array_to_exact_wrapper: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::ArrayType { element: source_element, size: source_size }, target: MirTypeInfo::StructType { name, adt_def, fields: MirTys::TysCons { head: field, tail: MirTys::TysEmpty() }, layout }, projections, target_size }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::ArrayType { element: source_element, size: source_size }, target: map::get(types, field), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::WrapStruct(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source_element: Ty, source_size: MaybeTyConst, name: String, adt_def: AdtDef, field: Ty, layout: MaybeLayoutShape, projections: ProjectionElems, target_size: MetadataSize, types: Map;

    #[k::rule(owise)]
    resolve_ptr_cast_compare_different: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source, target, projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Source(), height, pointer_place, mutability, metadata, destination, source, target, projections, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: TypeInfo, target: TypeInfo, projections: ProjectionElems, target_size: MetadataSize;

    #[k::requires(ZeroFieldOffset { layout })]
    resolve_ptr_cast_source_struct: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Source(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::StructType { name, adt_def, fields: MirTys::TysCons { head: field, tail: MirTys::TysEmpty() }, layout }, target, projections, target_size }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, field), target, projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::Field { field: 0, ty: field }, tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, name: String, adt_def: AdtDef, field: Ty, layout: MaybeLayoutShape, target: TypeInfo, projections: ProjectionElems, target_size: MetadataSize, types: Map;

    resolve_ptr_cast_source_array: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Source(), height, pointer_place, mutability, metadata, destination, source: MirTypeInfo::ArrayType { element, size: _ }, target, projections, target_size }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source: map::get(types, element), target, projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::ConstantIndex { offset: 0, min_length: 0, from_end: false }, tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, element: Ty, target: TypeInfo, projections: ProjectionElems, target_size: MetadataSize, types: Map;

    #[k::rule(owise)]
    resolve_ptr_cast_source_done: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Source(), height, pointer_place, mutability, metadata, destination, source, target, projections, target_size }, ..],
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::TargetPhase(), height, pointer_place, mutability, metadata, destination, source, target, projections, target_size }, ..],
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: TypeInfo, target: TypeInfo, projections: ProjectionElems, target_size: MetadataSize;

    resolve_ptr_cast_target_array: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::TargetPhase(), height, pointer_place, mutability, metadata, destination, source, target: MirTypeInfo::ArrayType { element, size: _ }, projections, target_size }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source, target: map::get(types, element), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::SingletonArray(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: TypeInfo, element: Ty, projections: ProjectionElems, target_size: MetadataSize, types: Map;

    #[k::requires(ZeroFieldOffset { layout })]
    resolve_ptr_cast_target_struct: {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::TargetPhase(), height, pointer_place, mutability, metadata, destination, source, target: MirTypeInfo::StructType { name, adt_def, fields: MirTys::TysCons { head: field, tail: MirTys::TysEmpty() }, layout }, projections, target_size }, ..],
        types: types,
    } => {
        k: [Execution::ResolvePtrCast { phase: MirPtrCastPhase::Compare(), height, pointer_place, mutability, metadata, destination, source, target: map::get(types, field), projections: AppendCastProjections { first: projections, second: Projections::ProjectionsCons { head: Projection::WrapStruct(), tail: Projections::ProjectionsEmpty() } }, target_size }, ..],
        types: types,
    }
    where height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, destination: Place, source: TypeInfo, name: String, adt_def: AdtDef, field: Ty, layout: MaybeLayoutShape, projections: ProjectionElems, target_size: MetadataSize, types: Map;

    finish_neg: {
        k: [Execution::Continue { value: Value::Integer { value, width, signed: true }, continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpNeg() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateSigned { value: int::sub(0, value), width }, width, signed: true } }, ..],
    }
    where value: Int, width: Int, place: Place;

    finish_bool_not: {
        k: [Execution::Continue { value: Value::Boolean(value), continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpNot() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::not(value)) }, ..],
    }
    where value: Bool, place: Place;

    finish_int_not: {
        k: [Execution::Continue { value: Value::Integer { value, width, signed }, continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpNot() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::bit_xor(value, int::sub(0, 1)), width, signed }, width, signed } }, ..],
    }
    where value: Int, width: Int, signed: Bool, place: Place;

    finish_pointer_metadata: {
        k: [Execution::Continue { value: Value::Pointer { height: _, place: _, mutability: _, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset: _, origin_size: _ } }, continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpPtrMetadata() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: size, width: 64, signed: false } }, ..],
    }
    where size: Int, place: Place;

    finish_reference_metadata: {
        k: [Execution::Continue { value: Value::Reference { height: _, place: _, mutability: _, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset: _, origin_size: _ } }, continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpPtrMetadata() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: size, width: 64, signed: false } }, ..],
    }
    where size: Int, place: Place;

    finish_allocation_reference_metadata: {
        k: [Execution::Continue { value: Value::AllocationReference { allocation: _, projections: _, metadata: MirMetadata::Metadata { size: MirMetadataSize::DynamicSize(size), offset: _, origin_size: _ } }, continuation: EvaluationContinuation::FinishUnary { place, operation: MirUnaryOp::UnOpPtrMetadata() } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: size, width: 64, signed: false } }, ..],
    }
    where size: Int, place: Place;

    continue_binary_right: {
        k: [Execution::Continue { value: lhs, continuation: EvaluationContinuation::BinaryRight { place, operation, rhs, checked } }, ..],
    } => {
        k: [Execution::EvalOperand { operand: rhs, continuation: EvaluationContinuation::FinishBinary { place, operation, lhs, checked } }, ..],
    }
    where lhs: MirValue, operation: BinaryOp, place: Place, rhs: Operand, checked: Bool;

    #[k::requires(int::eq(TruncateInteger { value: int::add(lhs, rhs), width, signed }, int::add(lhs, rhs)))]
    finish_add: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpAdd(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::add(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::eq(TruncateInteger { value: int::add(lhs, rhs), width, signed }, int::add(lhs, rhs)))]
    finish_add_unchecked: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpAddUnchecked(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::add(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_checked_add: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: true, operation: MirBinaryOp::BinOpAdd(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Aggregate { variant: 0, fields: list::concat(list::item(Value::Integer { value: TruncateInteger { value: int::add(lhs, rhs), width, signed }, width, signed }), list::concat(list::item(Value::Boolean(int::ne(TruncateInteger { value: int::add(lhs, rhs), width, signed }, int::add(lhs, rhs)))), list::empty())) } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::eq(TruncateInteger { value: int::sub(lhs, rhs), width, signed }, int::sub(lhs, rhs)))]
    finish_sub: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpSub(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::sub(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::eq(TruncateInteger { value: int::sub(lhs, rhs), width, signed }, int::sub(lhs, rhs)))]
    finish_sub_unchecked: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpSubUnchecked(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::sub(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_checked_sub: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: true, operation: MirBinaryOp::BinOpSub(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Aggregate { variant: 0, fields: list::concat(list::item(Value::Integer { value: TruncateInteger { value: int::sub(lhs, rhs), width, signed }, width, signed }), list::concat(list::item(Value::Boolean(int::ne(TruncateInteger { value: int::sub(lhs, rhs), width, signed }, int::sub(lhs, rhs)))), list::empty())) } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::eq(TruncateInteger { value: int::mul(lhs, rhs), width, signed }, int::mul(lhs, rhs)))]
    finish_mul: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpMul(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::mul(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::eq(TruncateInteger { value: int::mul(lhs, rhs), width, signed }, int::mul(lhs, rhs)))]
    finish_mul_unchecked: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpMulUnchecked(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::mul(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_checked_mul: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: true, operation: MirBinaryOp::BinOpMul(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Aggregate { variant: 0, fields: list::concat(list::item(Value::Integer { value: TruncateInteger { value: int::mul(lhs, rhs), width, signed }, width, signed }), list::concat(list::item(Value::Boolean(int::ne(TruncateInteger { value: int::mul(lhs, rhs), width, signed }, int::mul(lhs, rhs)))), list::empty())) } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(bool::and(int::ne(rhs, 0), int::eq(TruncateInteger { value: int::div(lhs, rhs), width, signed }, int::div(lhs, rhs))))]
    finish_div: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpDiv(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::div(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(bool::and(int::ne(rhs, 0), int::eq(TruncateInteger { value: int::sub(lhs, int::mul(int::div(lhs, rhs), rhs)), width, signed }, int::sub(lhs, int::mul(int::div(lhs, rhs), rhs)))))]
    finish_rem: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpRem(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::sub(lhs, int::mul(int::div(lhs, rhs), rhs)), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_int_bit_xor: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitXor(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: int::bit_xor(lhs, rhs), width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_int_bit_and: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitAnd(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: int::bit_and(lhs, rhs), width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_int_bit_or: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitOr(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: int::bit_or(lhs, rhs), width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_shl: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpShl(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::shift_left(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::lt(rhs, width))]
    finish_shl_unchecked: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpShlUnchecked(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::shift_left(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_shr: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpShr(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::shift_right(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    #[k::requires(int::lt(rhs, width))]
    finish_shr_unchecked: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpShrUnchecked(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Integer { value: TruncateInteger { value: int::shift_right(lhs, rhs), width, signed }, width, signed } }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_bool_bit_xor: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitXor(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::ne(lhs, rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_bit_and: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitAnd(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::and(lhs, rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_bit_or: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpBitOr(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::or(lhs, rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    #[k::requires(int::eq(offset, 0))]
    finish_pointer_offset_zero: {
        k: [Execution::Continue { value: Value::Integer { value: offset, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpOffset(), lhs: Value::Pointer { height, place: pointer_place, mutability, metadata } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata } }, ..],
    }
    where offset: Int, height: Int, pointer_place: Place, mutability: Mutability, metadata: Metadata, place: Place;

    #[k::requires(bool::and(
    int::ge(offset, 0),
    int::le(int::add(current_offset, offset), origin_size),
    ))]
    #[k::rule(owise)]
    finish_pointer_offset_dynamic: {
        k: [Execution::Continue { value: Value::Integer { value: offset, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpOffset(), lhs: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size, offset: current_offset, origin_size: MirMetadataSize::DynamicSize(origin_size) } } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size, offset: int::add(current_offset, offset), origin_size: MirMetadataSize::DynamicSize(origin_size) } } }, ..],
    }
    where offset: Int, height: Int, pointer_place: Place, mutability: Mutability, size: MetadataSize, current_offset: Int, origin_size: Int, place: Place;

    #[k::requires(bool::and(
    int::ge(offset, 0),
    int::le(int::add(current_offset, offset), origin_size),
    ))]
    #[k::rule(owise)]
    finish_pointer_offset_static: {
        k: [Execution::Continue { value: Value::Integer { value: offset, width: _, signed: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpOffset(), lhs: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size, offset: current_offset, origin_size: MirMetadataSize::StaticSize(origin_size) } } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Pointer { height, place: pointer_place, mutability, metadata: MirMetadata::Metadata { size, offset: int::add(current_offset, offset), origin_size: MirMetadataSize::StaticSize(origin_size) } } }, ..],
    }
    where offset: Int, height: Int, pointer_place: Place, mutability: Mutability, size: MetadataSize, current_offset: Int, origin_size: Int, place: Place;

    finish_pointer_eq_same: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability: _, metadata }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpEq(), lhs: Value::Pointer { height, place: pointer_place, mutability: _, metadata } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(true) }, ..],
    }
    where height: Int, pointer_place: Place, metadata: Metadata, place: Place;

    #[k::rule(owise)]
    finish_pointer_eq_different: {
        k: [Execution::Continue { value: Value::Pointer { height: _, place: _, mutability: _, metadata: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpEq(), lhs: Value::Pointer { height: _, place: _, mutability: _, metadata: _ } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    }
    where place: Place;

    finish_pointer_ne_same: {
        k: [Execution::Continue { value: Value::Pointer { height, place: pointer_place, mutability: _, metadata }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpNe(), lhs: Value::Pointer { height, place: pointer_place, mutability: _, metadata } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    }
    where height: Int, pointer_place: Place, metadata: Metadata, place: Place;

    #[k::rule(owise)]
    finish_pointer_ne_different: {
        k: [Execution::Continue { value: Value::Pointer { height: _, place: _, mutability: _, metadata: _ }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpNe(), lhs: Value::Pointer { height: _, place: _, mutability: _, metadata: _ } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(true) }, ..],
    }
    where place: Place;

    finish_eq: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpEq(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::eq(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_lt: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpLt(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::lt(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_le: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpLe(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::le(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_ne: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpNe(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::ne(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_ge: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpGe(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::ge(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_gt: {
        k: [Execution::Continue { value: Value::Integer { value: rhs, width, signed }, continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpGt(), lhs: Value::Integer { value: lhs, width, signed } } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(int::gt(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, width: Int, signed: Bool, place: Place;

    finish_bool_eq: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpEq(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::eq(lhs, rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_lt: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpLt(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::and(bool::not(lhs), rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_le: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpLe(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::or(bool::not(lhs), bool::and(lhs, rhs))) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_ne: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpNe(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::ne(lhs, rhs)) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_ge: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpGe(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::or(bool::not(rhs), bool::and(rhs, lhs))) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    finish_bool_gt: {
        k: [Execution::Continue { value: Value::Boolean(rhs), continuation: EvaluationContinuation::FinishBinary { place, checked: false, operation: MirBinaryOp::BinOpGt(), lhs: Value::Boolean(lhs) } }, ..],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(bool::and(lhs, bool::not(rhs))) }, ..],
    }
    where lhs: Bool, rhs: Bool, place: Place;

    set_local_value: {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }, value }, ..],
        locals: locals,
    } => {
        k: [Execution::WriteLocal { entry: list::get(locals, local), index: local, value }, ..],
        locals: locals,
    }
    where value: MirValue, local: Int, locals: List;

    set_projected_local_value: {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local, projections: Projections::ProjectionsCons { head, tail } }, value }, ..],
        locals: locals,
    } => {
        k: [Execution::WriteProjectedLocal { entry: list::get(locals, local), local, projections: Projections::ProjectionsCons { head, tail }, value }, ..],
        locals: locals,
    }
    where value: MirValue, local: Int, head: ProjectionElem, tail: ProjectionElems, locals: List;

    write_projected_local: {
        k: [Execution::WriteProjectedLocal { entry: LocalValue::TypedValue { value: original, ty: _, mutability: _ }, local, projections, value }, ..],
        locals: locals,
    } => {
        k: [Execution::TraverseProjection { target: MirProjectionTarget::ToLocal(local), value: original, projections, contexts: MirProjectionContexts::ContextsEmpty(), locals, action: MirProjectionAction::WriteAction(value) }, ..],
        locals: locals,
    }
    where original: MirValue, local: Int, projections: ProjectionElems, value: MirValue, locals: List;

    write_initialized_local: {
        k: [Execution::WriteLocal { entry: LocalValue::TypedValue { value: _, ty, mutability }, index, value }, ..],
        locals: locals,
    } => {
        k: [..],
        locals: list::update(locals, index, LocalValue::TypedValue { value, ty, mutability }),
    }
    where value: MirValue, ty: Ty, mutability: Mutability, index: Int, locals: List;

    write_new_local: {
        k: [Execution::WriteLocal { entry: LocalValue::NewLocal { ty, mutability }, index, value }, ..],
        locals: locals,
    } => {
        k: [..],
        locals: list::update(locals, index, LocalValue::TypedValue { value, ty, mutability }),
    }
    where value: MirValue, ty: Ty, mutability: Mutability, index: Int, locals: List;
}

k::rules! {
    for Machine;

    goto: {
        k: [Execution::ExecTerminator(MirTerminator::Goto(target)), ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where target: Int;

    switch_int: {
        k: [Execution::ExecTerminator(MirTerminator::SwitchInt { discr, targets }), ..],
    } => {
        k: [Execution::EvalOperand { operand: discr, continuation: EvaluationContinuation::SelectBlock(targets) }, ..],
    }
    where discr: Operand, targets: SwitchTargets;

    call_function: {
        k: [Execution::ExecTerminator(MirTerminator::Call { function: MirCallTarget::ConstantFunction { span, ty: callee, id: _ }, args, destination, target, unwind }), ..],
        current_func: current_func,
        current_body: current_body,
        caller: old_caller,
        dest: old_dest,
        target: old_target,
        unwind: old_unwind,
        locals: caller_locals,
        stack: stack,
        functions: functions,
    } => {
        k: [Execution::SetArgsFromStack { index: 1, args }, Execution::ExecBlockIdx(0), ..],
        current_func: callee,
        current_body: FunctionBlocks { function: map::get(functions, callee) },
        caller: current_func,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind: unwind,
        locals: FunctionLocals { function: map::get(functions, callee) },
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller: old_caller, dest: old_dest, target: old_target, unwind: old_unwind, locals: caller_locals, span }), stack),
        functions: functions,
    }
    where span: Int, callee: Ty, args: Operands, destination: Place, target: Int, unwind: UnwindAction, current_func: Ty, current_body: List, old_caller: Ty, old_dest: Place, old_target: MaybeBasicBlockIdx, old_unwind: UnwindAction, caller_locals: List, stack: List, functions: Map;

    set_args_done: {
        k: [Execution::SetArgsFromStack { index: _, args: Operands::Nil() }, ..],
    } => {
        k: [..],
    };

    set_args_cons: {
        k: [Execution::SetArgsFromStack { index, args: Operands::Cons { head, tail } }, ..],
    } => {
        k: [Execution::SetArgFromStack { index, operand: head }, Execution::SetArgsFromStack { index: int::add(index, 1), args: tail }, ..],
    }
    where index: Int, head: Operand, tail: Operands;

    set_constant_arg: {
        k: [Execution::SetArgFromStack { index, operand: MirOperand::Constant(value) }, ..],
    } => {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local: index, projections: Projections::ProjectionsEmpty() }, value }, ..],
    }
    where index: Int, value: MirValue;

    set_copied_arg: {
        k: [Execution::SetArgFromStack { index, operand: MirOperand::Copy(MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }) }, ..],
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller, dest, target, unwind, locals: caller_locals, span }), rest),
    } => {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local: index, projections: Projections::ProjectionsEmpty() }, value: AdjustRef { value: LocalValueOf { entry: list::get(caller_locals, local) }, offset: 1 } }, ..],
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller, dest, target, unwind, locals: caller_locals, span }), rest),
    }
    where index: Int, local: Int, caller: Ty, dest: Place, target: MaybeBasicBlockIdx, unwind: UnwindAction, caller_locals: List, span: Int, rest: List;

    set_moved_arg: {
        k: [Execution::SetArgFromStack { index, operand: MirOperand::Move(MirPlace::Place { local, projections: Projections::ProjectionsEmpty() }) }, ..],
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller, dest, target, unwind, locals: caller_locals, span }), rest),
    } => {
        k: [Execution::SetLocalValue { place: MirPlace::Place { local: index, projections: Projections::ProjectionsEmpty() }, value: AdjustRef { value: LocalValueOf { entry: list::get(caller_locals, local) }, offset: 1 } }, ..],
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller, dest, target, unwind, locals: list::update(caller_locals, local, MovedEntry { entry: list::get(caller_locals, local) }), span }), rest),
    }
    where index: Int, local: Int, caller: Ty, dest: Place, target: MaybeBasicBlockIdx, unwind: UnwindAction, caller_locals: List, span: Int, rest: List;

    assert: {
        k: [Execution::ExecTerminator(MirTerminator::Assert { condition, expected, message, target, unwind: _ }), ..],
    } => {
        k: [Execution::Expect { condition, expected, message }, Execution::ExecBlockIdx(target), ..],
    }
    where condition: Operand, expected: Bool, message: AssertMessage, target: Int;

    drop: {
        k: [Execution::ExecTerminator(MirTerminator::Drop { place: _, target, unwind: _ }), ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where target: Int;

    unreachable: {
        k: [Execution::ExecTerminator(MirTerminator::Unreachable()), ..],
    } => {
        k: [Execution::ProgramError { error: MirExecutionError::ReachedUnreachable() }, ..],
    };

    expect: {
        k: [Execution::Expect { condition, expected, message }, ..],
    } => {
        k: [Execution::EvalOperand { operand: condition, continuation: EvaluationContinuation::FinishAssert { expected, message } }, ..],
    }
    where condition: Operand, expected: Bool, message: AssertMessage;

    #[k::requires(bool::eq(condition, expected))]
    assert_succeeds: {
        k: [Execution::Continue { value: Value::Boolean(condition), continuation: EvaluationContinuation::FinishAssert { expected, message: _ } }, ..],
    } => {
        k: [..],
    }
    where condition: Bool, expected: Bool;

    #[k::requires(bool::ne(condition, expected))]
    #[k::rule(owise)]
    assert_fails: {
        k: [Execution::Continue { value: Value::Boolean(condition), continuation: EvaluationContinuation::FinishAssert { expected, message } }, ..],
    } => {
        k: [Execution::ProgramError { error: MirExecutionError::AssertError { message } }, ..],
    }
    where condition: Bool, expected: Bool, message: AssertMessage;

    select_otherwise: {
        k: [Execution::Continue { value: _, continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesEmpty(), otherwise }) }, ..],
    } => {
        k: [Execution::ExecBlockIdx(otherwise), ..],
    }
    where otherwise: Int;

    select_true: {
        k: [Execution::Continue { value: Value::Boolean(true), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: 1, target }, tail: _ }, otherwise: _ }) }, ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where target: Int;

    #[k::requires(int::ne(branch_value, 1))]
    #[k::rule(owise)]
    select_true_next: {
        k: [Execution::Continue { value: Value::Boolean(true), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: branch_value, target: _ }, tail }, otherwise }) }, ..],
    } => {
        k: [Execution::Continue { value: Value::Boolean(true), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: tail, otherwise }) }, ..],
    }
    where branch_value: Int, tail: Branches, otherwise: Int;

    select_false: {
        k: [Execution::Continue { value: Value::Boolean(false), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: 0, target }, tail: _ }, otherwise: _ }) }, ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where target: Int;

    #[k::requires(int::ne(branch_value, 0))]
    #[k::rule(owise)]
    select_false_next: {
        k: [Execution::Continue { value: Value::Boolean(false), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: branch_value, target: _ }, tail }, otherwise }) }, ..],
    } => {
        k: [Execution::Continue { value: Value::Boolean(false), continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: tail, otherwise }) }, ..],
    }
    where branch_value: Int, tail: Branches, otherwise: Int;

    #[k::requires(int::eq(branch_value, TruncateUnsigned { value, width }))]
    select_integer: {
        k: [Execution::Continue { value: Value::Integer { value, width, signed: _ }, continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: branch_value, target }, tail: _ }, otherwise: _ }) }, ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where value: Int, width: Int, branch_value: Int, target: Int;

    #[k::requires(int::ne(branch_value, TruncateUnsigned { value, width }))]
    #[k::rule(owise)]
    select_integer_next: {
        k: [Execution::Continue { value: Value::Integer { value, width, signed }, continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: BranchList::BranchesCons { head: MirBranch::Branch { value: branch_value, target: _ }, tail }, otherwise }) }, ..],
    } => {
        k: [Execution::Continue { value: Value::Integer { value, width, signed }, continuation: EvaluationContinuation::SelectBlock(MirSwitchTargets::SwitchTargets { branches: tail, otherwise }) }, ..],
    }
    where value: Int, width: Int, signed: Bool, branch_value: Int, tail: Branches, otherwise: Int;

    return_to_caller: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        current_func: callee,
        current_body: callee_body,
        caller: caller,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind: callee_unwind,
        locals: list::concat(list::item(LocalValue::TypedValue { value, ty: return_ty, mutability: return_mutability }), callee_locals_tail),
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller: new_caller, dest: new_dest, target: new_target, unwind: new_unwind, locals: new_locals, span: return_span }), remaining_stack),
        functions: functions,
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::SetLocalValue { place: destination, value: AdjustRef { value, offset: int::sub(0, 1) } }, Execution::ExecBlockIdx(target), ..],
        current_func: caller,
        current_body: FunctionBlocks { function: map::get(functions, caller) },
        caller: new_caller,
        dest: new_dest,
        target: new_target,
        unwind: new_unwind,
        locals: new_locals,
        stack: remaining_stack,
        functions: functions,
        ret_val: ReturnValue::NoReturn(),
    }
    where callee: Ty, callee_body: List, caller: Ty, destination: Place, target: Int, callee_unwind: UnwindAction, value: MirValue, return_ty: Ty, return_mutability: Mutability, callee_locals_tail: List, new_caller: Ty, new_dest: Place, new_target: MaybeBasicBlockIdx, new_unwind: UnwindAction, new_locals: List, return_span: Int, remaining_stack: List, functions: Map;

    return_unit_to_caller: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        current_func: callee,
        current_body: callee_body,
        caller: caller,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind: callee_unwind,
        locals: list::concat(list::item(LocalValue::NewLocal { ty: return_ty, mutability: return_mutability }), callee_locals_tail),
        stack: list::concat(list::item(MirStackFrame::StackFrame { caller: new_caller, dest: new_dest, target: new_target, unwind: new_unwind, locals: new_locals, span: return_span }), remaining_stack),
        functions: functions,
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
        current_func: caller,
        current_body: FunctionBlocks { function: map::get(functions, caller) },
        caller: new_caller,
        dest: new_dest,
        target: new_target,
        unwind: new_unwind,
        locals: new_locals,
        stack: remaining_stack,
        functions: functions,
        ret_val: ReturnValue::NoReturn(),
    }
    where callee: Ty, callee_body: List, caller: Ty, destination: Place, target: Int, callee_unwind: UnwindAction, return_ty: Ty, return_mutability: Mutability, callee_locals_tail: List, new_caller: Ty, new_dest: Place, new_target: MaybeBasicBlockIdx, new_unwind: UnwindAction, new_locals: List, return_span: Int, remaining_stack: List, functions: Map;

    top_level_return: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        target: MirMaybeBasicBlockIdx::NoBasicBlockIdx(),
        locals: locals,
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::ReturnLocal { entry: list::get(locals, 0) }, ..],
        target: MirMaybeBasicBlockIdx::NoBasicBlockIdx(),
        locals: locals,
        ret_val: ReturnValue::NoReturn(),
    }
    where locals: List;

    return_local: {
        k: [Execution::ReturnLocal { entry: LocalValue::TypedValue { value, ty: _, mutability: _ } }, ..],
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::EndProgram(), ..],
        ret_val: ReturnValue::Returned(value),
    }
    where value: MirValue;

    end_program: {
        k: [Execution::EndProgram(), ..],
    } => {
        k: [..],
    };
}

/// All-path claim spanning builtin-list block lookup, local dataflow, graph control, and return.
#[k::claim(all_paths, label = "list-add-switch-return")]
fn list_add_switch_return(
    k::cells! {
        k: k::configuration::KCell(Execution::Run()),
        current_func: k::configuration::Cell(MirTy::TyId(int::sub(0, 1))),
        CurrentFrame::current_body: k::configuration::Cell(list::concat(
            list::item(BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(MirPlace::Place(1, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(20, 64, false)))),
                    StatementList::StatementsCons(
                        MirStatement::Assign(MirPlace::Place(2, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(22, 64, false)))),
                        StatementList::StatementsCons(
                            MirStatement::Assign(MirPlace::Place(3, Projections::ProjectionsEmpty()), MirRvalue::Binary(MirBinaryOp::BinOpAdd(), MirOperand::Copy(MirPlace::Place(1, Projections::ProjectionsEmpty())), MirOperand::Copy(MirPlace::Place(2, Projections::ProjectionsEmpty())))),
                            StatementList::StatementsCons(
                                MirStatement::Assign(MirPlace::Place(4, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Boolean(true)))),
                                StatementList::StatementsEmpty(),
                            ),
                        ),
                    ),
                ),
                MirTerminator::Goto(1),
            )),
            list::concat(
                list::item(BlockSyntax::Block(
                    StatementList::StatementsEmpty(),
                    MirTerminator::SwitchInt(
                        MirOperand::Copy(MirPlace::Place(4, Projections::ProjectionsEmpty())),
                        MirSwitchTargets::SwitchTargets(
                            BranchList::BranchesCons(MirBranch::Branch(1, 2), BranchList::BranchesEmpty()),
                            3,
                        ),
                    ),
                )),
                list::concat(
                    list::item(BlockSyntax::Block(
                        StatementList::StatementsCons(
                            MirStatement::Assign(MirPlace::Place(0, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Copy(MirPlace::Place(3, Projections::ProjectionsEmpty())))),
                            StatementList::StatementsEmpty(),
                        ),
                        MirTerminator::Return(),
                    )),
                    list::concat(
                        list::item(BlockSyntax::Block(
                            StatementList::StatementsCons(
                                MirStatement::Assign(MirPlace::Place(0, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(0, 64, false)))),
                                StatementList::StatementsEmpty(),
                            ),
                            MirTerminator::Return(),
                        )),
                        list::empty(),
                    ),
                ),
            ),
        )),
        CurrentFrame::caller: k::configuration::Cell(MirTy::TyId(int::sub(0, 1))),
        CurrentFrame::dest: k::configuration::Cell(MirPlace::Place(int::sub(0, 1), Projections::ProjectionsEmpty())),
        CurrentFrame::target: k::configuration::Cell(MirMaybeBasicBlockIdx::NoBasicBlockIdx()),
        CurrentFrame::unwind: k::configuration::Cell(MirUnwindAction::UnwindContinue()),
        CurrentFrame::locals: k::configuration::Cell(list::concat(
            list::item(LocalValue::NewLocal(MirTy::TyId(0), LocalMutability::Mutable())),
            list::concat(
                list::item(LocalValue::NewLocal(MirTy::TyId(1), LocalMutability::Mutable())),
                list::concat(
                    list::item(LocalValue::NewLocal(MirTy::TyId(2), LocalMutability::Mutable())),
                    list::concat(
                        list::item(LocalValue::NewLocal(MirTy::TyId(3), LocalMutability::Mutable())),
                        list::concat(
                            list::item(LocalValue::NewLocal(MirTy::TyId(4), LocalMutability::Mutable())),
                            list::empty(),
                        ),
                    ),
                ),
            ),
        )),
        stack: k::configuration::Cell(list::empty()),
        functions: k::configuration::Cell(map![.Map]),
        types: k::configuration::Cell(map![.Map]),
        memory: k::configuration::Cell(map![.Map]),
        ret_val: k::configuration::Cell(ReturnValue::NoReturn()),
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        current_func: k::configuration::Cell(MirTy::TyId(int::sub(0, 1))),
        CurrentFrame::current_body: k::configuration::Cell(list::concat(
            list::item(BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(MirPlace::Place(1, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(20, 64, false)))),
                    StatementList::StatementsCons(
                        MirStatement::Assign(MirPlace::Place(2, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(22, 64, false)))),
                        StatementList::StatementsCons(
                            MirStatement::Assign(MirPlace::Place(3, Projections::ProjectionsEmpty()), MirRvalue::Binary(MirBinaryOp::BinOpAdd(), MirOperand::Copy(MirPlace::Place(1, Projections::ProjectionsEmpty())), MirOperand::Copy(MirPlace::Place(2, Projections::ProjectionsEmpty())))),
                            StatementList::StatementsCons(
                                MirStatement::Assign(MirPlace::Place(4, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Boolean(true)))),
                                StatementList::StatementsEmpty(),
                            ),
                        ),
                    ),
                ),
                MirTerminator::Goto(1),
            )),
            list::concat(
                list::item(BlockSyntax::Block(
                    StatementList::StatementsEmpty(),
                    MirTerminator::SwitchInt(
                        MirOperand::Copy(MirPlace::Place(4, Projections::ProjectionsEmpty())),
                        MirSwitchTargets::SwitchTargets(
                            BranchList::BranchesCons(MirBranch::Branch(1, 2), BranchList::BranchesEmpty()),
                            3,
                        ),
                    ),
                )),
                list::concat(
                    list::item(BlockSyntax::Block(
                        StatementList::StatementsCons(
                            MirStatement::Assign(MirPlace::Place(0, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Copy(MirPlace::Place(3, Projections::ProjectionsEmpty())))),
                            StatementList::StatementsEmpty(),
                        ),
                        MirTerminator::Return(),
                    )),
                    list::concat(
                        list::item(BlockSyntax::Block(
                            StatementList::StatementsCons(
                                MirStatement::Assign(MirPlace::Place(0, Projections::ProjectionsEmpty()), MirRvalue::Use(MirOperand::Constant(Value::Integer(0, 64, false)))),
                                StatementList::StatementsEmpty(),
                            ),
                            MirTerminator::Return(),
                        )),
                        list::empty(),
                    ),
                ),
            ),
        )),
        CurrentFrame::caller: k::configuration::Cell(MirTy::TyId(int::sub(0, 1))),
        CurrentFrame::dest: k::configuration::Cell(MirPlace::Place(int::sub(0, 1), Projections::ProjectionsEmpty())),
        CurrentFrame::target: k::configuration::Cell(MirMaybeBasicBlockIdx::NoBasicBlockIdx()),
        CurrentFrame::unwind: k::configuration::Cell(MirUnwindAction::UnwindContinue()),
        CurrentFrame::locals: k::configuration::Cell(list::concat(
            list::item(LocalValue::TypedValue(Value::Integer(42, 64, false), MirTy::TyId(0), LocalMutability::Mutable())),
            list::concat(
                list::item(LocalValue::TypedValue(Value::Integer(20, 64, false), MirTy::TyId(1), LocalMutability::Mutable())),
                list::concat(
                    list::item(LocalValue::TypedValue(Value::Integer(22, 64, false), MirTy::TyId(2), LocalMutability::Mutable())),
                    list::concat(
                        list::item(LocalValue::TypedValue(Value::Integer(42, 64, false), MirTy::TyId(3), LocalMutability::Mutable())),
                        list::concat(
                            list::item(LocalValue::TypedValue(Value::Boolean(true), MirTy::TyId(4), LocalMutability::Mutable())),
                            list::empty(),
                        ),
                    ),
                ),
            ),
        )),
        stack: k::configuration::Cell(list::empty()),
        functions: k::configuration::Cell(map![.Map]),
        types: k::configuration::Cell(map![.Map]),
        memory: k::configuration::Cell(map![.Map]),
        ret_val: k::configuration::Cell(ReturnValue::Returned(Value::Integer(42, 64, false))),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
    use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
    use krs_ir_levels::{DefinitionIr, SemanticTheory};

    fn package_context() -> PackageContext {
        PackageContext::new(
            "KRS-KMIR",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "workspace",
            "krs_kmir_semantics",
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("valid package context")
    }

    fn remove_first_list_get_argument(value: &mut serde_json::Value) -> bool {
        match value {
            serde_json::Value::Object(object) => {
                if object.get("term_kind").and_then(serde_json::Value::as_str) == Some("list")
                    && object.get("operation").and_then(serde_json::Value::as_str) == Some("get")
                    && let Some(arguments) = object
                        .get_mut("arguments")
                        .and_then(serde_json::Value::as_array_mut)
                {
                    arguments.pop();
                    return true;
                }
                object.values_mut().any(remove_first_list_get_argument)
            }
            serde_json::Value::Array(values) => {
                values.iter_mut().any(remove_first_list_get_argument)
            }
            _ => false,
        }
    }

    #[test]
    fn readable_kmir_slice_collects_and_lowers_deterministically() {
        let descriptors = k::host_descriptors().collect::<Vec<_>>();
        let first = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.clone(),
            &k::builtin_registry(),
        )
        .expect("KMIR slice lowers");
        let second = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.into_iter().rev(),
            &k::builtin_registry(),
        )
        .expect("KMIR slice lowers twice");
        assert_eq!(
            first.to_canonical_json().unwrap(),
            second.to_canonical_json().unwrap()
        );
        let semantic = lower_descriptor_bundle(&first).expect("KMIR descriptors lower");
        let definition = lower_semantic_theory(&semantic).expect("KMIR theory lowers");
        let source = emit_k(&definition).expect("KMIR definition emits");
        let semantic_json = semantic.to_canonical_json().unwrap();
        let definition_json = definition.definition().to_canonical_json().unwrap();
        assert!(semantic_json.contains(r#""term_kind": "list""#));
        assert!(semantic_json.contains(r#""operation": "get""#));
        assert!(definition_json.contains(r#""term_kind": "list""#));
        assert!(definition_json.contains(r#""operation": "get""#));
        assert!(source.source().contains("imports LIST"));
        assert!(!source.source().contains("<blocks>"));
        assert!(source.source().contains("<locals>"));
        assert!(source.source().contains(" <- "));
        assert!(source.source().contains("typedValue ( Moved , "));
        assert!(source.source().contains("projectionElemField"));
        assert!(source.source().contains("Aggregate"));
        assert!(source.source().contains(r##""#" "execBlockIdx""##));
        assert!(source.source().contains("ListItem("));
        assert!(source.source().contains(".List"));
        assert!(
            source
                .source()
                .contains("{Program:List [ Index:Int ]}:>BasicBlock")
        );
        assert!(source.source().contains("switchInt"));
        assert!(source.source().contains(r##""#" "EndProgram""##));

        let mut invalid_semantic: serde_json::Value = serde_json::from_str(&semantic_json).unwrap();
        assert!(remove_first_list_get_argument(&mut invalid_semantic));
        assert!(serde_json::from_value::<SemanticTheory>(invalid_semantic).is_err());
        let mut invalid_definition: serde_json::Value =
            serde_json::from_str(&definition_json).unwrap();
        assert!(remove_first_list_get_argument(&mut invalid_definition));
        assert!(serde_json::from_value::<DefinitionIr>(invalid_definition).is_err());
    }
}
