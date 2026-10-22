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
pub enum MirAllocId {
    #[k::syntax("allocId({id})")]
    AllocId { id: Int },
}

#[k::constructors(sort = Ty, result = KResult)]
pub enum MirTy {
    #[k::syntax("ty({id})")]
    TyId { id: Int },
}

#[k::constructors(sort = MaybeTy, result = KResult)]
pub enum MirMaybeTy {
    #[k::syntax("TyUnknown")]
    TyUnknown(),
}

#[k::constructors(sort = IntTy, result = KResult)]
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
pub enum MirTyConstId {
    #[k::syntax("tyConstId({id})")]
    TyConstId { id: Int },
}

#[k::constructors(sort = ProvenanceMap, result = KResult)]
pub enum MirProvenanceMap {
    #[k::syntax("provenanceMap(.ProvenanceMapEntries)")]
    EmptyProvenanceMap(),
    #[k::syntax("provenanceMap(provenanceMapEntry({offset}, {allocation}) .ProvenanceMapEntries)")]
    SingletonProvenanceMap { offset: Int, allocation: AllocId },
}

#[k::constructors(sort = Align, result = KResult)]
pub enum MirAlign {
    #[k::syntax("align({bytes})")]
    Align { bytes: Int },
}

#[k::constructors(sort = AdtDef, result = KResult)]
pub enum MirAdtDef {
    #[k::syntax("adtDef({id})")]
    AdtDef { id: Int },
}

#[k::constructors(sort = ClosureDef, result = KResult)]
pub enum MirClosureDef {
    #[k::syntax("closureDef({id})")]
    ClosureDef { id: Int },
}

#[k::constructors(sort = GenericArg, result = KResult)]
pub enum MirGenericArg {
    #[k::syntax("genericArgKindLifetime({region})")]
    GenericArgLifetime { region: Region },
    #[k::syntax("genericArgKindType({ty})")]
    GenericArgType { ty: Ty },
    #[k::syntax("genericArgKindConst({value})")]
    GenericArgConst { value: TyConst },
}

#[k::constructors(sort = GenericArgs, result = KResult)]
#[k::cons_list]
#[k::precedence((GenericArgsEmpty, GenericArgsCons))]
pub enum MirGenericArgs {
    #[k::syntax(".GenericArgs")]
    GenericArgsEmpty(),
    #[k::syntax("{head} {tail}")]
    GenericArgsCons { head: GenericArg, tail: GenericArgs },
}

#[k::constructors(sort = MaybeUserTypeAnnotationIndex, result = KResult)]
pub enum MirMaybeUserTypeAnnotationIndex {
    #[k::syntax("noUserTypeAnnotationIndex")]
    NoUserTypeAnnotationIndex(),
    #[k::syntax("someUserTypeAnnotationIndex(userTypeAnnotationIndex({index}))")]
    SomeUserTypeAnnotationIndex { index: Int },
}

#[k::constructors(sort = MaybeFieldIdx, result = KResult)]
pub enum MirMaybeFieldIdx {
    #[k::syntax("noFieldIdx")]
    NoFieldIdx(),
    #[k::syntax("someFieldIdx(fieldIdx({index}))")]
    SomeFieldIdx { index: Int },
}

#[k::constructors(sort = AggregateKind, result = KResult)]
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
#[k::cons_list]
#[k::precedence((TysEmpty, TysCons))]
pub enum MirTys {
    #[k::syntax(".Tys")]
    TysEmpty(),
    #[k::syntax("{head} {tail}")]
    TysCons { head: Ty, tail: Tys },
}

#[k::constructors(sort = Tyss, result = KResult)]
#[k::cons_list]
#[k::precedence((TyssEmpty, TyssCons))]
pub enum MirTyss {
    #[k::syntax(".Tyss")]
    TyssEmpty(),
    #[k::syntax("{head} : {tail}")]
    TyssCons { head: Tys, tail: Tyss },
}

#[k::constructors(sort = Discriminant, result = KResult)]
pub enum MirDiscriminant {
    #[k::syntax("discriminant({value})")]
    Discriminant { value: Int },
}

#[k::constructors(sort = Discriminants, result = KResult)]
#[k::cons_list]
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
pub enum MirMachineSize {
    #[k::syntax("machineSize({bits})")]
    MachineSize { bits: Int },
}

#[k::constructors(sort = MachineSizes, result = KResult)]
#[k::cons_list]
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
pub enum MirFieldsShapeArbitrary {
    #[k::syntax("mk({offsets})")]
    ArbitraryFields { offsets: MachineSizes },
}

#[k::constructors(sort = FieldsShape, result = KResult)]
pub enum MirFieldsShape {
    #[k::syntax("fieldsShapeArbitrary({fields})")]
    FieldsShapeArbitrary { fields: FieldsShapeArbitrary },
}

#[k::constructors(sort = VariantsShapeSingle, result = KResult)]
pub enum MirVariantsShapeSingle {
    #[k::syntax("mk(variantIdx({index}))")]
    SingleVariant { index: Int },
}

#[k::constructors(sort = LayoutShapes, result = KResult)]
#[k::cons_list]
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
pub enum MirPrimitiveInt {
    #[k::syntax("mk({length}, {signed})")]
    PrimitiveInt { length: IntegerLength, signed: Bool },
}

#[k::constructors(sort = AddressSpace, result = KResult)]
pub enum MirAddressSpace {
    #[k::syntax("addressSpace({id})")]
    AddressSpace { id: Int },
}

#[k::constructors(sort = Primitive, result = KResult)]
pub enum MirPrimitive {
    #[k::syntax("primitiveInt({integer})")]
    IntegerPrimitive { integer: PrimitiveInt },
    #[k::syntax("primitivePointer({address_space})")]
    PointerPrimitive { address_space: AddressSpace },
}

#[k::constructors(sort = WrappingRange, result = KResult)]
pub enum MirWrappingRange {
    #[k::syntax("wrappingRange({start}, {end})")]
    WrappingRange { start: Int, end: Int },
}

#[k::constructors(sort = ScalarInitialized, result = KResult)]
pub enum MirScalarInitialized {
    #[k::syntax("mk({value}, {valid_range})")]
    ScalarInitializedFields {
        value: Primitive,
        valid_range: WrappingRange,
    },
}

#[k::constructors(sort = Scalar, result = KResult)]
pub enum MirScalar {
    #[k::syntax("scalarInitialized({scalar})")]
    InitializedScalar { scalar: ScalarInitialized },
}

#[k::constructors(sort = TagEncoding, result = KResult)]
pub enum MirTagEncoding {
    #[k::syntax("tagEncodingDirect")]
    Direct(),
    #[k::syntax("tagEncodingNiche()")]
    Niche(),
}

#[k::constructors(sort = VariantsShapeMultiple, result = KResult)]
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
pub enum MirVariantsShape {
    #[k::syntax("variantsShapeSingle({variant})")]
    VariantsShapeSingle { variant: VariantsShapeSingle },
    #[k::syntax("variantsShapeMultiple({variants})")]
    VariantsShapeMultiple { variants: VariantsShapeMultiple },
}

#[k::constructors(sort = ValueAbiAggregate, result = KResult)]
pub enum MirValueAbiAggregate {
    #[k::syntax("mk({sized})")]
    AggregateAbi { sized: Bool },
}

#[k::constructors(sort = ValueAbi, result = KResult)]
pub enum MirValueAbi {
    #[k::syntax("valueAbiScalar({scalar})")]
    ValueAbiScalar { scalar: Scalar },
    #[k::syntax("valueAbiAggregate({aggregate})")]
    ValueAbiAggregate { aggregate: ValueAbiAggregate },
}

#[k::constructors(sort = LayoutShape, result = KResult)]
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
pub enum MirMaybeLayoutShape {
    #[k::syntax("someLayoutShape({layout})")]
    SomeLayoutShape { layout: LayoutShape },
    #[k::syntax("noLayoutShape")]
    NoLayoutShape(),
}

#[k::constructors(sort = Allocation, result = KResult)]
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
pub enum MirTyConstKind {
    #[k::syntax("tyConstKindValue({ty}, {allocation})")]
    Value { ty: Ty, allocation: Allocation },
}

#[k::constructors(sort = TyConst, result = KResult)]
pub enum MirTyConst {
    #[k::syntax("tyConst({kind}, {id})")]
    TyConst { kind: TyConstKind, id: TyConstId },
}

#[k::constructors(sort = MaybeTyConst, result = KResult)]
pub enum MirMaybeTyConst {
    #[k::syntax("someTyConst({value})")]
    SomeTyConst { value: TyConst },
    #[k::syntax("noTyConst")]
    NoTyConst(),
}

#[k::constructors(sort = TypeInfo, result = KResult)]
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
pub enum LocalMutability {
    #[k::syntax("mutabilityNot")]
    NotMutable(),
    #[k::syntax("mutabilityMut")]
    Mutable(),
}

#[k::constructors(sort = Region, result = KResult)]
pub enum MirRegion {
    #[k::syntax("region(regionKindReErased)")]
    Erased(),
}

#[k::constructors(sort = BorrowKind, result = KResult)]
pub enum MirBorrowKind {
    #[k::syntax("borrowKindShared")]
    SharedBorrow(),
    #[k::syntax("borrowKindMut(mutBorrowKindDefault)")]
    MutableBorrow(),
}

#[k::constructors(sort = PointerCoercion, result = KResult)]
pub enum MirPointerCoercion {
    #[k::syntax("pointerCoercionUnsize")]
    Unsize(),
}

#[k::constructors(sort = CastKind, result = KResult)]
pub enum MirCastKind {
    #[k::syntax("castKindPointerCoercion({coercion})")]
    PointerCoercion { coercion: PointerCoercion },
    #[k::syntax("castKindPtrToPtr")]
    PtrToPtr(),
    #[k::syntax("castKindTransmute")]
    Transmute(),
}

#[k::constructors(sort = MetadataSize, result = KResult)]
pub enum MirMetadataSize {
    #[k::syntax("noMetadataSize")]
    NoMetadataSize(),
    #[k::syntax("staticSize({size})")]
    StaticSize { size: Int },
    #[k::syntax("dynamicSize({size})")]
    DynamicSize { size: Int },
}

#[k::constructors(sort = Metadata, result = KResult)]
pub enum MirMetadata {
    #[k::syntax("metadata({size}, {offset}, {origin_size})")]
    Metadata {
        size: MetadataSize,
        offset: Int,
        origin_size: MetadataSize,
    },
}

#[k::constructors(sort = TypedLocal, result = KResult)]
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

k::equations! {
    for LocalTy;
    local_ty: LocalValue::NewLocal { ty, .. } | LocalValue::TypedValue { ty, .. } => ty;
}

#[k::function(total, sort = MaybeTy, syntax = "pointeeTy({info})")]
pub struct PointeeTy {
    pub info: k::Term<TypeInfo>,
}

k::equations! {
    for PointeeTy;
    pointee_ty:
        MirTypeInfo::PointerType { pointee } | MirTypeInfo::ReferenceType { pointee } => pointee;
    #[k::equation(priority = 60)]
    pointee_ty_other: _ => MirMaybeTy::TyUnknown();
}

#[k::function(total, sort = MaybeTy, syntax = "elemTy({info})")]
pub struct ElemTy {
    pub info: k::Term<TypeInfo>,
}

k::equations! {
    for ElemTy;
    elem_ty_array: MirTypeInfo::ArrayType { element, .. } => element;
    #[k::equation(priority = 60)]
    elem_ty_other: _                                      => MirMaybeTy::TyUnknown();
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

k::equations! {
    for GetTyOf;
    use MirMaybeTy::*;
    use Projection::*;
    #[k::equation(priority = 40)]
    get_ty_of_unknown: (_, TyUnknown(), _) => TyUnknown();
    get_ty_of_done   : (_, ty, [])         => ty;
    get_ty_of_deref:
        (types, ty, [Deref(), tail @ ..])
        => GetTyOf { types, ty: PointeeTy { info: map::get(types, ty) }, projections: tail };
    get_ty_of_field:
        (types, _, [Field { ty, .. }, tail @ ..]) => GetTyOf { types, ty, projections: tail };
    get_ty_of_element:
        (types, ty, [Index(_) | ConstantIndex(_, _, _), tail @ ..])
        => GetTyOf { types, ty: ElemTy { info: map::get(types, ty) }, projections: tail };
    /// A subslice keeps its array type, and a downcast keeps its enum type.
    get_ty_of_same_type:
        (types, ty, [Subslice(_, _, _) | Downcast(_), tail @ ..])
        => GetTyOf { types, ty, projections: tail };
    #[k::equation(priority = 60)]
    get_ty_of_other  : (_, _, _)           => TyUnknown();
}

#[k::function(total, sort = TypeInfo, syntax = "#lookupMaybeTy({types}, {ty})")]
pub struct LookupMaybeTy {
    pub types: k::Term<Map>,
    pub ty: k::Term<MaybeTy>,
}

/// A known type is looked up in the type map. `ty` is declared `Ty`, not the
/// field's `MaybeTy`: otherwise this equation would also match `TyUnknown`,
/// which is never a key of the map, and would state that the lookup there
/// equals both an undefined map lookup and `lookup_maybe_ty_unknown`'s
/// `typeInfoVoidType`.
#[k::equation]
fn lookup_maybe_ty_known(
    types: k::Term<Map>,
    ty: k::Term<Ty>,
    k::term![LookupMaybeTy { types, ty }]: k::Term<TypeInfo>,
) -> k::Term<TypeInfo> {
    map::get(types, ty)
}

#[k::equation]
fn lookup_maybe_ty_unknown(
    k::term![LookupMaybeTy {
        ty: MirMaybeTy::TyUnknown(),
        ..
    }]: k::Term<TypeInfo>,
) -> k::Term<TypeInfo> {
    MirTypeInfo::VoidType()
}

#[k::function(
    total,
    underspecified = "a trait object's pointer metadata is a vtable, which no MetadataSize describes",
    sort = MetadataSize,
    syntax = "#metadataSizeOf({info})"
)]
pub struct MetadataSizeOf {
    pub info: k::Term<TypeInfo>,
}

#[k::function(
    total,
    underspecified = "every application starts at index 0 or 8 and each step adds 1, so the index is never negative",
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

#[k::function(total, syntax = "#intWidth({kind})")]
pub fn IntWidth(kind: k::Term<IntTy>) -> k::Term<Int>;

#[k::function(total, syntax = "#uintWidth({kind})")]
pub fn UintWidth(kind: k::Term<UintTy>) -> k::Term<Int>;

#[k::function(total, syntax = "#floatWidth({kind})")]
pub fn FloatWidth(kind: k::Term<FloatTy>) -> k::Term<Int>;

#[k::function(total, syntax = "#sizeOf({types}, {info})")]
pub fn SizeOfTypeInfo(types: k::Term<Map>, info: k::Term<TypeInfo>) -> k::Term<Int>;

#[k::function(total, syntax = "#alignOf({types}, {info})")]
pub fn AlignOfTypeInfo(types: k::Term<Map>, info: k::Term<TypeInfo>) -> k::Term<Int>;

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

#[k::function(total, sort = Bool, syntax = "#noFields({fields})")]
pub struct NoFields {
    pub fields: k::Term<Tyss>,
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

#[k::function(total, syntax = "#byteLength({width})")]
pub fn ByteLength(width: k::Term<IntegerLength>) -> k::Term<Int>;

k::equations! {
    for ReadTyConstInt;
    #[k::requires(index >= bytes::length(value))]
    read_ty_const_int_done: (value, index, _, result) => result;
    #[k::requires(index >= 0 && index < bytes::length(value))]
    read_ty_const_int_byte:
        (value, index, multiplier, result) => ReadTyConstInt {
            bytes: value,
            index: index + 1,
            multiplier: multiplier * 256,
            result: result + bytes::get(value, index) * multiplier
        };
}

k::equations! {
    for IntWidth;
    int_width_isize: MirIntTy::Isize() => 64;
    int_width_i8   : MirIntTy::I8()    => 8;
    int_width_i16  : MirIntTy::I16()   => 16;
    int_width_i32  : MirIntTy::I32()   => 32;
    int_width_i64  : MirIntTy::I64()   => 64;
    int_width_i128 : MirIntTy::I128()  => 128;
}

k::equations! {
    for UintWidth;
    uint_width_usize: MirUintTy::Usize() => 64;
    uint_width_u8   : MirUintTy::U8()    => 8;
    uint_width_u16  : MirUintTy::U16()   => 16;
    uint_width_u32  : MirUintTy::U32()   => 32;
    uint_width_u64  : MirUintTy::U64()   => 64;
    uint_width_u128 : MirUintTy::U128()  => 128;
}

k::equations! {
    for FloatWidth;
    float_width_f16 : MirFloatTy::F16()  => 16;
    float_width_f32 : MirFloatTy::F32()  => 32;
    float_width_f64 : MirFloatTy::F64()  => 64;
    float_width_f128: MirFloatTy::F128() => 128;
}

k::equations! {
    for LayoutSize;
    layout_size_known:
        MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape { size: MirMachineSize::MachineSize { bits }, .. }
        } => bits / 8;
    layout_size_unknown: MirMaybeLayoutShape::NoLayoutShape() => 0;
}

k::equations! {
    for LayoutAlign;
    layout_align_known:
        MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape { abi_align: MirAlign::Align { bytes }, .. }
        } => bytes;
    layout_align_unknown: MirMaybeLayoutShape::NoLayoutShape() => 1;
}

k::equations! {
    for PointerWords;
    /// A pointer to a slice or to `str` carries its length beside the address.
    pointer_words_unsized:
        MirTypeInfo::ArrayType { size: MirMaybeTyConst::NoTyConst(), .. }
        | MirTypeInfo::PrimitiveType { primitive: MirPrimitiveType::Str() } => 2;
    #[k::equation(priority = 60)]
    pointer_words_thin: _ => 1;
}

k::equations! {
    for IsVoidType;
    is_void_type    : MirTypeInfo::VoidType() => true;
    #[k::equation(priority = 60)]
    is_not_void_type: _                       => false;
}

k::equations! {
    for SizeOfTypeInfo;
    size_of_boolean      : (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Bool()))    => 1;
    size_of_char         : (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Char()))    => 4;
    size_of_signed_integer:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::SignedInteger(kind)))
        => IntWidth(kind) / 8;
    size_of_unsigned_integer:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::UnsignedInteger(kind)))
        => UintWidth(kind) / 8;
    size_of_float:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Float(kind))) => FloatWidth(kind) / 8;
    size_of_str          : (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Str()))     => 0;
    size_of_aggregate:
        (
            _,
            MirTypeInfo::EnumType(_, _, _, _, layout)
            | MirTypeInfo::StructType(_, _, _, layout)
            | MirTypeInfo::UnionType(_, _, _, layout)
            | MirTypeInfo::TupleType(_, layout)
        ) => LayoutSize(layout);
    size_of_dynamic_array: (_, MirTypeInfo::ArrayType(_, MirMaybeTyConst::NoTyConst())) => 0;
    size_of_static_array:
        (
            types,
            MirTypeInfo::ArrayType(
                element,
                MirMaybeTyConst::SomeTyConst(
                    MirTyConst::TyConst(
                        MirTyConstKind::Value(_, MirAllocation::Allocation(bytes, _, _, _)),
                        _
                    )
                )
            )
        ) => SizeOfTypeInfo(types, map::get(types, element)) * ReadTyConstInt(bytes, 0, 1, 0);
    size_of_pointer:
        (types, MirTypeInfo::PointerType(pointee) | MirTypeInfo::ReferenceType(pointee))
        => SizeOfTypeInfo(
            types,
            MirTypeInfo::PrimitiveType(MirPrimitiveType::UnsignedInteger(MirUintTy::Usize()))
        ) * PointerWords(map::get(types, pointee));
    #[k::equation(priority = 60)]
    size_of_other        : (_, _)                                                       => 0;
}

k::equations! {
    for AlignOfTypeInfo;
    align_of_boolean: (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Bool())) => 1;
    align_of_char   : (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Char())) => 4;
    align_of_signed_integer:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::SignedInteger(kind)))
        => IntWidth(kind) / 8;
    align_of_unsigned_integer:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::UnsignedInteger(kind)))
        => UintWidth(kind) / 8;
    align_of_float:
        (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Float(kind))) => FloatWidth(kind) / 8;
    align_of_str    : (_, MirTypeInfo::PrimitiveType(MirPrimitiveType::Str()))  => 1;
    align_of_aggregate:
        (
            _,
            MirTypeInfo::EnumType(_, _, _, _, layout)
            | MirTypeInfo::StructType(_, _, _, layout)
            | MirTypeInfo::UnionType(_, _, _, layout)
            | MirTypeInfo::TupleType(_, layout)
        ) => LayoutAlign(layout);
    align_of_array:
        (types, MirTypeInfo::ArrayType(element, _))
        => AlignOfTypeInfo(types, map::get(types, element));
    align_of_pointer:
        (types, MirTypeInfo::PointerType(_) | MirTypeInfo::ReferenceType(_)) => AlignOfTypeInfo(
            types,
            MirTypeInfo::PrimitiveType(MirPrimitiveType::UnsignedInteger(MirUintTy::Usize()))
        );
    #[k::equation(priority = 60)]
    align_of_other  : (_, _)                                                    => 0;
}

#[k::function(partial, syntax = "#decodeInteger({bytes}, {width}, {signed})")]
#[k::requires(bytes::length(bytes) == width / 8)]
pub fn DecodeInteger(
    bytes: k::Term<Bytes>,
    width: k::Term<Int>,
    signed: k::Term<Bool>,
) -> k::Term<MirValue> {
    Value::Integer {
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
    }
}

k::equations! {
    for DecodeAllocatedValue;
    use MirFieldsShape::*;
    use MirFieldsShapeArbitrary::*;
    use MirLayoutShape::*;
    use MirMaybeLayoutShape::*;
    use MirPrimitiveType::*;
    use MirTypeInfo::*;
    use Value::*;
    #[k::requires(
        bytes::length(bytes) == 1 && ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 } == 0
    )]
    decode_allocated_boolean_false:
        (_, bytes, PrimitiveType { primitive: Bool() }) => Boolean(false);
    #[k::requires(
        bytes::length(bytes) == 1 && ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 } == 1
    )]
    decode_allocated_boolean_true: (_, bytes, PrimitiveType { primitive: Bool() }) => Boolean(true);
    decode_allocated_signed_integer:
        (_, bytes, PrimitiveType { primitive: SignedInteger { kind } })
        => DecodeInteger { bytes, width: IntWidth { kind }, signed: true };
    decode_allocated_unsigned_integer:
        (_, bytes, PrimitiveType { primitive: UnsignedInteger { kind } })
        => DecodeInteger { bytes, width: UintWidth { kind }, signed: false };
    #[k::requires(NoFields { fields } == false)]
    decode_allocated_direct_enum:
        (
            types,
            bytes,
            EnumType {
                discriminants,
                fields,
                layout: SomeLayoutShape {
                    layout: LayoutShape {
                        variants: MirVariantsShape::VariantsShapeMultiple {
                            variants: MirVariantsShapeMultiple::MultipleVariants {
                                tag: MirScalar::InitializedScalar {
                                    scalar: MirScalarInitialized::ScalarInitializedFields {
                                        value: MirPrimitive::IntegerPrimitive {
                                            integer: MirPrimitiveInt::PrimitiveInt { length, .. }
                                        },
                                        ..
                                    }
                                },
                                tag_encoding: MirTagEncoding::Direct(),
                                tag_field: 0,
                                variants: layouts
                            }
                        },
                        ..
                    }
                },
                ..
            }
        ) => DecodeEnumDirectFields {
            types,
            bytes,
            index: FindVariantIndex {
                tag: DecodeEnumDirectTag { bytes, width: length },
                discriminants
            },
            fields,
            layouts
        };
    #[k::requires(ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 } == 0)]
    decode_allocated_niche_pointer_none:
        (
            _,
            bytes,
            EnumType {
                discriminants: [
                    MirDiscriminant::Discriminant { value: 0 },
                    MirDiscriminant::Discriminant { value: 1 }
                ],
                fields: [[], [_]],
                layout: SomeLayoutShape {
                    layout: LayoutShape {
                        fields: FieldsShapeArbitrary {
                            fields: ArbitraryFields {
                                offsets: [MirMachineSize::MachineSize { bits: 0 }]
                            }
                        },
                        variants: MirVariantsShape::VariantsShapeMultiple {
                            variants: MirVariantsShapeMultiple::MultipleVariants {
                                tag: MirScalar::InitializedScalar {
                                    scalar: MirScalarInitialized::ScalarInitializedFields {
                                        value: MirPrimitive::PointerPrimitive(_),
                                        valid_range: MirWrappingRange::WrappingRange {
                                            start: 1,
                                            end: 0
                                        }
                                    }
                                },
                                tag_encoding: MirTagEncoding::Niche(),
                                tag_field: 0,
                                ..
                            }
                        },
                        ..
                    }
                },
                ..
            }
        ) => Aggregate { variant: 0, fields: list::empty() };
    decode_allocated_static_array:
        (
            types,
            bytes,
            ArrayType {
                element,
                size: MirMaybeTyConst::SomeTyConst {
                    value: MirTyConst::TyConst {
                        kind: MirTyConstKind::Value {
                            allocation: MirAllocation::Allocation { bytes: length_bytes, .. },
                            ..
                        },
                        ..
                    }
                }
            }
        ) => DecodeArrayAllocation {
            types,
            bytes,
            info: map::get(types, element),
            length: ReadTyConstInt { bytes: length_bytes, index: 0, multiplier: 1, result: 0 }
        };
    decode_allocated_slice:
        (types, bytes, ArrayType { element, size: MirMaybeTyConst::NoTyConst() })
        => DecodeSliceAllocation { types, bytes, info: map::get(types, element) };
    #[k::requires(
        NeededBytesForOffsets { types, fields, offsets } >= 0
            && bytes::length(bytes) >= NeededBytesForOffsets { types, fields, offsets }
    )]
    decode_allocated_struct:
        (
            types,
            bytes,
            StructType {
                fields,
                layout: SomeLayoutShape {
                    layout: LayoutShape {
                        fields: FieldsShapeArbitrary { fields: ArbitraryFields { offsets } },
                        ..
                    }
                },
                ..
            }
        ) => Aggregate {
            variant: 0,
            fields: DecodeFieldsWithOffsets { types, bytes, fields, offsets }
        };
    #[k::requires(bytes::length(bytes) == 0)]
    decode_allocated_empty_tuple:
        (_, bytes, TupleType { fields: [], .. }) => Aggregate { variant: 0, fields: list::empty() };
    #[k::requires(
        NeededBytesForOffsets { types, fields: [first, ..remaining], offsets } >= 0
            && bytes::length(bytes) >= NeededBytesForOffsets { types, fields: [first, ..remaining], offsets }
    )]
    decode_allocated_tuple:
        (
            types,
            bytes,
            TupleType {
                fields: [first, remaining @ ..],
                layout: SomeLayoutShape {
                    layout: LayoutShape {
                        fields: FieldsShapeArbitrary { fields: ArbitraryFields { offsets } },
                        ..
                    }
                }
            }
        ) => Aggregate {
            variant: 0,
            fields: DecodeFieldsWithOffsets { types, bytes, fields: [first, ..remaining], offsets }
        };
    #[k::requires(NoFields { fields } == true)]
    decode_allocated_fieldless_enum:
        (_, bytes, EnumType { discriminants, fields, .. }) => Aggregate {
            variant: FindVariantIndex {
                tag: ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 },
                discriminants
            },
            fields: list::empty()
        };
}

k::equations! {
    for NoFields;
    no_fields_empty           : []              => true;
    no_fields_empty_variant   : [[], tail @ ..] => NoFields { fields: tail };
    no_fields_nonempty_variant: [[_, ..], ..]   => false;
}

#[k::function(partial, syntax = "#findVariantIdx({tag}, {discriminants})")]
pub fn FindVariantIndex(tag: k::Term<Int>, discriminants: k::Term<Discriminants>) -> k::Term<Int> {
    FindVariantIndexAux {
        tag,
        discriminants,
        index: 0,
    }
}

k::equations! {
    for FindVariantIndexAux;
    #[k::requires(tag == discriminant)]
    find_variant_index_match:
        (tag, [MirDiscriminant::Discriminant { value: discriminant }, ..], index) => index;
    #[k::requires(tag != discriminant)]
    find_variant_index_continue:
        (tag, [MirDiscriminant::Discriminant { value: discriminant }, tail @ ..], index)
        => FindVariantIndexAux { tag, discriminants: tail, index: index + 1 };
}

k::equations! {
    for LookupDiscriminant;
    #[k::requires(index == 0)]
    lookup_discriminant_head: ([MirDiscriminant::Discriminant { value }, ..], index) => value;
    #[k::requires(index > 0)]
    lookup_discriminant_tail:
        ([_, tail @ ..], index) => LookupDiscriminant { discriminants: tail, index: index - 1 };
}

#[k::function(
    partial,
    syntax = "#decodeEnumDirectFields({types}, {bytes}, {index}, {fields}, {layouts})"
)]
#[k::requires(index >= 0)]
pub fn DecodeEnumDirectFields(
    types: k::Term<Map>,
    bytes: k::Term<Bytes>,
    index: k::Term<Int>,
    fields: k::Term<Tyss>,
    layouts: k::Term<LayoutShapes>,
) -> k::Term<MirValue> {
    Value::Aggregate {
        variant: index,
        fields: DecodeFieldsWithOffsets {
            types,
            bytes,
            fields: NthTys { fields, index },
            offsets: NthVariantOffsets { layouts, index },
        },
    }
}

#[k::function(partial, syntax = "#decodeEnumDirectTag({bytes}, {width})")]
#[k::requires(bytes::length(bytes) >= ByteLength { width })]
pub fn DecodeEnumDirectTag(bytes: k::Term<Bytes>, width: k::Term<IntegerLength>) -> k::Term<Int> {
    ReadTyConstInt {
        bytes: bytes::substr(bytes, 0, ByteLength { width }),
        index: 0,
        multiplier: 1,
        result: 0,
    }
}

k::equations! {
    for NthTys;
    nth_tys_first: ([head, ..], 0)         => head;
    #[k::requires(index > 0)]
    nth_tys_next : ([_, tail @ ..], index) => NthTys { fields: tail, index: index - 1 };
}

k::equations! {
    for NthVariantOffsets;
    nth_variant_offsets_first:
        (
            [
                MirLayoutShape::LayoutShape {
                    fields: MirFieldsShape::FieldsShapeArbitrary {
                        fields: MirFieldsShapeArbitrary::ArbitraryFields { offsets }
                    },
                    ..
                },
                ..
            ],
            0
        ) => offsets;
    #[k::requires(index > 0)]
    nth_variant_offsets_next:
        ([_, tail @ ..], index) => NthVariantOffsets { layouts: tail, index: index - 1 };
}

k::equations! {
    for ByteLength;
    byte_length_i8  : MirIntegerLength::LengthI8()   => 1;
    byte_length_i16 : MirIntegerLength::LengthI16()  => 2;
    byte_length_i32 : MirIntegerLength::LengthI32()  => 4;
    byte_length_i64 : MirIntegerLength::LengthI64()  => 8;
    byte_length_i128: MirIntegerLength::LengthI128() => 16;
}

k::equations! {
    for ElementSize;
    use MirMaybeLayoutShape::*;
    use MirPrimitiveType::*;
    use MirTypeInfo::*;
    element_size_boolean    : (_, PrimitiveType { primitive: Bool() })               => 1;
    element_size_signed_integer:
        (_, PrimitiveType { primitive: SignedInteger { kind } }) => IntWidth { kind } / 8;
    element_size_unsigned_integer:
        (_, PrimitiveType { primitive: UnsignedInteger { kind } }) => UintWidth { kind } / 8;
    element_size_struct:
        (
            _,
            StructType {
                layout: SomeLayoutShape {
                    layout: MirLayoutShape::LayoutShape {
                        size: MirMachineSize::MachineSize { bits },
                        ..
                    }
                },
                ..
            }
        ) => bits / 8;
    element_size_tuple_layout:
        (
            _,
            TupleType {
                layout: SomeLayoutShape {
                    layout: MirLayoutShape::LayoutShape {
                        size: MirMachineSize::MachineSize { bits },
                        ..
                    }
                },
                ..
            }
        ) => bits / 8;
    element_size_empty_tuple: (_, TupleType { fields: [], layout: NoLayoutShape() }) => 0;
    element_size_static_array:
        (
            types,
            ArrayType {
                element,
                size: MirMaybeTyConst::SomeTyConst {
                    value: MirTyConst::TyConst {
                        kind: MirTyConstKind::Value {
                            allocation: MirAllocation::Allocation { bytes, .. },
                            ..
                        },
                        ..
                    }
                }
            }
        ) => ElementSize { types, info: map::get(types, element) } * ReadTyConstInt {
            bytes,
            index: 0,
            multiplier: 1,
            result: 0
        };
}

k::equations! {
    for Maximum;
    #[k::requires(first >= second)]
    maximum_first : (first, second) => first;
    #[k::requires(first < second)]
    maximum_second: (first, second) => second;
}

k::equations! {
    for NeededBytesForOffsets;
    needed_bytes_for_offsets_done: (_, [], []) => 0;
    needed_bytes_for_offsets_cons:
        (types, [field, fields @ ..], [MirMachineSize::MachineSize { bits }, offsets @ ..])
        => Maximum {
            first: bits / 8 + ElementSize { types, info: map::get(types, field) },
            second: NeededBytesForOffsets { types, fields, offsets }
        };
}

k::equations! {
    for DecodeFieldsWithOffsets;
    decode_fields_with_offsets_done: (_, _, [], []) => list::empty();
    #[k::requires(
        bytes::length(bytes) >= bits / 8 + ElementSize { types, info: map::get(types, field) }
    )]
    decode_fields_with_offsets_cons:
        (types, bytes, [field, fields @ ..], [MirMachineSize::MachineSize { bits }, offsets @ ..])
        => list::concat(
            list::item(
                DecodeAllocatedValue {
                    bytes: bytes::substr(
                        bytes,
                        bits / 8,
                        bits / 8 + ElementSize { types, info: map::get(types, field) }
                    ),
                    info: map::get(types, field),
                    types
                }
            ),
            DecodeFieldsWithOffsets { types, bytes, fields, offsets }
        );
}

#[k::function(
    partial,
    syntax = "#decodeArrayAllocation({types}, {bytes}, {info}, {length})"
)]
pub fn DecodeArrayAllocation(
    types: k::Term<Map>,
    bytes: k::Term<Bytes>,
    info: k::Term<TypeInfo>,
    length: k::Term<Int>,
) -> k::Term<MirValue> {
    Value::Range {
        elements: DecodeArrayElements {
            types,
            bytes,
            info,
            remaining: length,
            accumulated: list::empty(),
        },
    }
}

k::equations! {
    for DecodeArrayElements;
    #[k::requires(bool::and(
        remaining > 0,
        ElementSize { types, info } > 0 && bytes::length(bytes) >= ElementSize { types, info },
    ))]
    decode_array_elements_cons:
        (types, bytes, info, remaining, accumulated) => DecodeArrayElements {
            types,
            bytes: bytes::substr(bytes, ElementSize { types, info }, bytes::length(bytes)),
            info,
            remaining: remaining - 1,
            accumulated: list::concat(
                accumulated,
                list::item(
                    DecodeAllocatedValue {
                        bytes: bytes::substr(bytes, 0, ElementSize { types, info }),
                        info,
                        types
                    }
                )
            )
        };
    #[k::requires(remaining <= 0 && bytes::length(bytes) == 0)]
    decode_array_elements_done: (_, bytes, _, remaining, accumulated) => accumulated;
}

#[k::function(partial, syntax = "#decodeSliceAllocation({types}, {bytes}, {info})")]
#[k::requires(
    ElementSize { types, info } > 0
        && int::rem_euclid(bytes::length(bytes), ElementSize { types, info }) == 0
)]
pub fn DecodeSliceAllocation(
    types: k::Term<Map>,
    bytes: k::Term<Bytes>,
    info: k::Term<TypeInfo>,
) -> k::Term<MirValue> {
    DecodeArrayAllocation {
        types,
        bytes,
        info,
        length: bytes::length(bytes) / ElementSize { types, info },
    }
}

k::equations! {
    for DecodeZeroSizedConstant;
    use MirTypeInfo::*;
    decode_zero_sized_aggregate:
        StructType(_, _, _, _) | TupleType(_, _) | FunType(_)
        => Value::Aggregate { variant: 0, fields: list::empty() };
    decode_zero_sized_array: ArrayType(_, _) => Value::Range { elements: list::empty() };
}

k::equations! {
    for DecodeAllocatedReference;
    #[k::requires(bytes::length(bytes) == 8)]
    decode_allocated_reference_thin:
        (allocation, bytes, _, MirTypeInfo::ReferenceType { pointee }, types)
        => Value::AllocationReference {
            allocation,
            projections: [],
            metadata: MirMetadata::Metadata {
                size: MetadataSizeOf { info: map::get(types, pointee) },
                offset: 0,
                origin_size: MetadataSizeOf { info: map::get(types, pointee) }
            }
        };
    #[k::requires(bytes::length(bytes) == 16)]
    decode_allocated_reference_fat:
        (allocation, bytes, _, MirTypeInfo::ReferenceType(_), _) => Value::AllocationReference {
            allocation,
            projections: [],
            metadata: MirMetadata::Metadata {
                size: MirMetadataSize::DynamicSize(
                    ReadTyConstInt { bytes, index: 8, multiplier: 1, result: 0 }
                ),
                offset: 0,
                origin_size: MirMetadataSize::DynamicSize(
                    ReadTyConstInt { bytes, index: 8, multiplier: 1, result: 0 }
                )
            }
        };
}

k::equations! {
    for MetadataSizeOf;
    use MirMetadataSize::*;
    use MirPrimitiveType::*;
    use MirTypeInfo::*;
    /// A pointer to any of these types carries no size metadata.
    metadata_size_of_thin:
        PrimitiveType {
            primitive: Bool() | Char() | SignedInteger(_) | UnsignedInteger(_) | Float(_)
        }
        | PointerType(_)
        | ReferenceType(_)
        | StructType(_, _, _, _)
        | UnionType(_, _, _, _)
        | TupleType(_, _)
        | EnumType(_, _, _, _, _)
        | FunType(_)
        | VoidType() => NoMetadataSize();
    /// `str` is a sequence of UTF-8 bytes laid out as `[u8]`, so a pointer to
    /// either carries the number of elements, which for `str` is its byte length.
    metadata_size_of_unsized:
        ArrayType { size: MirMaybeTyConst::NoTyConst(), .. } | PrimitiveType { primitive: Str() }
        => DynamicSize(1);
    metadata_size_of_static_array:
        ArrayType {
            size: MirMaybeTyConst::SomeTyConst {
                value: MirTyConst::TyConst {
                    kind: MirTyConstKind::Value {
                        allocation: MirAllocation::Allocation { bytes: value, .. },
                        ..
                    },
                    ..
                }
            },
            ..
        } => StaticSize(ReadTyConstInt { bytes: value, index: 0, multiplier: 1, result: 0 });
}

#[k::function(partial, sort = Bool, syntax = "#sameTypeInfo({first}, {second})")]
pub struct SameTypeInfo {
    pub first: k::Term<TypeInfo>,
    pub second: k::Term<TypeInfo>,
}

k::equations! {
    for SameTypeInfo;
    same_type_info: (info, info) => true;
}

#[k::function(
    partial,
    sort = Bool,
    syntax = "#zeroFieldOffset({layout})"
)]
pub struct ZeroFieldOffset {
    pub layout: k::Term<MaybeLayoutShape>,
}

k::equations! {
    for ZeroFieldOffset;
    zero_field_offset:
        MirMaybeLayoutShape::SomeLayoutShape {
            layout: MirLayoutShape::LayoutShape {
                fields: MirFieldsShape::FieldsShapeArbitrary {
                    fields: MirFieldsShapeArbitrary::ArbitraryFields {
                        offsets: [MirMachineSize::MachineSize { bits: 0 }]
                    }
                },
                ..
            }
        } => true;
}

#[k::function(total, sort = Metadata, syntax = "#convertPointerMetadata({metadata}, {target_size})")]
pub struct ConvertPointerMetadata {
    pub metadata: k::Term<Metadata>,
    pub target_size: k::Term<MetadataSize>,
}

k::equations! {
    for ConvertPointerMetadata;
    use MirMetadata::*;
    use MirMetadataSize::*;
    #[k::equation(priority = 40)]
    convert_pointer_metadata_thin:
        (Metadata { size, offset, .. }, NoMetadataSize())
        => Metadata { size: NoMetadataSize(), offset, origin_size: size };
    convert_pointer_metadata_thin_to_sized:
        (
            Metadata { size: NoMetadataSize(), offset, origin_size },
            target_size @ (DynamicSize(_) | StaticSize(_))
        ) => Metadata { size: target_size, offset, origin_size };
    convert_pointer_metadata_static_to_dynamic:
        (Metadata { size: StaticSize(size), offset, .. }, DynamicSize(_))
        => Metadata { size: DynamicSize(size), offset, origin_size: StaticSize(size) };
    convert_pointer_metadata_dynamic_to_dynamic:
        (Metadata { size: DynamicSize(size), offset, .. }, DynamicSize(_))
        => Metadata { size: DynamicSize(size), offset, origin_size: DynamicSize(size) };
    convert_pointer_metadata_static_to_static:
        (Metadata { size: StaticSize(origin), offset, .. }, StaticSize(size))
        => Metadata { size: StaticSize(size), offset, origin_size: StaticSize(origin) };
    convert_pointer_metadata_dynamic_to_static:
        (Metadata { size: DynamicSize(origin), offset, .. }, StaticSize(size))
        => Metadata { size: StaticSize(size), offset, origin_size: DynamicSize(origin) };
}

#[k::constructors(sort = ProjectionElem, result = KResult)]
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
#[k::cons_list]
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

k::equations! {
    for RemoveIndexTail;
    remove_index_tail_empty: []                                            => [];
    #[k::equation(priority = 40)]
    remove_index_tail_zero : [Projection::ConstantIndex { offset: 0, .. }] => [];
    remove_index_tail_cons: [head, tail @ ..] => [head, ..RemoveIndexTail { projections: tail }];
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

k::equations! {
    for ProjectionMetadataSize;
    use Projection::*;
    projection_metadata_size_done: (ty, [], types) => MetadataSizeOf { info: map::get(types, ty) };
    projection_metadata_size_field:
        (_, [Field { ty, .. }, tail @ ..], types)
        => ProjectionMetadataSize { ty, projections: tail, types };
    projection_metadata_size_element:
        (ty, [Index(_) | ConstantIndex(_, _, _), tail @ ..], types) => ProjectionMetadataSize {
            ty: ArrayElementType { info: map::get(types, ty) },
            projections: tail,
            types
        };
    projection_metadata_size_reference_deref:
        (ty, [Deref(), tail @ ..], types) => ProjectionMetadataSize {
            ty: ReferencePointeeType { info: map::get(types, ty) },
            projections: tail,
            types
        };
}

#[k::function(partial, sort = Ty, syntax = "#arrayElementType({info})")]
pub struct ArrayElementType {
    pub info: k::Term<TypeInfo>,
}

k::equations! {
    for ArrayElementType;
    array_element_type: MirTypeInfo::ArrayType { element, .. } => element;
}

#[k::function(partial, sort = Ty, syntax = "#referencePointeeType({info})")]
pub struct ReferencePointeeType {
    pub info: k::Term<TypeInfo>,
}

k::equations! {
    for ReferencePointeeType;
    reference_pointee_type:
        MirTypeInfo::ReferenceType { pointee } | MirTypeInfo::PointerType { pointee } => pointee;
}

#[k::function(total, sort = MetadataSize, syntax = "#maybeDynamicSize({size}, {value})")]
pub struct MaybeDynamicSize {
    pub size: k::Term<MetadataSize>,
    pub value: k::Term<MirValue>,
}

k::equations! {
    for MaybeDynamicSize;
    use MirMetadataSize::*;
    #[k::equation(priority = 40)]
    maybe_dynamic_size_range:
        (DynamicSize(_), Value::Range { elements }) => DynamicSize(list::size(elements));
    maybe_dynamic_size_non_range: (DynamicSize(_), _) => NoMetadataSize();
    #[k::equation(priority = 60)]
    maybe_dynamic_size_other    : (size, _)           => size;
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

k::equations! {
    for ProjectionsFor;
    use MirProjectionContext::*;
    use Projection::*;
    projections_for_done: ([], projections) => projections;
    projections_for_field:
        (
            [FieldContext { field, ty, .. } | UnionFieldContext { field, ty, .. }, tail @ ..],
            projections
        ) => ProjectionsFor { contexts: tail, projections: [Field { field, ty }, ..projections] };
    projections_for_index:
        ([IndexContext { index, .. }, tail @ ..], projections) => ProjectionsFor {
            contexts: tail,
            projections: [
                ConstantIndex { offset: index, min_length: 0, from_end: false },
                ..projections
            ]
        };
    projections_for_subslice:
        ([SubsliceContext { start, from_back, .. }, tail @ ..], projections) => ProjectionsFor {
            contexts: tail,
            projections: [Subslice { from: start, to: from_back, from_end: false }, ..projections]
        };
    projections_for_pointer_offset:
        ([PointerOffsetContext { offset, origin_size, .. }, tail @ ..], projections)
        => ProjectionsFor {
            contexts: tail,
            projections: [PointerOffset { offset, origin_size }, ..projections]
        };
    projections_for_wrap_struct:
        ([WrapStructContext(), tail @ ..], projections)
        => ProjectionsFor { contexts: tail, projections: [WrapStruct(), ..projections] };
}

#[k::constructors(sort = ProjectionTarget, result = KResult)]
pub enum MirProjectionTarget {
    #[k::syntax("toLocal(local({local}))")]
    ToLocal { local: Int },
    #[k::syntax("toStack({height}, local({local}))")]
    ToStack { height: Int, local: Int },
    #[k::syntax("toAlloc({allocation})")]
    ToAllocation { allocation: AllocId },
}

#[k::constructors(sort = ProjectionContext, result = KResult)]
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
#[k::cons_list]
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
pub enum MirPtrCastPhase {
    #[k::syntax("ptrCastCompare")]
    Compare(),
    #[k::syntax("ptrCastSource")]
    Source(),
    #[k::syntax("ptrCastTarget")]
    TargetPhase(),
}

#[k::constructors(sort = Place, result = KResult)]
pub enum MirPlace {
    #[k::syntax("place(local({local}), {projections})")]
    Place {
        local: Int,
        projections: ProjectionElems,
    },
}

#[k::constructors(sort = MirValue, result = KResult)]
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

k::equations! {
    for MaterializeAggregate;
    use MirAggregateKind::*;
    use MirMetadata::*;
    use Value::*;
    materialize_adt:
        (AggregateAdt { variant, field: MirMaybeFieldIdx::NoFieldIdx(), .. }, values)
        => Aggregate { variant, fields: values };
    materialize_union:
        (
            AggregateAdt { field: MirMaybeFieldIdx::SomeFieldIdx { index: field }, .. },
            list::concat(list::item(value), list::empty())
        ) => Union { field, value };
    materialize_fat_raw_pointer:
        (
            AggregateRawPointer { mutability, .. },
            list::concat(
                list::item(
                    Pointer {
                        height,
                        place: MirPlace::Place { local, projections },
                        metadata: Metadata { offset, origin_size, .. },
                        ..
                    }
                ),
                list::concat(
                    list::item(Integer { value: length, width: 64, signed: false }),
                    list::empty()
                )
            )
        ) => Pointer {
            height,
            place: MirPlace::Place { local, projections: RemoveIndexTail { projections } },
            mutability,
            metadata: Metadata { size: MirMetadataSize::DynamicSize(length), offset, origin_size }
        };
    materialize_thin_raw_pointer:
        (
            AggregateRawPointer { mutability, .. },
            list::concat(
                list::item(
                    Pointer { height, place, metadata: Metadata { offset, origin_size, .. }, .. }
                ),
                list::concat(list::item(Aggregate { fields: list::empty(), .. }), list::empty())
            )
        ) => Pointer {
            height,
            place,
            mutability,
            metadata: Metadata { size: MirMetadataSize::NoMetadataSize(), offset, origin_size }
        };
    materialize_array: (AggregateArray(_), values) => Range { elements: values };
    materialize_tuple:
        (AggregateTuple() | AggregateClosure(_, _), values)
        => Aggregate { variant: 0, fields: values };
}

#[k::constructors(sort = BinaryOp, result = KResult)]
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
pub enum MirUnaryOp {
    #[k::syntax("unOpNot")]
    UnOpNot(),
    #[k::syntax("unOpNeg")]
    UnOpNeg(),
    #[k::syntax("unOpPtrMetadata")]
    UnOpPtrMetadata(),
}

#[k::constructors(sort = NullOp, result = KResult)]
pub enum MirNullOp {
    #[k::syntax("nullOpSizeOf")]
    SizeOf(),
    #[k::syntax("nullOpAlignOf")]
    AlignOf(),
    #[k::syntax("nullOpUbChecks")]
    UbChecks(),
}

#[k::constructors(sort = Rvalue, result = KResult)]
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
pub enum MirStatement {
    #[k::syntax("assign({place}, {value})")]
    Assign { place: Place, value: Rvalue },
}

#[k::constructors(sort = Statements, result = KResult)]
#[k::cons_list]
#[k::precedence((StatementsEmpty, StatementsCons))]
pub enum StatementList {
    #[k::syntax(".Statements")]
    StatementsEmpty(),
    #[k::syntax("{head} ; {tail}")]
    StatementsCons { head: Statement, tail: Statements },
}

#[k::constructors(sort = Branch, result = KResult)]
pub enum MirBranch {
    #[k::syntax("branch({value}, {target})")]
    Branch { value: Int, target: Int },
}

#[k::constructors(sort = Branches, result = KResult)]
#[k::cons_list]
#[k::precedence((BranchesEmpty, BranchesCons))]
pub enum BranchList {
    #[k::syntax(".Branches")]
    BranchesEmpty(),
    #[k::syntax("{head} {tail}")]
    BranchesCons { head: Branch, tail: Branches },
}

#[k::constructors(sort = SwitchTargets, result = KResult)]
pub enum MirSwitchTargets {
    #[k::syntax("switchTargets({branches}, {otherwise})")]
    SwitchTargets { branches: Branches, otherwise: Int },
}

#[k::constructors(sort = MaybeBasicBlockIdx, result = KResult)]
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
pub enum MirLocalDecl {
    #[k::syntax("localDecl({ty}, span({span}), {mutability})")]
    LocalDecl {
        ty: Ty,
        span: Int,
        mutability: Mutability,
    },
}

#[k::constructors(sort = LocalDecls, result = KResult)]
#[k::cons_list]
#[k::precedence((LocalDeclsEmpty, LocalDeclsCons))]
pub enum MirLocalDecls {
    #[k::syntax(".LocalDecls")]
    LocalDeclsEmpty(),
    #[k::syntax("{head} {tail}")]
    LocalDeclsCons { head: LocalDecl, tail: LocalDecls },
}

#[k::constructors(sort = FunctionBody, result = KResult)]
pub enum MirFunctionBody {
    #[k::syntax("body({blocks}, {locals}, {arg_count})")]
    Body {
        blocks: List,
        locals: LocalDecls,
        arg_count: Int,
    },
}

#[k::constructors(sort = Function, result = KResult)]
pub enum MirFunction {
    #[k::syntax("monoItemFn(defId({id}), someBody({body}))")]
    MonoItemFn { id: Int, body: FunctionBody },
}

#[k::constructors(sort = CallTarget, result = KResult)]
pub enum MirCallTarget {
    #[k::syntax(
        "operandConstant(constOperand(span({span}), mirConst(constantKindZeroSized, {ty}, mirConstId({id}))))"
    )]
    ConstantFunction { span: Int, ty: Ty, id: Int },
}

#[k::constructors(sort = StackFrame, result = KResult)]
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
pub enum MirAssertMessage {
    #[k::syntax("assertMessageOverflow({operation}, {lhs}, {rhs})")]
    Overflow {
        operation: BinaryOp,
        lhs: Operand,
        rhs: Operand,
    },
}

#[k::constructors(sort = UnwindAction, result = KResult)]
pub enum MirUnwindAction {
    #[k::syntax("unwindActionContinue")]
    UnwindContinue(),
}

#[k::constructors(sort = MirError, result = k::KItem)]
pub enum MirExecutionError {
    #[k::syntax("AssertError({message})")]
    AssertError { message: AssertMessage },
    #[k::syntax("ReachedUnreachable")]
    ReachedUnreachable(),
}

#[k::constructors(sort = Terminator, result = KResult)]
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
pub enum BlockSyntax {
    #[k::syntax("basicBlock({statements}, {terminator})")]
    Block {
        statements: Statements,
        terminator: Terminator,
    },
}

#[k::constructors(sort = RetVal, result = KResult)]
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

k::equations! {
    for TruncateUnsigned;
    #[k::requires(width <= 0)]
    truncate_unsigned_nonpositive: (value, width) => value;
    #[k::requires(width > 0)]
    truncate_unsigned_positive   : (value, width) => int::rem_euclid(value, 1 << width);
}

k::equations! {
    for TruncateSigned;
    #[k::requires(width <= 0)]
    truncate_signed_nonpositive: (value, width) => value;
    #[k::requires(
        width > 0
            && TruncateUnsigned { value, width } < 1 << (width - 1)
    )]
    truncate_signed_nonnegative: (value, width) => TruncateUnsigned { value, width };
    #[k::requires(
        width > 0
            && TruncateUnsigned { value, width } >= 1 << (width - 1)
    )]
    truncate_signed_negative   : (value, width) => TruncateUnsigned { value, width } - (1 << width);
}

k::equations! {
    for TruncateInteger;
    truncate_integer_unsigned: (value, width, false) => TruncateUnsigned { value, width };
    truncate_integer_signed  : (value, width, true)  => TruncateSigned { value, width };
}

#[k::function(partial, sort = MirValue, syntax = "#localValue({entry})")]
pub struct LocalValueOf {
    pub entry: k::Term<TypedLocal>,
}

k::equations! {
    for LocalValueOf;
    local_value_of: LocalValue::TypedValue { value, .. } => value;
}

#[k::function(partial, sort = TypedLocal, syntax = "#movedEntry({entry})")]
pub struct MovedEntry {
    pub entry: k::Term<TypedLocal>,
}

k::equations! {
    for MovedEntry;
    moved_entry:
        LocalValue::TypedValue { ty, mutability, .. }
        => LocalValue::TypedValue { value: Value::Moved(), ty, mutability };
}

#[k::function(total, sort = List, syntax = "#reserveFor({locals})")]
pub struct ReserveFor {
    pub locals: k::Term<LocalDecls>,
}

k::equations! {
    for ReserveFor;
    reserve_for_done: [] => list::empty();
    reserve_for_cons:
        [MirLocalDecl::LocalDecl { ty, mutability, .. }, tail @ ..] => list::concat(
            list::item(LocalValue::NewLocal { ty, mutability }),
            ReserveFor { locals: tail }
        );
}

#[k::function(total, sort = List, syntax = "#functionBlocks({function})")]
pub struct FunctionBlocks {
    pub function: k::Term<Function>,
}

k::equations! {
    for FunctionBlocks;
    function_blocks:
        MirFunction::MonoItemFn { body: MirFunctionBody::Body { blocks, .. }, .. } => blocks;
}

#[k::function(total, sort = List, syntax = "#functionLocals({function})")]
pub struct FunctionLocals {
    pub function: k::Term<Function>,
}

k::equations! {
    for FunctionLocals;
    function_locals:
        MirFunction::MonoItemFn { body: MirFunctionBody::Body { locals, .. }, .. }
        => ReserveFor { locals };
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

k::equations! {
    for MapRefOffset;
    map_ref_offset_done: (list::empty(), _) => list::empty();
    map_ref_offset_cons:
        (list::concat(list::item(value), tail), offset) => list::concat(
            list::item(AdjustRef { value, offset }),
            MapRefOffset { values: tail, offset }
        );
}

k::equations! {
    for AdjustRef;
    use Value::*;
    adjust_ref_reference:
        (Reference { height, place, mutability, metadata }, offset)
        => Reference { height: height + offset, place, mutability, metadata };
    adjust_ref_pointer:
        (Pointer { height, place, mutability, metadata }, offset)
        => Pointer { height: height + offset, place, mutability, metadata };
    adjust_ref_aggregate:
        (Aggregate { variant, fields }, offset)
        => Aggregate { variant, fields: MapRefOffset { values: fields, offset } };
    adjust_ref_range:
        (Range { elements }, offset)
        => Range { elements: MapRefOffset { values: elements, offset } };
    /// A union holds one value, its active field, and that value may be a
    /// reference into a frame (`union U<'a> { r: &'a i8, n: usize }`), so it is
    /// rebased like a struct field.
    adjust_ref_union:
        (Union { field, value }, offset) => Union { field, value: AdjustRef { value, offset } };
    /// Integers, Booleans, the moved marker, and allocation references hold no
    /// frame height, so crossing a call boundary leaves them unchanged: an
    /// allocation reference names its allocation by `AllocId`, which does not
    /// depend on the call stack.
    adjust_ref_unchanged:
        (value @ (Integer(_, _, _) | Boolean(_) | AllocationReference(_, _, _) | Moved()), _)
        => value;
}

#[k::function(partial, sort = List, syntax = "#frameLocals({frame})")]
pub struct FrameLocals {
    pub frame: k::Term<StackFrame>,
}

k::equations! {
    for FrameLocals;
    frame_locals: MirStackFrame::StackFrame { locals, .. } => locals;
}

#[k::function(partial, sort = MirValue, syntax = "#localFromFrame({frame}, {local}, {offset})")]
pub struct LocalFromFrame {
    pub frame: k::Term<StackFrame>,
    pub local: k::Term<Int>,
    pub offset: k::Term<Int>,
}

k::equations! {
    for LocalFromFrame;
    local_from_frame:
        (MirStackFrame::StackFrame { locals, .. }, local, offset)
        => AdjustRef { value: LocalValueOf { entry: list::get(locals, local) }, offset };
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

k::equations! {
    for WriteProjectedEntry;
    write_projected_entry:
        (LocalValue::TypedValue { value: original, ty, mutability }, projections, value, locals)
        => LocalValue::TypedValue {
            value: WriteProjection { value: original, projections, replacement: value, locals },
            ty,
            mutability
        };
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

k::equations! {
    for UpdateProjectedStackLocal;
    update_projected_stack_local:
        (
            MirStackFrame::StackFrame { caller, dest, target, unwind, locals: frame_locals, span },
            local,
            projections,
            value,
            locals
        ) => MirStackFrame::StackFrame {
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
                    locals
                }
            ),
            span
        };
}

#[k::function(partial, sort = Mutability, syntax = "#borrowMutability({kind})")]
pub struct BorrowMutability {
    pub kind: k::Term<BorrowKind>,
}

k::equations! {
    for BorrowMutability;
    borrow_mutability_shared : MirBorrowKind::SharedBorrow()  => LocalMutability::NotMutable();
    borrow_mutability_mutable: MirBorrowKind::MutableBorrow() => LocalMutability::Mutable();
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

k::equations! {
    for AppendProjections;
    append_projections_done: ([], second) => second;
    append_projections_cons:
        ([head, tail @ ..], second) => [head, ..AppendProjections { first: tail, second }];
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

k::equations! {
    for AppendCastProjections;
    use Projection::*;
    append_cast_projections_done           : ([], second)                        => second;
    #[k::equation(priority = 40)]
    append_cast_projections_cancel_singleton:
        (
            [SingletonArray()],
            [ConstantIndex { offset: 0, min_length: 0, from_end: false }, tail @ ..]
        ) => tail;
    #[k::equation(priority = 40)]
    append_cast_projections_cancel_element:
        (
            [ConstantIndex { offset: 0, min_length: 0, from_end: false }],
            [SingletonArray(), tail @ ..]
        ) => tail;
    #[k::equation(priority = 40)]
    append_cast_projections_cancel_wrapped_field:
        ([WrapStruct()], [Field { field: 0, .. }, tail @ ..]) => tail;
    #[k::equation(priority = 40)]
    append_cast_projections_cancel_to_zst  : ([ToZst()], [FromZst(), tail @ ..]) => tail;
    #[k::equation(priority = 40)]
    append_cast_projections_cancel_from_zst: ([FromZst()], [ToZst(), tail @ ..]) => tail;
    append_cast_projections_cons:
        ([head, tail @ ..], second) => [head, ..AppendCastProjections { first: tail, second }];
}

#[k::function(total, sort = Int, syntax = "#originSize({size})")]
pub struct OriginSize {
    pub size: k::Term<MetadataSize>,
}

k::equations! {
    for OriginSize;
    use MirMetadataSize::*;
    origin_size_none : NoMetadataSize()                     => 0;
    origin_size_sized: StaticSize(size) | DynamicSize(size) => size;
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

k::equations! {
    for DerefProjectionPath;
    use Projection::*;
    #[k::requires(offset == 0)]
    deref_projection_path_zero_offset:
        (referenced, size, offset, _, tail)
        => AppendProjections { first: referenced, second: [DerefTruncate { size }, ..tail] };
    #[k::requires(offset > 0)]
    deref_projection_path_positive_offset:
        (referenced, size, offset, origin_size, tail) => AppendProjections {
            first: referenced,
            second: [
                PointerOffset { offset, origin_size: OriginSize { size: origin_size } },
                DerefTruncate { size },
                ..tail
            ]
        };
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

k::equations! {
    for FreezeProjections;
    use Projection::*;
    freeze_projections_done: ([], _) => [];
    /// These projections already name a fixed place, so freezing keeps them;
    /// only a dynamic index reads a local, which `freeze_projections_index`
    /// replaces by its value.
    freeze_projections_fixed:
        (
            [
                head @ (Field(_, _)
                | WrapStruct()
                | ConstantIndex(_, _, _)
                | Subslice(_, _, _)
                | Downcast(_)
                | PointerOffset(_, _)),
                tail @ ..
            ],
            locals
        ) => [head, ..FreezeProjections { projections: tail, locals }];
    freeze_projections_index:
        ([Index { local }, tail @ ..], locals) => [
            ConstantIndex {
                offset: ExpectUsize { entry: list::get(locals, local) },
                min_length: 0,
                from_end: false
            },
            ..FreezeProjections { projections: tail, locals }
        ];
}

#[k::function(partial, sort = Place, syntax = "#freezePlace({place}, {locals})")]
pub struct FreezePlace {
    pub place: k::Term<Place>,
    pub locals: k::Term<List>,
}

k::equations! {
    for FreezePlace;
    freeze_place:
        (MirPlace::Place { local, projections }, locals)
        => MirPlace::Place { local, projections: FreezeProjections { projections, locals } };
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#expectUsize({entry})"
)]
pub struct ExpectUsize {
    pub entry: k::Term<TypedLocal>,
}

k::equations! {
    for ExpectUsize;
    expect_usize:
        LocalValue::TypedValue { value: Value::Integer { value, width: 64, signed: false }, .. }
        => value;
}

#[k::function(partial, sort = List, syntax = "#rangeElements({value})")]
pub struct RangeElements {
    pub value: k::Term<MirValue>,
}

k::equations! {
    for RangeElements;
    range_elements: Value::Range { elements } => elements;
}

#[k::function(
    partial,
    syntax = "#replaceSubslice({elements}, {start}, {from_back}, {replacement})"
)]
#[k::requires(list::size(replacement) == list::size(elements) - (start + from_back))]
pub fn ReplaceSubslice(
    elements: k::Term<List>,
    start: k::Term<Int>,
    from_back: k::Term<Int>,
    replacement: k::Term<List>,
) -> k::Term<List> {
    list::update_all(elements, start, replacement)
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

k::equations! {
    for ReadProjection;
    use Projection::*;
    use Value::*;
    read_projection_done: (value, [], _) => value;
    read_projection_field:
        (Aggregate { fields, .. }, [Field { field, .. }, tail @ ..], locals)
        => ReadProjection { value: list::get(fields, field), projections: tail, locals };
    read_projection_downcast:
        (Aggregate { fields, .. }, [Downcast { variant }, tail @ ..], locals)
        => ReadProjection { value: Aggregate { variant, fields }, projections: tail, locals };
    read_projection_index:
        (Range { elements }, [Index { local }, tail @ ..], locals) => ReadProjection {
            value: list::get(elements, ExpectUsize { entry: list::get(locals, local) }),
            projections: tail,
            locals
        };
    read_projection_deref:
        (
            Reference { height: 0, place: MirPlace::Place { local, projections: referenced }, .. }
            | Pointer { height: 0, place: MirPlace::Place { local, projections: referenced }, .. },
            [Deref(), tail @ ..],
            locals
        ) => ReadProjection {
            value: LocalValueOf { entry: list::get(locals, local) },
            projections: AppendProjections { first: referenced, second: tail },
            locals
        };
    #[k::requires(offset >= 0 && offset < list::size(elements))]
    read_projection_constant_index_front:
        (Range { elements }, [ConstantIndex { offset, from_end: false, .. }, tail @ ..], locals)
        => ReadProjection { value: list::get(elements, offset), projections: tail, locals };
    #[k::requires(offset > 0 && offset <= min_length && min_length == list::size(elements))]
    read_projection_constant_index_end:
        (
            Range { elements },
            [ConstantIndex { offset, min_length, from_end: true }, tail @ ..],
            locals
        ) => ReadProjection {
            value: list::get(elements, min_length - offset),
            projections: tail,
            locals
        };
    #[k::requires(
        from >= 0 && from <= list::size(elements) && to > 0 && to <= list::size(elements) && from < to
    )]
    read_projection_subslice_front:
        (Range { elements }, [Subslice { from, to, from_end: false }, tail @ ..], locals)
        => ReadProjection {
            value: Range { elements: list::range(elements, from, list::size(elements) - to) },
            projections: tail,
            locals
        };
    #[k::requires(
        from >= 0 && to >= 0 && to < list::size(elements) && from <= list::size(elements) - to
    )]
    read_projection_subslice_end:
        (Range { elements }, [Subslice { from, to, from_end: true }, tail @ ..], locals)
        => ReadProjection {
            value: Range { elements: list::range(elements, from, to) },
            projections: tail,
            locals
        };
}

k::equations! {
    for WriteProjection;
    use Projection::*;
    use Value::*;
    write_projection_done: (_, [], replacement, _) => replacement;
    write_projection_field:
        (Aggregate { variant, fields }, [Field { field, .. }, tail @ ..], replacement, locals)
        => Aggregate {
            variant,
            fields: list::update(
                fields,
                field,
                WriteProjection {
                    value: list::get(fields, field),
                    projections: tail,
                    replacement,
                    locals
                }
            )
        };
    write_projection_downcast:
        (Aggregate { fields, .. }, [Downcast { variant }, tail @ ..], replacement, locals)
        => WriteProjection {
            value: Aggregate { variant, fields },
            projections: tail,
            replacement,
            locals
        };
    write_projection_index:
        (Range { elements }, [Index { local }, tail @ ..], replacement, locals) => Range {
            elements: list::update(
                elements,
                ExpectUsize { entry: list::get(locals, local) },
                WriteProjection {
                    value: list::get(elements, ExpectUsize { entry: list::get(locals, local) }),
                    projections: tail,
                    replacement,
                    locals
                }
            )
        };
    #[k::requires(offset >= 0 && offset < list::size(elements))]
    write_projection_constant_index_front:
        (
            Range { elements },
            [ConstantIndex { offset, from_end: false, .. }, tail @ ..],
            replacement,
            locals
        ) => Range {
            elements: list::update(
                elements,
                offset,
                WriteProjection {
                    value: list::get(elements, offset),
                    projections: tail,
                    replacement,
                    locals
                }
            )
        };
    #[k::requires(offset > 0 && offset <= min_length && min_length == list::size(elements))]
    write_projection_constant_index_end:
        (
            Range { elements },
            [ConstantIndex { offset, min_length, from_end: true }, tail @ ..],
            replacement,
            locals
        ) => Range {
            elements: list::update(
                elements,
                min_length - offset,
                WriteProjection {
                    value: list::get(elements, min_length - offset),
                    projections: tail,
                    replacement,
                    locals
                }
            )
        };
    #[k::requires(
        from >= 0 && from <= list::size(elements) && to > 0 && to <= list::size(elements) && from < to
    )]
    write_projection_subslice_front:
        (
            Range { elements },
            [Subslice { from, to, from_end: false }, tail @ ..],
            replacement,
            locals
        ) => Range {
            elements: ReplaceSubslice {
                elements,
                start: from,
                from_back: list::size(elements) - to,
                replacement: RangeElements {
                    value: WriteProjection {
                        value: Range {
                            elements: list::range(elements, from, list::size(elements) - to)
                        },
                        projections: tail,
                        replacement,
                        locals
                    }
                }
            }
        };
    #[k::requires(
        from >= 0 && to >= 0 && to < list::size(elements) && from <= list::size(elements) - to
    )]
    write_projection_subslice_end:
        (
            Range { elements },
            [Subslice { from, to, from_end: true }, tail @ ..],
            replacement,
            locals
        ) => Range {
            elements: ReplaceSubslice {
                elements,
                start: from,
                from_back: to,
                replacement: RangeElements {
                    value: WriteProjection {
                        value: Range { elements: list::range(elements, from, to) },
                        projections: tail,
                        replacement,
                        locals
                    }
                }
            }
        };
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

k::equations! {
    for BuildProjectionUpdate;
    use MirProjectionContext::*;
    use Value::*;
    build_projection_update_done: (value, []) => value;
    build_projection_update_field:
        (value, [FieldContext { variant, fields, field, .. }, tail @ ..]) => BuildProjectionUpdate {
            value: Aggregate { variant, fields: list::update(fields, field, value) },
            contexts: tail
        };
    build_projection_update_union_field:
        (value, [UnionFieldContext { field, .. }, tail @ ..])
        => BuildProjectionUpdate { value: Union { field, value }, contexts: tail };
    build_projection_update_wrap_struct:
        (
            Aggregate { variant: 0, fields: list::concat(list::item(value), list::empty()) },
            [WrapStructContext(), tail @ ..]
        ) => BuildProjectionUpdate { value, contexts: tail };
    build_projection_update_index:
        (value, [IndexContext { elements, index }, tail @ ..]) => BuildProjectionUpdate {
            value: Range { elements: list::update(elements, index, value) },
            contexts: tail
        };
    build_projection_update_subslice:
        (
            Range { elements: replacement },
            [SubsliceContext { elements, start, from_back }, tail @ ..]
        ) => BuildProjectionUpdate {
            value: Range { elements: ReplaceSubslice { elements, start, from_back, replacement } },
            contexts: tail
        };
    build_projection_update_pointer_offset:
        (
            Range { elements: replacement },
            [PointerOffsetContext { elements, offset, .. }, tail @ ..]
        ) => BuildProjectionUpdate {
            value: Range {
                elements: ReplaceSubslice { elements, start: offset, from_back: 0, replacement }
            },
            contexts: tail
        };
}

#[k::constructors(sort = Continuation, result = KResult)]
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
    };

    lookup_block: {
        k: [Execution::ExecBlockIdx(index), ..],
        current_body: program,
    } => {
        k: [Execution::ExecBlock(list::get(program, index)), ..],
    };

    exec_block: {
        k: [Execution::ExecBlock(BlockSyntax::Block { statements, terminator }), ..],
    } => {
        k: [Execution::ExecStmts(statements), Execution::ExecTerminator(terminator), ..],
    };

    statements_done: {
        k: [Execution::ExecStmts([]), ..],
    } => {
        k: [..],
    };

    statements_cons: {
        k: [Execution::ExecStmts([head, tail @ ..]), ..],
    } => {
        k: [Execution::ExecStmt(head), Execution::ExecStmts(tail), ..],
    };

    assign: {
        k: [Execution::ExecStmt(MirStatement::Assign { place, value }), ..],
    } => {
        k: [Execution::EvalRvalue { value, place }, ..],
    };
}

k::rules! {
    for Machine;

    eval_use: {
        k: [Execution::EvalRvalue { value: MirRvalue::Use(operand), place }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand,
                continuation: EvaluationContinuation::StoreAt(place)
            },
            ..
        ],
    };

    eval_cast: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Cast {
                    kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() },
                    operand,
                    ..
                },
                place
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand,
                continuation: EvaluationContinuation::FinishCast {
                    place,
                    kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() }
                }
            },
            ..
        ],
    };

    eval_ptr_cast: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Cast {
                    kind: MirCastKind::PtrToPtr(),
                    operand: operand @ (MirOperand::Copy(MirPlace::Place { local, projections })
                    | MirOperand::Move(MirPlace::Place { local, projections })),
                    target
                },
                place
            },
            ..
        ],
        locals,
        types,
    } => {
        k: [
            Execution::EvalOperand {
                operand,
                continuation: EvaluationContinuation::FinishPtrCast {
                    place,
                    source: LookupMaybeTy {
                        types,
                        ty: GetTyOf {
                            types,
                            ty: LocalTy { entry: list::get(locals, local) },
                            projections
                        }
                    },
                    target: map::get(types, target)
                }
            },
            ..
        ],
    };

    eval_transmute: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Cast {
                    kind: MirCastKind::Transmute(),
                    operand: operand @ (MirOperand::Copy(MirPlace::Place { local, projections })
                    | MirOperand::Move(MirPlace::Place { local, projections })),
                    target
                },
                place
            },
            ..
        ],
        locals,
        types,
    } => {
        k: [
            Execution::EvalOperand {
                operand,
                continuation: EvaluationContinuation::FinishTransmute {
                    place,
                    source: LookupMaybeTy {
                        types,
                        ty: GetTyOf {
                            types,
                            ty: LocalTy { entry: list::get(locals, local) },
                            projections
                        }
                    },
                    target: map::get(types, target)
                }
            },
            ..
        ],
    };

    eval_ref: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Ref { kind, place: MirPlace::Place { local, projections }, .. },
                place
            },
            ..
        ],
        locals,
        types,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value: LocalValueOf { entry: list::get(locals, local) },
                projections,
                contexts: [],
                locals,
                action: MirProjectionAction::ReferenceAction {
                    place,
                    mutability: BorrowMutability { kind },
                    metadata: MirMetadata::Metadata {
                        size: ProjectionMetadataSize {
                            ty: LocalTy { entry: list::get(locals, local) },
                            projections,
                            types
                        },
                        offset: 0,
                        origin_size: MirMetadataSize::NoMetadataSize()
                    }
                }
            },
            ..
        ],
    };

    eval_address_of: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::AddressOf {
                    mutability,
                    place: MirPlace::Place { local, projections }
                },
                place: destination
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::ResolveAddressOf {
                entry: list::get(locals, local),
                mutability,
                referenced: MirPlace::Place { local, projections },
                destination
            },
            ..
        ],
    };

    address_of_reference_deref: {
        k: [
            Execution::ResolveAddressOf {
                entry: LocalValue::TypedValue {
                    value: Value::Reference { height, place: referenced, metadata, .. },
                    ..
                },
                mutability,
                referenced: MirPlace::Place { projections: [Projection::Deref()], .. },
                destination
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place: destination,
                value: Value::Pointer { height, place: referenced, mutability, metadata }
            },
            ..
        ],
    };

    #[k::rule(owise)]
    address_of_local: {
        k: [
            Execution::ResolveAddressOf {
                entry: LocalValue::TypedValue(_, _, _),
                mutability,
                referenced,
                destination
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::SetLocalValue {
                place: destination,
                value: Value::Pointer {
                    height: 0,
                    place: FreezePlace { place: referenced, locals },
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::NoMetadataSize(),
                        offset: 0,
                        origin_size: MirMetadataSize::NoMetadataSize()
                    }
                }
            },
            ..
        ],
    };

    eval_unary: {
        k: [Execution::EvalRvalue { value: MirRvalue::Unary { operation, operand }, place }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand,
                continuation: EvaluationContinuation::FinishUnary { place, operation }
            },
            ..
        ],
    };

    eval_ub_checks: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Nullary { operation: MirNullOp::UbChecks(), .. },
                place
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    };

    #[k::requires(!IsVoidType { info: map::get(types, ty) })]
    eval_size_of: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Nullary { operation: MirNullOp::SizeOf(), ty },
                place
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: SizeOfTypeInfo { types, info: map::get(types, ty) },
                    width: 64,
                    signed: false
                }
            },
            ..
        ],
    };

    #[k::requires(!IsVoidType { info: map::get(types, ty) })]
    eval_align_of: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Nullary { operation: MirNullOp::AlignOf(), ty },
                place
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: AlignOfTypeInfo { types, info: map::get(types, ty) },
                    width: 64,
                    signed: false
                }
            },
            ..
        ],
    };

    eval_binary: {
        k: [Execution::EvalRvalue { value: MirRvalue::Binary { operation, lhs, rhs }, place }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand: lhs,
                continuation: EvaluationContinuation::BinaryRight {
                    place,
                    operation,
                    rhs,
                    checked: false
                }
            },
            ..
        ],
    };

    eval_checked_binary: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::CheckedBinary { operation, lhs, rhs },
                place
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand: lhs,
                continuation: EvaluationContinuation::BinaryRight {
                    place,
                    operation,
                    rhs,
                    checked: true
                }
            },
            ..
        ],
    };

    eval_aggregate_empty: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::AggregateRvalue { kind, operands: [] },
                place
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: MaterializeAggregate { kind, values: list::empty() }
            },
            ..
        ],
    };

    eval_aggregate_cons: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::AggregateRvalue { kind, operands: [head, tail @ ..] },
                place
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand: head,
                continuation: EvaluationContinuation::AggregateNext {
                    place,
                    kind,
                    values: list::empty(),
                    remaining: tail
                }
            },
            ..
        ],
    };

    eval_repeat: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::Repeat {
                    element,
                    count: MirTyConst::TyConst {
                        kind: MirTyConstKind::Value {
                            allocation: MirAllocation::Allocation { bytes, .. },
                            ..
                        },
                        ..
                    }
                },
                place
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand: element,
                continuation: EvaluationContinuation::FinishRepeat {
                    place,
                    count: ReadTyConstInt { bytes, index: 0, multiplier: 1, result: 0 }
                }
            },
            ..
        ],
    };

    eval_len: {
        k: [Execution::EvalRvalue { value: MirRvalue::Len { place: source }, place }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Copy(source),
                continuation: EvaluationContinuation::FinishLen { place }
            },
            ..
        ],
    };

    eval_copy_for_deref: {
        k: [Execution::EvalRvalue { value: MirRvalue::CopyForDeref { place: source }, place }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Copy(source),
                continuation: EvaluationContinuation::StoreAt(place)
            },
            ..
        ],
    };

    eval_discriminant: {
        k: [
            Execution::EvalRvalue {
                value: MirRvalue::DiscriminantRvalue {
                    place: MirPlace::Place { local, projections }
                },
                place
            },
            ..
        ],
        locals,
        types,
    } => {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Copy(MirPlace::Place { local, projections }),
                continuation: EvaluationContinuation::FinishDiscriminant {
                    place,
                    info: LookupMaybeTy {
                        types,
                        ty: GetTyOf {
                            types,
                            ty: LocalTy { entry: list::get(locals, local) },
                            projections
                        }
                    }
                }
            },
            ..
        ],
    };

    eval_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::Constant(value), continuation }, ..],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    };

    eval_allocated_reference_constant: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::AllocatedConstant {
                    allocation: MirAllocation::Allocation {
                        bytes,
                        provenance: MirProvenanceMap::SingletonProvenanceMap {
                            offset: 0,
                            allocation
                        },
                        ..
                    },
                    ty,
                    ..
                },
                continuation
            },
            ..
        ],
        types,
        memory,
    } => {
        k: [
            Execution::Continue {
                value: DecodeAllocatedReference {
                    allocation,
                    bytes,
                    stored: map::get(memory, allocation),
                    info: map::get(types, ty),
                    types
                },
                continuation
            },
            ..
        ],
    };

    eval_allocated_value_constant: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::AllocatedConstant {
                    allocation: MirAllocation::Allocation {
                        bytes,
                        provenance: MirProvenanceMap::EmptyProvenanceMap(),
                        ..
                    },
                    ty,
                    ..
                },
                continuation
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::Continue {
                value: DecodeAllocatedValue { bytes, info: map::get(types, ty), types },
                continuation
            },
            ..
        ],
    };

    eval_zero_sized_constant: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::ZeroSizedConstant { ty, .. },
                continuation
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::Continue {
                value: DecodeZeroSizedConstant { info: map::get(types, ty) },
                continuation
            },
            ..
        ],
    };

    eval_copy: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Copy(MirPlace::Place { local, projections: [] }),
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::ReadLocal {
                entry: list::get(locals, local),
                move_after: false,
                index: local,
                continuation
            },
            ..
        ],
    };

    eval_copy_field: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Copy(
                    MirPlace::Place { local, projections: [head, tail @ ..] }
                ),
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::ReadProjectedLocal {
                entry: list::get(locals, local),
                local,
                projections: [head, ..tail],
                continuation
            },
            ..
        ],
    };

    eval_move: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Move(MirPlace::Place { local, projections: [] }),
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::ReadLocal {
                entry: list::get(locals, local),
                move_after: true,
                index: local,
                continuation
            },
            ..
        ],
    };

    eval_move_projected: {
        k: [
            Execution::EvalOperand {
                operand: MirOperand::Move(
                    MirPlace::Place { local, projections: [head, tail @ ..] }
                ),
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::ReadMovedProjectedLocal {
                entry: list::get(locals, local),
                local,
                projections: [head, ..tail],
                continuation
            },
            ..
        ],
    };

    read_local_copy: {
        k: [
            Execution::ReadLocal {
                entry: LocalValue::TypedValue { value, .. },
                move_after: false,
                continuation,
                ..
            },
            ..
        ],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    };

    read_local_move: {
        k: [
            Execution::ReadLocal {
                entry: LocalValue::TypedValue { value, ty, mutability },
                move_after: true,
                index,
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [Execution::Continue { value, continuation }, ..],
        locals: list::update(
            locals,
            index,
            LocalValue::TypedValue { value: Value::Moved(), ty, mutability }
        ),
    };

    read_projected_local: {
        k: [
            Execution::ReadProjectedLocal {
                entry: LocalValue::TypedValue { value, .. },
                local,
                projections,
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value,
                projections,
                contexts: [],
                locals,
                action: MirProjectionAction::ReadAction(continuation)
            },
            ..
        ],
    };

    read_moved_projected_local: {
        k: [
            Execution::ReadMovedProjectedLocal {
                entry: LocalValue::TypedValue { value, .. },
                local,
                projections,
                continuation
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value,
                projections,
                contexts: [],
                locals,
                action: MirProjectionAction::MoveAction(continuation)
            },
            ..
        ],
    };

    traverse_projection_read_done: {
        k: [
            Execution::TraverseProjection {
                value,
                projections: [],
                action: MirProjectionAction::ReadAction(continuation),
                ..
            },
            ..
        ],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    };

    traverse_projection_reference_local_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value,
                projections: [],
                contexts,
                action: MirProjectionAction::ReferenceAction {
                    place,
                    mutability,
                    metadata: MirMetadata::Metadata { size, offset, origin_size }
                },
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Reference {
                    height: 0,
                    place: MirPlace::Place {
                        local,
                        projections: ProjectionsFor { contexts, projections: [] }
                    },
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MaybeDynamicSize { size, value },
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    traverse_projection_reference_stack_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToStack { height, local },
                value,
                projections: [],
                contexts,
                action: MirProjectionAction::ReferenceAction {
                    place,
                    mutability,
                    metadata: MirMetadata::Metadata { size, offset, origin_size }
                },
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Reference {
                    height,
                    place: MirPlace::Place {
                        local,
                        projections: ProjectionsFor { contexts, projections: [] }
                    },
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MaybeDynamicSize { size, value },
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    traverse_projection_reference_allocation_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToAllocation(allocation),
                value,
                projections: [],
                contexts,
                action: MirProjectionAction::ReferenceAction {
                    place,
                    metadata: MirMetadata::Metadata { size, offset, origin_size },
                    ..
                },
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::AllocationReference {
                    allocation,
                    projections: ProjectionsFor { contexts, projections: [] },
                    metadata: MirMetadata::Metadata {
                        size: MaybeDynamicSize { size, value },
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    traverse_projection_write_local_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                projections: [],
                contexts,
                action: MirProjectionAction::WriteAction(replacement),
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local, projections: [] },
                value: BuildProjectionUpdate { value: replacement, contexts }
            },
            ..
        ],
    };

    traverse_projection_write_stack_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToStack { height, local },
                projections: [],
                contexts,
                locals,
                action: MirProjectionAction::WriteAction(replacement),
                ..
            },
            ..
        ],
        stack,
    } => {
        k: [..],
        stack: list::update(
            stack,
            height - 1,
            UpdateProjectedStackLocal {
                frame: list::get(stack, height - 1),
                local,
                projections: [],
                value: AdjustRef {
                    value: BuildProjectionUpdate { value: replacement, contexts },
                    offset: -height
                },
                locals
            }
        ),
    };

    traverse_projection_move_local_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value,
                projections: [],
                contexts,
                action: MirProjectionAction::MoveAction(continuation),
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local, projections: [] },
                value: BuildProjectionUpdate { value: Value::Moved(), contexts }
            },
            Execution::Continue { value, continuation },
            ..
        ],
    };

    traverse_projection_move_stack_done: {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToStack { height, local },
                value,
                projections: [],
                contexts,
                locals,
                action: MirProjectionAction::MoveAction(continuation)
            },
            ..
        ],
        stack,
    } => {
        k: [Execution::Continue { value, continuation }, ..],
        stack: list::update(
            stack,
            height - 1,
            UpdateProjectedStackLocal {
                frame: list::get(stack, height - 1),
                local,
                projections: [],
                value: AdjustRef {
                    value: BuildProjectionUpdate { value: Value::Moved(), contexts },
                    offset: -height
                },
                locals
            }
        ),
    };

    traverse_projection_field: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Aggregate { variant, fields },
                projections: [Projection::Field { field, ty }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: list::get(fields, field),
                projections: tail,
                contexts: [
                    MirProjectionContext::FieldContext { variant, fields, field, ty },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    traverse_projection_union_field: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Union { field, value },
                projections: [Projection::Field { field, ty }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value,
                projections: tail,
                contexts: [
                    MirProjectionContext::UnionFieldContext { field, value, ty },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    traverse_projection_wrap_struct: {
        k: [
            traversal @ Execution::TraverseProjection {
                value,
                projections: [Projection::WrapStruct(), tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Aggregate {
                    variant: 0,
                    fields: list::concat(list::item(value), list::empty())
                },
                projections: tail,
                contexts: [MirProjectionContext::WrapStructContext(), ..contexts],
                ..traversal
            },
            ..
        ],
    };

    traverse_projection_downcast: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Aggregate { fields, .. },
                projections: [Projection::Downcast { variant }, tail @ ..],
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Aggregate { variant, fields },
                projections: tail,
                ..traversal
            },
            ..
        ],
    };

    traverse_projection_index: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [Projection::Index { local }, tail @ ..],
                contexts,
                locals,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: list::get(elements, ExpectUsize { entry: list::get(locals, local) }),
                projections: tail,
                contexts: [
                    MirProjectionContext::IndexContext {
                        elements,
                        index: ExpectUsize { entry: list::get(locals, local) }
                    },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(offset >= 0 && offset < list::size(elements))]
    traverse_projection_constant_index_front: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [Projection::ConstantIndex { offset, from_end: false, .. }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: list::get(elements, offset),
                projections: tail,
                contexts: [
                    MirProjectionContext::IndexContext { elements, index: offset },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(
        offset > 0 && offset <= min_length && min_length == list::size(elements)
    )]
    traverse_projection_constant_index_end: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [
                    Projection::ConstantIndex { offset, min_length, from_end: true },
                    tail @ ..
                ],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: list::get(elements, min_length - offset),
                projections: tail,
                contexts: [
                    MirProjectionContext::IndexContext { elements, index: min_length - offset },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(
        from >= 0
            && from <= list::size(elements)
            && to > 0
            && to <= list::size(elements)
            && from < to
    )]
    traverse_projection_subslice_front: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [Projection::Subslice { from, to, from_end: false }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Range {
                    elements: list::range(elements, from, list::size(elements) - to)
                },
                projections: tail,
                contexts: [
                    MirProjectionContext::SubsliceContext {
                        elements,
                        start: from,
                        from_back: list::size(elements) - to
                    },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(
        from >= 0 && to >= 0 && to < list::size(elements) && from <= list::size(elements) - to
    )]
    traverse_projection_subslice_end: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [Projection::Subslice { from, to, from_end: true }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Range { elements: list::range(elements, from, to) },
                projections: tail,
                contexts: [
                    MirProjectionContext::SubsliceContext { elements, start: from, from_back: to },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(offset >= 0 && offset <= list::size(elements))]
    traverse_projection_pointer_offset: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [Projection::PointerOffset { offset, origin_size }, tail @ ..],
                contexts,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Range { elements: list::range(elements, offset, 0) },
                projections: tail,
                contexts: [
                    MirProjectionContext::PointerOffsetContext { elements, offset, origin_size },
                    ..contexts
                ],
                ..traversal
            },
            ..
        ],
    };

    #[k::requires(size >= 0 && size <= list::size(elements))]
    traverse_projection_truncate_size: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [
                    Projection::DerefTruncate {
                        size: MirMetadataSize::StaticSize(size) | MirMetadataSize::DynamicSize(size)
                    },
                    tail @ ..
                ],
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: Value::Range {
                    elements: list::range(elements, 0, list::size(elements) - size)
                },
                projections: tail,
                ..traversal
            },
            ..
        ],
    };

    traverse_projection_truncate_array_head: {
        k: [
            traversal @ Execution::TraverseProjection {
                value: Value::Range(elements),
                projections: [
                    Projection::DerefTruncate { size: MirMetadataSize::NoMetadataSize() },
                    tail @ ..
                ],
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                value: list::get(elements, 0),
                projections: tail,
                ..traversal
            },
            ..
        ],
    };

    #[k::rule(owise)]
    traverse_projection_truncate_non_range: {
        k: [
            traversal @ Execution::TraverseProjection {
                projections: [
                    Projection::DerefTruncate { size: MirMetadataSize::NoMetadataSize() },
                    tail @ ..
                ],
                ..
            },
            ..
        ],
    } => {
        k: [Execution::TraverseProjection { projections: tail, ..traversal }, ..],
    };

    #[k::rule(owise)]
    traverse_projection_current_deref: {
        k: [
            Execution::TraverseProjection {
                value: Value::Reference {
                    height: 0,
                    place: MirPlace::Place { local, projections: referenced },
                    metadata: MirMetadata::Metadata { size, offset, origin_size },
                    ..
                }
                | Value::Pointer {
                    height: 0,
                    place: MirPlace::Place { local, projections: referenced },
                    metadata: MirMetadata::Metadata { size, offset, origin_size },
                    ..
                },
                projections: [Projection::Deref(), tail @ ..],
                locals,
                action,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value: LocalValueOf { entry: list::get(locals, local) },
                projections: DerefProjectionPath { referenced, size, offset, origin_size, tail },
                contexts: [],
                locals,
                action
            },
            ..
        ],
    };

    #[k::requires(height > 0)]
    traverse_projection_stack_deref: {
        k: [
            Execution::TraverseProjection {
                value: Value::Reference {
                    height,
                    place: MirPlace::Place { local, projections: referenced },
                    metadata: MirMetadata::Metadata { size, offset, origin_size },
                    ..
                }
                | Value::Pointer {
                    height,
                    place: MirPlace::Place { local, projections: referenced },
                    metadata: MirMetadata::Metadata { size, offset, origin_size },
                    ..
                },
                projections: [Projection::Deref(), tail @ ..],
                locals,
                action,
                ..
            },
            ..
        ],
        stack,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToStack { height, local },
                value: LocalFromFrame {
                    frame: list::get(stack, height - 1),
                    local,
                    offset: height
                },
                projections: DerefProjectionPath { referenced, size, offset, origin_size, tail },
                contexts: [],
                locals,
                action
            },
            ..
        ],
    };

    traverse_projection_allocation_reference_read: {
        k: [
            Execution::TraverseProjection {
                value: Value::AllocationReference {
                    allocation,
                    projections: referenced,
                    metadata: MirMetadata::Metadata { size, .. }
                },
                projections: [Projection::Deref(), tail @ ..],
                locals,
                action: MirProjectionAction::ReadAction(continuation),
                ..
            },
            ..
        ],
        memory,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToAllocation(allocation),
                value: map::get(memory, allocation),
                projections: DerefProjectionPath {
                    referenced,
                    size,
                    offset: 0,
                    origin_size: MirMetadataSize::NoMetadataSize(),
                    tail
                },
                contexts: [],
                locals,
                action: MirProjectionAction::ReadAction(continuation)
            },
            ..
        ],
    };

    traverse_projection_allocation_reference_reborrow: {
        k: [
            Execution::TraverseProjection {
                value: Value::AllocationReference {
                    allocation,
                    projections: referenced,
                    metadata: MirMetadata::Metadata { size, .. }
                },
                projections: [Projection::Deref(), tail @ ..],
                locals,
                action: MirProjectionAction::ReferenceAction { place, mutability, metadata },
                ..
            },
            ..
        ],
        memory,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToAllocation(allocation),
                value: map::get(memory, allocation),
                projections: DerefProjectionPath {
                    referenced,
                    size,
                    offset: 0,
                    origin_size: MirMetadataSize::NoMetadataSize(),
                    tail
                },
                contexts: [],
                locals,
                action: MirProjectionAction::ReferenceAction { place, mutability, metadata }
            },
            ..
        ],
    };

    continue_store: {
        k: [
            Execution::Continue { value, continuation: EvaluationContinuation::StoreAt(place) },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value }, ..],
    };

    continue_aggregate_done: {
        k: [
            Execution::Continue {
                value,
                continuation: EvaluationContinuation::AggregateNext {
                    place,
                    kind,
                    values,
                    remaining: []
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: MaterializeAggregate {
                    kind,
                    values: list::concat(values, list::item(value))
                }
            },
            ..
        ],
    };

    continue_aggregate_next: {
        k: [
            Execution::Continue {
                value,
                continuation: EvaluationContinuation::AggregateNext {
                    place,
                    kind,
                    values,
                    remaining: [head, tail @ ..]
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand: head,
                continuation: EvaluationContinuation::AggregateNext {
                    place,
                    kind,
                    values: list::concat(values, list::item(value)),
                    remaining: tail
                }
            },
            ..
        ],
    };

    #[k::requires(count >= 0)]
    finish_repeat: {
        k: [
            Execution::Continue {
                value,
                continuation: EvaluationContinuation::FinishRepeat { place, count }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Range { elements: list::make(count, value) }
            },
            ..
        ],
    };

    finish_len: {
        k: [
            Execution::Continue {
                value: Value::Range(elements),
                continuation: EvaluationContinuation::FinishLen { place }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer { value: list::size(elements), width: 64, signed: false }
            },
            ..
        ],
    };

    finish_discriminant: {
        k: [
            Execution::Continue {
                value: Value::Aggregate { variant, .. },
                continuation: EvaluationContinuation::FinishDiscriminant {
                    place,
                    info: MirTypeInfo::EnumType { discriminants, .. }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: LookupDiscriminant { discriminants, index: variant },
                    width: 0,
                    signed: false
                }
            },
            ..
        ],
    };

    finish_pointer_unsize: {
        k: [
            Execution::Continue {
                value: Value::Pointer {
                    height,
                    place: pointer_place,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::StaticSize(size),
                        offset,
                        origin_size
                    }
                },
                continuation: EvaluationContinuation::FinishCast {
                    place,
                    kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Pointer {
                    height,
                    place: pointer_place,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    finish_reference_unsize: {
        k: [
            Execution::Continue {
                value: Value::Reference {
                    height,
                    place: referenced,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::StaticSize(size),
                        offset,
                        origin_size
                    }
                },
                continuation: EvaluationContinuation::FinishCast {
                    place,
                    kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Reference {
                    height,
                    place: referenced,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    finish_allocation_reference_unsize: {
        k: [
            Execution::Continue {
                value: Value::AllocationReference {
                    allocation,
                    projections,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::StaticSize(size),
                        offset,
                        origin_size
                    }
                },
                continuation: EvaluationContinuation::FinishCast {
                    place,
                    kind: MirCastKind::PointerCoercion { coercion: MirPointerCoercion::Unsize() }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::AllocationReference {
                    allocation,
                    projections,
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        offset,
                        origin_size
                    }
                }
            },
            ..
        ],
    };

    finish_transmute_identity: {
        k: [
            Execution::Continue {
                value: value @ (Value::Reference(_, _, _, _)
                | Value::Pointer(_, _, _, _)
                | Value::AllocationReference(_, _, _)),
                continuation: EvaluationContinuation::FinishTransmute {
                    place,
                    source: info,
                    target: info
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value }, ..],
    };

    finish_same_pointee_ptr_cast: {
        k: [
            Execution::Continue {
                value: value @ Value::Pointer(_, _, _, _),
                continuation: EvaluationContinuation::FinishPtrCast {
                    place,
                    source: MirTypeInfo::PointerType { pointee }
                    | MirTypeInfo::ReferenceType { pointee },
                    target: MirTypeInfo::PointerType { pointee }
                    | MirTypeInfo::ReferenceType { pointee }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value }, ..],
    };

    #[k::rule(owise)]
    begin_projected_ptr_cast: {
        k: [
            Execution::Continue {
                value: Value::Pointer { height, place: pointer_place, mutability, metadata },
                continuation: EvaluationContinuation::FinishPtrCast {
                    place: destination,
                    source: MirTypeInfo::PointerType { pointee: source }
                    | MirTypeInfo::ReferenceType { pointee: source },
                    target: MirTypeInfo::PointerType { pointee: target }
                    | MirTypeInfo::ReferenceType { pointee: target }
                }
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                height,
                pointer_place,
                mutability,
                metadata,
                destination,
                source: map::get(types, source),
                target: map::get(types, target),
                projections: [],
                target_size: MetadataSizeOf { info: map::get(types, target) }
            },
            ..
        ],
    };

    resolve_ptr_cast_done: {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                height,
                pointer_place: MirPlace::Place { local, projections: pointer_projections },
                mutability,
                metadata,
                destination,
                source: info,
                target: info,
                projections,
                target_size
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place: destination,
                value: Value::Pointer {
                    height,
                    place: MirPlace::Place {
                        local,
                        projections: AppendCastProjections {
                            first: pointer_projections,
                            second: projections
                        }
                    },
                    mutability,
                    metadata: ConvertPointerMetadata { metadata, target_size }
                }
            },
            ..
        ],
    };

    resolve_ptr_cast_to_zst: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: MirTypeInfo::PrimitiveType(_)
                | MirTypeInfo::ArrayType(_, _)
                | MirTypeInfo::PointerType(_),
                target: MirTypeInfo::VoidType(),
                projections,
                target_size,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::ResolvePtrCast {
                pointer_place,
                source: MirTypeInfo::VoidType(),
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::ToZst()]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    resolve_ptr_cast_from_zst: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: MirTypeInfo::VoidType(),
                target: target @ (MirTypeInfo::PrimitiveType(_)
                | MirTypeInfo::ArrayType(_, _)
                | MirTypeInfo::PointerType(_)),
                projections,
                target_size,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::ResolvePtrCast {
                pointer_place,
                source: target,
                target,
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::FromZst()]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    // `str` is laid out as `[u8]` and its pointers carry the same length, so a
    // cast between a byte-slice pointer and a `str` pointer
    // (`bytes as *const [u8] as *const str`) keeps the place and the
    // metadata: the two pointees compare equal.
    #[k::requires(
        SameTypeInfo {
            first: map::get(types, element),
            second: MirTypeInfo::PrimitiveType {
                primitive: MirPrimitiveType::UnsignedInteger { kind: MirUintTy::U8() }
            }
        }
    )]
    resolve_ptr_cast_bytes_to_str: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                metadata,
                source: MirTypeInfo::ArrayType { element, size: MirMaybeTyConst::NoTyConst() },
                target: target @ MirTypeInfo::PrimitiveType { primitive: MirPrimitiveType::Str() },
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                pointer_place,
                source: target,
                target,
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::requires(
        SameTypeInfo {
            first: map::get(types, element),
            second: MirTypeInfo::PrimitiveType {
                primitive: MirPrimitiveType::UnsignedInteger { kind: MirUintTy::U8() }
            }
        }
    )]
    resolve_ptr_cast_str_to_bytes: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: MirTypeInfo::PrimitiveType { primitive: MirPrimitiveType::Str() },
                target: target @ MirTypeInfo::ArrayType {
                    element,
                    size: MirMaybeTyConst::NoTyConst()
                },
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                pointer_place,
                source: target,
                target,
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::requires(
        bool::and(
            ZeroFieldOffset { layout },
            SameTypeInfo {
                first: MirTypeInfo::ArrayType { element: source_element, size: source_size },
                second: map::get(types, field)
            }
        )
    )]
    resolve_ptr_cast_array_to_exact_wrapper: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: MirTypeInfo::ArrayType { element: source_element, size: source_size },
                target: MirTypeInfo::StructType { name, adt_def, fields: [field], layout },
                projections,
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                pointer_place,
                source: MirTypeInfo::ArrayType { element: source_element, size: source_size },
                target: map::get(types, field),
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::WrapStruct()]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::rule(owise)]
    resolve_ptr_cast_compare_different: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                target_size,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Source(),
                pointer_place,
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::requires(ZeroFieldOffset { layout })]
    resolve_ptr_cast_source_struct: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Source(),
                pointer_place,
                source: MirTypeInfo::StructType { name, adt_def, fields: [field], layout },
                projections,
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: map::get(types, field),
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::Field { field: 0, ty: field }]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    resolve_ptr_cast_source_array: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Source(),
                pointer_place,
                source: MirTypeInfo::ArrayType { element, .. },
                projections,
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: map::get(types, element),
                projections: AppendCastProjections {
                    first: projections,
                    second: [
                        Projection::ConstantIndex { offset: 0, min_length: 0, from_end: false }
                    ]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    // A `str` pointer's first element is its first byte, as for `[u8]`
    // (`str::as_ptr` casts `*const str` to `*const u8`).
    resolve_ptr_cast_source_str: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Source(),
                pointer_place,
                source: MirTypeInfo::PrimitiveType { primitive: MirPrimitiveType::Str() },
                projections,
                target_size,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                source: MirTypeInfo::PrimitiveType {
                    primitive: MirPrimitiveType::UnsignedInteger { kind: MirUintTy::U8() }
                },
                projections: AppendCastProjections {
                    first: projections,
                    second: [
                        Projection::ConstantIndex { offset: 0, min_length: 0, from_end: false }
                    ]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::rule(owise)]
    resolve_ptr_cast_source_done: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Source(),
                pointer_place,
                target_size,
                ..
            },
            ..
        ],
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::TargetPhase(),
                pointer_place,
                target_size,
                ..cast
            },
            ..
        ],
    };

    resolve_ptr_cast_target_array: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::TargetPhase(),
                pointer_place,
                target: MirTypeInfo::ArrayType { element, .. },
                projections,
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                target: map::get(types, element),
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::SingletonArray()]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    #[k::requires(ZeroFieldOffset { layout })]
    resolve_ptr_cast_target_struct: {
        k: [
            cast @ Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::TargetPhase(),
                pointer_place,
                target: MirTypeInfo::StructType { name, adt_def, fields: [field], layout },
                projections,
                target_size,
                ..
            },
            ..
        ],
        types,
    } => {
        k: [
            Execution::ResolvePtrCast {
                phase: MirPtrCastPhase::Compare(),
                pointer_place,
                target: map::get(types, field),
                projections: AppendCastProjections {
                    first: projections,
                    second: [Projection::WrapStruct()]
                },
                target_size,
                ..cast
            },
            ..
        ],
    };

    finish_neg: {
        k: [
            Execution::Continue {
                value: Value::Integer { value, width, signed: true },
                continuation: EvaluationContinuation::FinishUnary {
                    place,
                    operation: MirUnaryOp::UnOpNeg()
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateSigned { value: -value, width },
                    width,
                    signed: true
                }
            },
            ..
        ],
    };

    finish_bool_not: {
        k: [
            Execution::Continue {
                value: Value::Boolean(value),
                continuation: EvaluationContinuation::FinishUnary {
                    place,
                    operation: MirUnaryOp::UnOpNot()
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(!value) }, ..],
    };

    finish_int_not: {
        k: [
            Execution::Continue {
                value: Value::Integer { value, width, signed },
                continuation: EvaluationContinuation::FinishUnary {
                    place,
                    operation: MirUnaryOp::UnOpNot()
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: value ^ -1, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_ptr_metadata: {
        k: [
            Execution::Continue {
                value: Value::Pointer {
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        ..
                    },
                    ..
                }
                | Value::Reference {
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        ..
                    },
                    ..
                }
                | Value::AllocationReference {
                    metadata: MirMetadata::Metadata {
                        size: MirMetadataSize::DynamicSize(size),
                        ..
                    },
                    ..
                },
                continuation: EvaluationContinuation::FinishUnary {
                    place,
                    operation: MirUnaryOp::UnOpPtrMetadata()
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer { value: size, width: 64, signed: false }
            },
            ..
        ],
    };

    continue_binary_right: {
        k: [
            Execution::Continue {
                value: lhs,
                continuation: EvaluationContinuation::BinaryRight { place, operation, rhs, checked }
            },
            ..
        ],
    } => {
        k: [
            Execution::EvalOperand {
                operand: rhs,
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    operation,
                    lhs,
                    checked
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs + rhs, width, signed } == lhs + rhs
    )]
    finish_add: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpAdd(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs + rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs + rhs, width, signed } == lhs + rhs
    )]
    finish_add_unchecked: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpAddUnchecked(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs + rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_checked_add: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: true,
                    operation: MirBinaryOp::BinOpAdd(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Aggregate {
                    variant: 0,
                    fields: list::concat(
                        list::item(
                            Value::Integer {
                                value: TruncateInteger { value: lhs + rhs, width, signed },
                                width,
                                signed
                            }
                        ),
                        list::concat(
                            list::item(
                                Value::Boolean(
                                    TruncateInteger { value: lhs + rhs, width, signed } != lhs + rhs
                                )
                            ),
                            list::empty()
                        )
                    )
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs - rhs, width, signed } == lhs - rhs
    )]
    finish_sub: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpSub(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs - rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs - rhs, width, signed } == lhs - rhs
    )]
    finish_sub_unchecked: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpSubUnchecked(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs - rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_checked_sub: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: true,
                    operation: MirBinaryOp::BinOpSub(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Aggregate {
                    variant: 0,
                    fields: list::concat(
                        list::item(
                            Value::Integer {
                                value: TruncateInteger { value: lhs - rhs, width, signed },
                                width,
                                signed
                            }
                        ),
                        list::concat(
                            list::item(
                                Value::Boolean(
                                    TruncateInteger { value: lhs - rhs, width, signed } != lhs - rhs
                                )
                            ),
                            list::empty()
                        )
                    )
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs * rhs, width, signed } == lhs * rhs
    )]
    finish_mul: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpMul(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs * rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(
        TruncateInteger { value: lhs * rhs, width, signed } == lhs * rhs
    )]
    finish_mul_unchecked: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpMulUnchecked(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs * rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_checked_mul: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: true,
                    operation: MirBinaryOp::BinOpMul(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Aggregate {
                    variant: 0,
                    fields: list::concat(
                        list::item(
                            Value::Integer {
                                value: TruncateInteger { value: lhs * rhs, width, signed },
                                width,
                                signed
                            }
                        ),
                        list::concat(
                            list::item(
                                Value::Boolean(
                                    TruncateInteger { value: lhs * rhs, width, signed } != lhs * rhs
                                )
                            ),
                            list::empty()
                        )
                    )
                }
            },
            ..
        ],
    };

    #[k::requires(
        rhs != 0
            && TruncateInteger { value: lhs / rhs, width, signed } == lhs / rhs
    )]
    finish_div: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpDiv(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs / rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(
        rhs != 0
            && TruncateInteger { value: lhs - lhs / rhs * rhs, width, signed } == lhs - lhs / rhs * rhs
    )]
    finish_rem: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpRem(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs - lhs / rhs * rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_int_bit_xor: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitXor(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer { value: lhs ^ rhs, width, signed }
            },
            ..
        ],
    };

    finish_int_bit_and: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitAnd(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer { value: lhs & rhs, width, signed }
            },
            ..
        ],
    };

    finish_int_bit_or: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitOr(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer { value: lhs | rhs, width, signed }
            },
            ..
        ],
    };

    finish_shl: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpShl(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs << rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(rhs < width)]
    finish_shl_unchecked: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpShlUnchecked(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs << rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_shr: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpShr(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs >> rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    #[k::requires(rhs < width)]
    finish_shr_unchecked: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpShrUnchecked(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Integer {
                    value: TruncateInteger { value: lhs >> rhs, width, signed },
                    width,
                    signed
                }
            },
            ..
        ],
    };

    finish_bool_bit_xor: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitXor(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs != rhs) }, ..],
    };

    finish_bool_bit_and: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitAnd(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs && rhs) }, ..],
    };

    finish_bool_bit_or: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpBitOr(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs || rhs) }, ..],
    };

    #[k::requires(offset == 0)]
    finish_pointer_offset_zero: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: offset, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpOffset(),
                    lhs: Value::Pointer { height, place: pointer_place, mutability, metadata }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Pointer { height, place: pointer_place, mutability, metadata }
            },
            ..
        ],
    };

    #[k::requires(offset >= 0 && current_offset + offset <= origin_size)]
    #[k::rule(owise)]
    finish_pointer_offset_dynamic: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: offset, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpOffset(),
                    lhs: Value::Pointer {
                        height,
                        place: pointer_place,
                        mutability,
                        metadata: MirMetadata::Metadata {
                            size,
                            offset: current_offset,
                            origin_size: MirMetadataSize::DynamicSize(origin_size)
                        }
                    }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Pointer {
                    height,
                    place: pointer_place,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size,
                        offset: current_offset + offset,
                        origin_size: MirMetadataSize::DynamicSize(origin_size)
                    }
                }
            },
            ..
        ],
    };

    #[k::requires(offset >= 0 && current_offset + offset <= origin_size)]
    #[k::rule(owise)]
    finish_pointer_offset_static: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: offset, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpOffset(),
                    lhs: Value::Pointer {
                        height,
                        place: pointer_place,
                        mutability,
                        metadata: MirMetadata::Metadata {
                            size,
                            offset: current_offset,
                            origin_size: MirMetadataSize::StaticSize(origin_size)
                        }
                    }
                }
            },
            ..
        ],
    } => {
        k: [
            Execution::SetLocalValue {
                place,
                value: Value::Pointer {
                    height,
                    place: pointer_place,
                    mutability,
                    metadata: MirMetadata::Metadata {
                        size,
                        offset: current_offset + offset,
                        origin_size: MirMetadataSize::StaticSize(origin_size)
                    }
                }
            },
            ..
        ],
    };

    finish_pointer_eq_same: {
        k: [
            Execution::Continue {
                value: Value::Pointer { height, place: pointer_place, metadata, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpEq(),
                    lhs: Value::Pointer { height, place: pointer_place, metadata, .. }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(true) }, ..],
    };

    #[k::rule(owise)]
    finish_pointer_eq_different: {
        k: [
            Execution::Continue {
                value: Value::Pointer(_, _, _, _),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpEq(),
                    lhs: Value::Pointer(_, _, _, _)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    };

    finish_pointer_ne_same: {
        k: [
            Execution::Continue {
                value: Value::Pointer { height, place: pointer_place, metadata, .. },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpNe(),
                    lhs: Value::Pointer { height, place: pointer_place, metadata, .. }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(false) }, ..],
    };

    #[k::rule(owise)]
    finish_pointer_ne_different: {
        k: [
            Execution::Continue {
                value: Value::Pointer(_, _, _, _),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpNe(),
                    lhs: Value::Pointer(_, _, _, _)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(true) }, ..],
    };

    finish_eq: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpEq(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs == rhs) }, ..],
    };

    finish_lt: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpLt(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs < rhs) }, ..],
    };

    finish_le: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpLe(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs <= rhs) }, ..],
    };

    finish_ne: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpNe(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs != rhs) }, ..],
    };

    finish_ge: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpGe(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs >= rhs) }, ..],
    };

    finish_gt: {
        k: [
            Execution::Continue {
                value: Value::Integer { value: rhs, width, signed },
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpGt(),
                    lhs: Value::Integer { value: lhs, width, signed }
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs > rhs) }, ..],
    };

    finish_bool_eq: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpEq(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs == rhs) }, ..],
    };

    finish_bool_lt: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpLt(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(!lhs && rhs) }, ..],
    };

    finish_bool_le: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpLe(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(!lhs || (lhs && rhs)) }, ..],
    };

    finish_bool_ne: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpNe(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs != rhs) }, ..],
    };

    finish_bool_ge: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpGe(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(!rhs || (rhs && lhs)) }, ..],
    };

    finish_bool_gt: {
        k: [
            Execution::Continue {
                value: Value::Boolean(rhs),
                continuation: EvaluationContinuation::FinishBinary {
                    place,
                    checked: false,
                    operation: MirBinaryOp::BinOpGt(),
                    lhs: Value::Boolean(lhs)
                }
            },
            ..
        ],
    } => {
        k: [Execution::SetLocalValue { place, value: Value::Boolean(lhs && !rhs) }, ..],
    };

    set_local_value: {
        k: [
            Execution::SetLocalValue { place: MirPlace::Place { local, projections: [] }, value },
            ..
        ],
        locals,
    } => {
        k: [Execution::WriteLocal { entry: list::get(locals, local), index: local, value }, ..],
    };

    set_projected_local_value: {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local, projections: [head, tail @ ..] },
                value
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::WriteProjectedLocal {
                entry: list::get(locals, local),
                local,
                projections: [head, ..tail],
                value
            },
            ..
        ],
    };

    write_projected_local: {
        k: [
            Execution::WriteProjectedLocal {
                entry: LocalValue::TypedValue { value: original, .. },
                local,
                projections,
                value
            },
            ..
        ],
        locals,
    } => {
        k: [
            Execution::TraverseProjection {
                target: MirProjectionTarget::ToLocal(local),
                value: original,
                projections,
                contexts: [],
                locals,
                action: MirProjectionAction::WriteAction(value)
            },
            ..
        ],
    };

    write_initialized_local: {
        k: [
            Execution::WriteLocal {
                entry: LocalValue::TypedValue { ty, mutability, .. },
                index,
                value
            },
            ..
        ],
        locals,
    } => {
        k: [..],
        locals: list::update(locals, index, LocalValue::TypedValue { value, ty, mutability }),
    };

    write_new_local: {
        k: [
            Execution::WriteLocal { entry: LocalValue::NewLocal { ty, mutability }, index, value },
            ..
        ],
        locals,
    } => {
        k: [..],
        locals: list::update(locals, index, LocalValue::TypedValue { value, ty, mutability }),
    };
}

k::rules! {
    for Machine;

    goto: {
        k: [Execution::ExecTerminator(MirTerminator::Goto(target)), ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    };

    switch_int: {
        k: [Execution::ExecTerminator(MirTerminator::SwitchInt { discr, targets }), ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand: discr,
                continuation: EvaluationContinuation::SelectBlock(targets)
            },
            ..
        ],
    };

    call_function: {
        k: [
            Execution::ExecTerminator(
                MirTerminator::Call {
                    function: MirCallTarget::ConstantFunction { span, ty: callee, .. },
                    args,
                    destination,
                    target,
                    unwind
                }
            ),
            ..
        ],
        current_func,
        current_body,
        caller: old_caller,
        dest: old_dest,
        target: old_target,
        unwind: old_unwind,
        locals: caller_locals,
        stack,
        functions,
    } => {
        k: [Execution::SetArgsFromStack { index: 1, args }, Execution::ExecBlockIdx(0), ..],
        current_func: callee,
        current_body: FunctionBlocks { function: map::get(functions, callee) },
        caller: current_func,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind,
        locals: FunctionLocals { function: map::get(functions, callee) },
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller: old_caller,
                    dest: old_dest,
                    target: old_target,
                    unwind: old_unwind,
                    locals: caller_locals,
                    span
                }
            ),
            stack
        ),
    };

    set_args_done: {
        k: [Execution::SetArgsFromStack { args: [], .. }, ..],
    } => {
        k: [..],
    };

    set_args_cons: {
        k: [Execution::SetArgsFromStack { index, args: [head, tail @ ..] }, ..],
    } => {
        k: [
            Execution::SetArgFromStack { index, operand: head },
            Execution::SetArgsFromStack { index: index + 1, args: tail },
            ..
        ],
    };

    set_constant_arg: {
        k: [Execution::SetArgFromStack { index, operand: MirOperand::Constant(value) }, ..],
    } => {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local: index, projections: [] },
                value
            },
            ..
        ],
    };

    set_copied_arg: {
        k: [
            Execution::SetArgFromStack {
                index,
                operand: MirOperand::Copy(MirPlace::Place { local, projections: [] })
            },
            ..
        ],
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller,
                    dest,
                    target,
                    unwind,
                    locals: caller_locals,
                    span
                }
            ),
            rest
        ),
    } => {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local: index, projections: [] },
                value: AdjustRef {
                    value: LocalValueOf { entry: list::get(caller_locals, local) },
                    offset: 1
                }
            },
            ..
        ],
    };

    set_moved_arg: {
        k: [
            Execution::SetArgFromStack {
                index,
                operand: MirOperand::Move(MirPlace::Place { local, projections: [] })
            },
            ..
        ],
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller,
                    dest,
                    target,
                    unwind,
                    locals: caller_locals,
                    span
                }
            ),
            rest
        ),
    } => {
        k: [
            Execution::SetLocalValue {
                place: MirPlace::Place { local: index, projections: [] },
                value: AdjustRef {
                    value: LocalValueOf { entry: list::get(caller_locals, local) },
                    offset: 1
                }
            },
            ..
        ],
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller,
                    dest,
                    target,
                    unwind,
                    locals: list::update(
                        caller_locals,
                        local,
                        MovedEntry { entry: list::get(caller_locals, local) }
                    ),
                    span
                }
            ),
            rest
        ),
    };

    assert: {
        k: [
            Execution::ExecTerminator(
                MirTerminator::Assert { condition, expected, message, target, .. }
            ),
            ..
        ],
    } => {
        k: [
            Execution::Expect { condition, expected, message },
            Execution::ExecBlockIdx(target),
            ..
        ],
    };

    drop: {
        k: [Execution::ExecTerminator(MirTerminator::Drop { target, .. }), ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    };

    unreachable: {
        k: [Execution::ExecTerminator(MirTerminator::Unreachable()), ..],
    } => {
        k: [Execution::ProgramError { error: MirExecutionError::ReachedUnreachable() }, ..],
    };

    expect: {
        k: [Execution::Expect { condition, expected, message }, ..],
    } => {
        k: [
            Execution::EvalOperand {
                operand: condition,
                continuation: EvaluationContinuation::FinishAssert { expected, message }
            },
            ..
        ],
    };

    #[k::requires(condition == expected)]
    assert_succeeds: {
        k: [
            Execution::Continue {
                value: Value::Boolean(condition),
                continuation: EvaluationContinuation::FinishAssert { expected, .. }
            },
            ..
        ],
    } => {
        k: [..],
    };

    #[k::requires(condition != expected)]
    #[k::rule(owise)]
    assert_fails: {
        k: [
            Execution::Continue {
                value: Value::Boolean(condition),
                continuation: EvaluationContinuation::FinishAssert { expected, message }
            },
            ..
        ],
    } => {
        k: [Execution::ProgramError { error: MirExecutionError::AssertError { message } }, ..],
    };

    select_otherwise: {
        k: [
            Execution::Continue {
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets { branches: [], otherwise }
                ),
                ..
            },
            ..
        ],
    } => {
        k: [Execution::ExecBlockIdx(otherwise), ..],
    };

    select_true: {
        k: [
            Execution::Continue {
                value: Value::Boolean(true),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: 1, target }, ..],
                        ..
                    }
                )
            },
            ..
        ],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    };

    #[k::requires(branch_value != 1)]
    #[k::rule(owise)]
    select_true_next: {
        k: [
            Execution::Continue {
                value: Value::Boolean(true),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: branch_value, .. }, tail @ ..],
                        otherwise
                    }
                )
            },
            ..
        ],
    } => {
        k: [
            Execution::Continue {
                value: Value::Boolean(true),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets { branches: tail, otherwise }
                )
            },
            ..
        ],
    };

    select_false: {
        k: [
            Execution::Continue {
                value: Value::Boolean(false),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: 0, target }, ..],
                        ..
                    }
                )
            },
            ..
        ],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    };

    #[k::requires(branch_value != 0)]
    #[k::rule(owise)]
    select_false_next: {
        k: [
            Execution::Continue {
                value: Value::Boolean(false),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: branch_value, .. }, tail @ ..],
                        otherwise
                    }
                )
            },
            ..
        ],
    } => {
        k: [
            Execution::Continue {
                value: Value::Boolean(false),
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets { branches: tail, otherwise }
                )
            },
            ..
        ],
    };

    #[k::requires(branch_value == TruncateUnsigned { value, width })]
    select_integer: {
        k: [
            Execution::Continue {
                value: Value::Integer { value, width, .. },
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: branch_value, target }, ..],
                        ..
                    }
                )
            },
            ..
        ],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    };

    #[k::requires(branch_value != TruncateUnsigned { value, width })]
    #[k::rule(owise)]
    select_integer_next: {
        k: [
            Execution::Continue {
                value: Value::Integer { value, width, signed },
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets {
                        branches: [MirBranch::Branch { value: branch_value, .. }, tail @ ..],
                        otherwise
                    }
                )
            },
            ..
        ],
    } => {
        k: [
            Execution::Continue {
                value: Value::Integer { value, width, signed },
                continuation: EvaluationContinuation::SelectBlock(
                    MirSwitchTargets::SwitchTargets { branches: tail, otherwise }
                )
            },
            ..
        ],
    };

    return_to_caller: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        current_func: callee,
        current_body: callee_body,
        caller,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind: callee_unwind,
        locals: list::concat(
            list::item(
                LocalValue::TypedValue { value, ty: return_ty, mutability: return_mutability }
            ),
            callee_locals_tail
        ),
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller: new_caller,
                    dest: new_dest,
                    target: new_target,
                    unwind: new_unwind,
                    locals: new_locals,
                    span: return_span
                }
            ),
            remaining_stack
        ),
        functions,
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [
            Execution::SetLocalValue { place: destination, value: AdjustRef { value, offset: -1 } },
            Execution::ExecBlockIdx(target),
            ..
        ],
        current_func: caller,
        current_body: FunctionBlocks { function: map::get(functions, caller) },
        caller: new_caller,
        dest: new_dest,
        target: new_target,
        unwind: new_unwind,
        locals: new_locals,
        stack: remaining_stack,
    };

    return_unit_to_caller: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        current_func: callee,
        current_body: callee_body,
        caller,
        dest: destination,
        target: MirMaybeBasicBlockIdx::SomeBasicBlockIdx(target),
        unwind: callee_unwind,
        locals: list::concat(
            list::item(LocalValue::NewLocal { ty: return_ty, mutability: return_mutability }),
            callee_locals_tail
        ),
        stack: list::concat(
            list::item(
                MirStackFrame::StackFrame {
                    caller: new_caller,
                    dest: new_dest,
                    target: new_target,
                    unwind: new_unwind,
                    locals: new_locals,
                    span: return_span
                }
            ),
            remaining_stack
        ),
        functions,
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
    };

    top_level_return: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        target: MirMaybeBasicBlockIdx::NoBasicBlockIdx(),
        locals,
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::ReturnLocal { entry: list::get(locals, 0) }, ..],
    };

    return_local: {
        k: [Execution::ReturnLocal { entry: LocalValue::TypedValue { value, .. } }, ..],
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::EndProgram(), ..],
        ret_val: ReturnValue::Returned(value),
    };

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
        current_func: k::configuration::Cell(MirTy::TyId(-1)),
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
        CurrentFrame::caller: k::configuration::Cell(MirTy::TyId(-1)),
        CurrentFrame::dest: k::configuration::Cell(MirPlace::Place(-1, Projections::ProjectionsEmpty())),
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
        current_func: k::configuration::Cell(MirTy::TyId(-1)),
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
        CurrentFrame::caller: k::configuration::Cell(MirTy::TyId(-1)),
        CurrentFrame::dest: k::configuration::Cell(MirPlace::Place(-1, Projections::ProjectionsEmpty())),
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
