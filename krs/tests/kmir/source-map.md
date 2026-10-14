# Readable KMIR qualification

Status: typed locals, aggregate and active-union fields, indexed ranges and subslices, ordinary place-based rvalues, allocated and zero-sized constant decoding, same- and cross-frame plus allocation-backed references, width-aware integer operations, assertions, ordered control flow, and regular function calls qualified through K-Rust, 2026-08-28 JST

## Pinned authority

The external acceptance corpus is the clean sibling checkout at `../inspirations/runtimeverification/mir-semantics`, relative to the repository root:

- commit `4d793252bcd77091ee759ca6cd1629db41ed5496`;
- K release `7.1.337` from `deps/k_release`, exactly matching KRS;
- core semantics in `kmir/src/kmir/kdist/mir-semantics/`;
- parser fixtures and representative Rust programs under `kmir/src/tests/integration/data/`.

The KMIR checkout and the recovery evidence remain read-only.
KRS owns this fixture, its structured-body adapter, and every generated acceptance artifact.

## Corpus inventory

The selected production roots have the following principal size and rule shapes:

| file | lines | syntax declarations | rules | `requires` | `owise` |
|---|---:|---:|---:|---:|---:|
| `kmir.md` | 742 | 31 | 99 | 28 | 11 |
| `mono.md` | 76 | 10 | 0 | 0 | 0 |
| `body.md` | 518 | 77 | 0 | 0 | 0 |
| `rt/configuration.md` | 78 | 2 | 0 | 0 | 0 |
| `rt/data.md` | 2,488 | 77 | 316 | 121 | 23 |
| `ty.md` | 821 | 159 | 0 | 0 | 0 |

KMIR contains no checked-in K `claim` sentence.
Its proving corpus is generated through the Python tooling from Rust and Stable MIR inputs.
Full KMIR additionally uses generic K lists, nested configuration, call stacks, remaining type metadata, projections and reference forms, allocations, bytes, strictness-generated evaluation, priorities, `owise`, and extensive guarded rules.
This milestone does not claim those features.

## Representative operational slice

The first slice follows KMIR's `#execBlockIdx` / `#execBlock` / `#execStmts` / `#execStmt` / `#execTerminator` pipeline:

1. a basic-block graph stored in K's builtin `List` and ordered recursive statement lists;
2. direct indexed block lookup and a typed builtin-`List` locals cell;
3. `newLocal` and `typedValue` entries that preserve opaque `Ty` and `Mutability` metadata;
4. exact `place(local(...), PROJECTIONS)` syntax for empty places, aggregate `projectionElemField` chains and `projectionElemDowncast`, local-backed `projectionElemIndex`, `projectionElemConstantIndex`, and `projectionElemDeref` values;
5. constant, copied-local, and moved-local operands, including whole-local and projected move invalidation plus later reassignment;
6. recursive aggregate field reads and metadata-preserving persistent reconstruction of every enclosing aggregate on nested field writes;
7. `Range` array/slice values with local-backed indices, front- and end-relative constant indices, and front- and end-relative subslices for reads and persistent nested writes;
8. source-shaped shared and mutable reference creation through type-directed projection traversal with exact metadata, dynamic-index freezing, local/stack/allocation targets, dereference reads, and pointee-directed writes;
9. local assignment through a staged `#setLocalValue` analogue;
10. exact signed and unsigned width truncation shared by arithmetic, shifts, unary operations, and integer branch selection;
11. ordinary addition, subtraction, multiplication, division, and truncating remainder, including unchecked add/subtract/multiply constructors, with upstream undefinedness at overflow and zero divisors;
12. checked addition, subtraction, and multiplication returning wrapped-result and overflow-flag aggregates, followed by source-shaped overflow assertions;
13. all six integer and Boolean comparisons, producing `BoolVal` results;
14. integer and Boolean conjunction, disjunction, and exclusive disjunction through the source `binOpBitAnd`, `binOpBitOr`, and `binOpBitXor` constructors;
15. signed and unsigned left/right shifts, including unchecked width guards, plus Boolean/integer not and signed negation;
16. `Goto` and source-shaped ordered `SwitchInt` branch lists with otherwise fallback and unsigned width-aware integer matching;
17. `Assert` success through its target block and failure as terminal `#ProgramError(AssertError(...))` while retaining the exact overflow message operands;
18. source-shaped no-op `Drop` continuation and terminal `ReachedUnreachable` program errors;
19. top-level `Return` of local `_0` into the return-value cell;
20. source-shaped nested current-frame state, current-function identity, function map, and stack frames for regular constant-target calls;
21. callee local reservation, constant/copy/move argument transfer, caller-side move invalidation, nested return, returned-value placement, caller restoration, and continuation at the selected target block;
22. recursive reference-height adjustment across aggregate and range values, copied reference arguments, read-only dereference through a saved caller frame, and returned-reference height restoration;
23. mutable-reference writes into a saved caller frame with retained projections, recursive replacement-reference height restoration, and saved local type and mutability preservation;
24. one upstream-shaped execution traversal carrying the selected local/stack/allocation target, persistent reconstruction contexts, and read/write/move/reference action over aggregate, range, and reference projections;
25. repeated dereference and references crossing multiple saved call frames for reads, nested writes, and projected move invalidation;
26. retained `PointerOffset(offset, originSize)` traversal over `Range` values, followed by static or dynamic metadata truncation before remaining operand projections;
27. persistent pointer-offset writes below aggregate fields and through saved caller frames;
28. source-shaped `rvalueAddressOf` and `PtrLocal` values, including frozen projected addresses and direct reference-to-pointer shortening;
29. raw-pointer dereference reads and writes in current or saved frames with recursive pointer-height adjustment across calls;
30. raw-pointer equality and inequality over frame height, projected place, and metadata while ignoring mutability;
31. `unOpPtrMetadata` extraction for dynamic pointer/reference sizes and bounded `binOpOffset` arithmetic over static or dynamic origin sizes;
32. the concrete builtin `<types>` map with pointer `TypeInfo` entries and same-pointee `PtrToPtr` copy/move casts;
33. source-shaped fixed-array `TyConst` allocation bytes and metadata conversion among slice pointers and fixed-array pointers of equal or differing lengths;
34. `typeInfoVoidType` zero-sized pointees with `projectionElemToZST` / `projectionElemFromZST` cast markers and inverse cancellation;
35. singleton transparent `typeInfoStructType` pointees with zero-offset layouts, `projectionElemField` / `projectionElemWrapStruct` cast paths, dereference traversal, and persistent write reconstruction;
36. source-shaped `AllocId` identities and `AllocRef` values backed by a concrete allocation-memory map, with retained allocation projections, metadata-truncated read-only dereference traversal, static-to-dynamic unsizing, and dynamic pointer-metadata extraction;
37. source-shaped `castKindTransmute` identity casts for local references, raw pointers, and allocation references when source and target resolve to equal `TypeInfo`;
38. type-directed `rvalueRef` traversal that reconstructs frozen field, index, subslice, pointer-offset, and transparent-wrapper projections and creates `AllocRef` when dereference resolves into allocation memory;
39. source-shaped union ADT construction with exactly one active field plus same-active-field reads, persistent writes, projected moves, and reference creation;
40. source-shaped `AggregateKind::RawPtr` construction from a pointer plus dynamic-length or empty-unit metadata, with requested mutability and retained provenance;
41. one all-path native claim spanning builtin-list lookup, sequencing, local reads and updates, graph edges, a conditional branch, and return.

KMIR receives Stable MIR bodies through generated JSON and converts `BasicBlocks` to K's builtin `List` before execution.
The fixture now preserves that boundary directly as `List<BasicBlock>`.
Execution begins at index zero, retains the program list in state, and projects `PROGRAM [ INDEX ]` to `BasicBlock` before entering the source pipeline.

The fixture now represents locals as KMIR-shaped typed builtin-`List` entries.
As upstream, a moved local is a `TypedValue` whose value is the `Moved` constructor of `Value`, not a separate entry form.
Reads project the value of a `TypedValue`; writes to `NewLocal` or `TypedValue` entries preserve the entry's type and mutability; moving a value replaces its source with `typedValue(Moved, TY, MUTABILITY)`, keeping the entry's type and mutability.
Moving a projected value first reads the selected value, then persistently reconstructs its enclosing aggregate or range with only that projection replaced by the source `Moved` marker.
Reading an uninitialized entry has no rule and therefore halts; reading a moved entry yields `Moved`, as upstream's `typedValue(VAL, _, _) => VAL` does.
The selected nonempty `Place` surface admits arbitrary chains of `projectionElemField` over aggregate values and dynamic or constant indices over `Range` values.
Recursive reads use typed builtin-List lookup at every selected depth; writes rebuild each enclosing aggregate or range and the typed local through persistent List updates while preserving every variant index, local type, and mutability.
An index local must contain `Integer(_, 64, false)`, matching KMIR's partial `#expectUsize` boundary; invalid indices and value/projection combinations remain undefined.
Front-relative constant indices require an in-range offset.
End-relative constant indices require an exact `minLength` and select `minLength - offset` for both reads and writes, following the documented Stable MIR meaning and correcting an inconsistent upstream read equation: the pinned KMIR traversal reads the element at `OFFSET` while its write context records `MINLEN -Int OFFSET`, so a read and a write of the same end-relative place select different elements (upstream mir-semantics/constant-index-from-end-read-write).
Creating a reference now enters the same projection traversal used by reads, writes, and moves.
The initial metadata size is derived from the local `Ty`, selected place projections, and concrete type map; a final `Range` replaces the dynamic placeholder with its concrete view length.
Reconstruction contexts retain field types and distinguish pointer offsets from ordinary subslices, so the resulting place freezes dynamic indices and preserves field, subslice, offset, and wrapper structure.
Completion creates a height-zero or saved-frame `Reference` for local/stack targets and an `AllocRef` for allocation targets.
This makes reborrowing through an allocation reference source-shaped rather than a constructor-only test path.
Dereference reads append the retained reference projections to the remaining read path; dereference writes redirect assignment to the referenced local and rebuild its selected aggregate/range path without replacing the reference value.
Front-relative subslices remove `from` elements from the front and `to` elements from the back.
End-relative subslices use the source-defined reversed interpretation of those operands.
Reads use K's builtin `LIST.range`; writes reconstruct the selected nested value and replace the same contiguous region through `LIST.updateAll` while preserving each enclosing range, aggregate, and typed local.
The selected `Assert` route evaluates its operand explicitly, compares the resulting `BoolVal` with the expected Boolean, and either enters the target block or leaves `#ProgramError(AssertError(assertMessageOverflow(...)))` terminal at the head of the computation.
The ignored `unwindActionContinue` field is retained in the source-shaped terminator; alternate unwind behavior remains deferred.
Aggregate downcasts replace the active variant index before continuing recursive projection traversal, including persistent writes through a selected variant field.
Regular calls resolve a constant function target through the function map, push the caller metadata and locals, reserve the callee's declared locals, and begin its first block.
Constant arguments are written directly into callee locals; copied and moved whole-local arguments are read from the saved caller frame, with moved arguments replacing the saved caller entry by a metadata-preserving moved local.
Returning a value restores the caller function, body, metadata, and locals, writes callee local `_0` to the call destination, and resumes at the selected target block.
Returning an uninitialized unit local restores the caller without writing the destination.
Copying or moving a reference-valued argument increments every reference height recursively through aggregate and range values because the caller frame has been pushed.
A selected read-only dereference resolves the saved frame at `height - 1`, adjusts any fetched reference by the traversed height, and applies the retained reference and operand projections against that frame's locals.
Returning a reference decrements its height recursively before storing it in the restored caller.
A selected positive-height mutable-reference write updates the saved frame at `height - 1`, appends the retained reference projections to the post-dereference path, and recursively shifts the replacement value by `-height` before storing it in caller coordinates.
The saved local retains its original type and mutability.
Projected copy reads, writes, and moves now traverse one projection at a time as a shared execution command, retaining stack access between steps.
Field, index, and subslice contexts reconstruct every enclosing value after a write or move, while dereference resets obsolete contexts and redirects the target to the referenced current or saved local.
If a dereference fetches another positive-height reference, traversal selects its saved frame and continues rather than falling into the same-frame-only pure helper.
The same route handles references crossing more than one saved call frame and preserves the selected aggregate, downcast, dynamic/constant index, and subslice read behavior.
Nested cross-frame writes apply the replacement at the final target and restore caller-coordinate reference heights.
Projected moves return the selected value in current coordinates while rebuilding the target with `Moved`, including saved caller locals.
Pointer-offset reference metadata is retained for the selected `Range` boundary.
Dereference first applies the reference place's frozen projections, then any metadata-provided offset as `PointerOffset(offset, originSize)`, then static or dynamic metadata truncation, and only then the operand's remaining projections.
Pointer-offset traversal selects the suffix beginning at the offset while recording the original range for persistent reconstruction; truncation limits only the selected view and adds no reconstruction context, following the pinned upstream equations.
The selected path works below aggregate fields and through saved caller frames for reads and writes.
The selected raw-pointer boundary retains source-shaped `rvalueAddressOf(mutability, place)` and `PtrLocal(height, place, mutability, metadata)` terms.
Direct local addresses freeze dynamic indices just like references, so later mutation of the index local cannot retarget the pointer.
Addressing the sole dereference of a reference shortens the chain to a `PtrLocal` over the reference's place and metadata, matching the pinned higher-priority upstream rule.
Raw pointers use the shared projection traversal for current- and saved-frame reads, writes, pointer offsets, and metadata truncation.
Recursive frame-height adjustment now covers pointers inside aggregates and ranges as well as references.
Raw-pointer equality compares exact frame height, frozen projected place, and metadata identity while deliberately ignoring mutability.
Ordered fallback rules distinguish different locals, array-element projections, offsets and other metadata, or frame heights without assigning invented numeric addresses.
`unOpPtrMetadata` returns a source-shaped unsigned 64-bit integer only for a dynamic pointer or reference size.
`binOpOffset` preserves every pointer component for a zero offset, including thin pointers without origin metadata.
Nonzero offsets preserve the current view size and advance the metadata offset only when the operand is nonnegative and the result is no greater than the static or dynamic origin size.
The exact one-past-end pointer result is allowed, while dereferencing it remains undefined through the existing projection guards.
`rvalueCast(castKindPointerCoercion(pointerCoercionUnsize), operand, target)` evaluates its copy or move operand through the shared operand path.
For `PtrLocal` and `Reference` values with `staticSize`, the selected upstream coercion changes only the current size to `dynamicSize`; frame height, place, mutability, offset, and origin metadata are preserved exactly.
Unsupported coercions remain undefined rather than receiving a guessed fallback.
The concrete configuration now retains the upstream `<types>` lookup boundary as a builtin `Map` from `Ty` to the selected `typeInfoPtrType(pointee)` and `typeInfoRefType(pointee)` surfaces.
For whole-local copy and move operands, `rvalueCast(castKindPtrToPtr, operand, target)` preserves the complete raw pointer when the source and target `TypeInfo` entries name the same pointee type.
The move form uses the shared operand route and therefore invalidates its source local exactly once.
Raw-pointer values may carry any of the source's four raw-pointer/reference outer-type combinations.
When their pointees differ, all four combinations enter the same source-first projection and target-metadata conversion route.
Dynamic slice and primitive-u8 `TypeInfo` entries now drive the upstream source-first recursive array conversion.
Source arrays append `projectionElemConstantIndex(0, 0, false)` while target arrays append `projectionElemSingletonArray`; inverse array projections cancel at the append boundary.
This supports nested slice-to-element conversion, element-to-slice pointer construction, and composed roundtrips without assigning numeric addresses.
Target metadata conversion loses dynamic size when producing a thin pointer, creates dynamic size one from a thin pointer, and preserves the upstream static/dynamic origin policy.
Fixed-array lengths retain the source `someTyConst(tyConst(tyConstKindValue(...)))` shape, including allocation bytes, empty provenance, alignment, and mutability.
The selected unsigned `usize` allocation is decoded little-endian, so slice-to-array, array-to-slice, and differing fixed-array pointer casts produce the target static or dynamic size while retaining the source allocation size as origin metadata.
As upstream specifies, construction of a pointer to a longer fixed array remains allowed; a later dereference is responsible for rejecting insufficient origin length.
The selected zero-sized boundary classifies the source `typeInfoVoidType` as a ZST and appends `projectionElemToZST` or `projectionElemFromZST` when crossing the material/ZST boundary.
Adjacent inverse ZST projections cancel, so a material-to-ZST-to-material roundtrip recovers the original pointer place.
Pinned KMIR defines no traversal rule for dereferencing either ZST marker; this tranche therefore qualifies pointer construction and cancellation only.
Transparent singleton structs retain the upstream `typeInfoStructType` shape, including the `AdtDef`, singleton `Tys`, and arbitrary-field `LayoutShape` whose sole field offset is `machineSize(0)`.
KRS independent expansion now preserves declared token-sort constructor fields as symbolic terms over their concrete token newtypes, allowing the source `String` name field to survive readable-to-reference projection without an invented algebraic marker trait.
Source-side casts append `projectionElemField(fieldIdx(0), FIELD)` and target-side casts append `projectionElemWrapStruct`; the exact array-to-wrapper case is selected before ordinary source-array unwrapping.
Only a `projectionElemWrapStruct` followed by the inverse field projection cancels, matching the valid runtime cancellation order.
Dereference traversal materializes a singleton `Aggregate`, and the retained `CtxWrapStruct` removes that synthetic wrapper after a persistent write rebuilds the selected field.
The selected allocation boundary retains source-shaped `allocId(Int)` identities and `AllocRef(AllocId, ProjectionElems, Metadata)` values.
The concrete `<memory>` map stores allocation values by identity.
A read-only dereference restarts shared projection traversal from the selected allocation value, discards obsolete local projection contexts, replays the reference's allocation projections, applies metadata truncation, and then continues with the operand projections.
The pointer offset carried by an allocation reference remains intentionally ignored, matching pinned KMIR's current rule and FIXME; mutable allocation traversal is not enabled by this slice.
`PointerCoercion::Unsize` converts an allocation reference's current `staticSize` to `dynamicSize` while preserving its allocation identity, retained projections, pointer offset, and origin metadata.
`unOpPtrMetadata` returns that dynamic size as the source-shaped unsigned 64-bit integer, placing allocation references on the same selected metadata surface as local pointers and references.
The selected `castKindTransmute` boundary resolves the source local and target `Ty` through the concrete type map.
Local references, raw pointers, and allocation references are preserved exactly only when both entries resolve to equal `TypeInfo`; copy leaves the source intact and move uses ordinary source invalidation.
Unequal representations remain undefined rather than receiving a byte-layout guess.
Allocated fixed arrays retain their source `typeInfoArrayType(element, someTyConst(...))` metadata and decode the length from its little-endian `usize` allocation.
Each element consumes exactly the recursively computed element size; decoding succeeds only when the requested element count consumes the allocation bytes exactly.
Dynamic slices use the same element decoder after requiring a positive element size and exact divisibility of the allocation length.
Arbitrary-layout structs retain their declared field types and machine-size offsets.
Each field is decoded from its half-open byte interval in declaration order, while the required allocation length is the maximum offset-plus-field-size extent rather than the sum of field sizes.
This preserves reordered and padded layouts and composes recursively with nested fixed arrays and structs.
An empty `typeInfoTupleType(.Tys, LAYOUT)` materializes `Aggregate(variantIdx(0), .List)` only from zero allocation bytes.
Nonempty tuples require an arbitrary-field layout and reuse the same extent and declaration-order decoder as structs.
An explicit tuple layout supplies its element size, so tuple fields can participate recursively in later aggregate decoders.
Fieldless enums retain source-shaped discriminant and per-variant field-list constructors.
The decoder first proves every variant field list empty, reads the allocation bytes as one unsigned little-endian tag, and selects the index of the exact matching declared discriminant.
An absent discriminant match remains undefined instead of producing an adapted variant or error value.
Direct-tag enums retain the source `variantsShapeMultiple`, initialized integer scalar, direct encoding, integer-length, per-variant layout-list, and wrapping-range surfaces.
The decoder reads only the tag-width prefix as an unsigned little-endian integer, selects the exact declared discriminant, indexes both the selected field-type list and its arbitrary-offset layout, and decodes fields in declaration order.
The qualified behavior covers every supported integer tag width from I8 through I128, signed and unsigned tag metadata, nonconsecutive and high-byte discriminants, and selection of the third variant in a three-variant layout.
Invalid tags, insufficient tag bytes, absent variant entries, and non-arbitrary selected layouts remain undefined through the existing partial allocation-decoding boundary.
The selected niche-pointer Option case retains the source pointer primitive, address space, niche tag encoding, wrapping range, and two-variant field-list layout.
Exactly all-zero allocation bytes decode to the empty variant-zero aggregate, matching pinned KMIR's only supported niche representation.
Nonzero pointer and reference payloads remain undefined because pinned KMIR explicitly requires a different encoding for them.
Ordinary `constantKindZeroSized` operands resolve their `Ty` through the concrete type map.
Structs, tuples, and function items materialize as empty variant-zero aggregates, while fixed zero-length arrays materialize as an empty `Range`, matching all four pinned `rt/data.md` rules.
The function-item `TypeInfo` remains distinct from the existing zero-sized function call target: the former is an ordinary value operand, while the latter identifies a function-table entry during call setup.
The shared typed Bytes surface now includes half-open `BYTES.substr` in descriptor protocol 34 and Definition IR schema 26; the K-Rust adapter targets the pinned `substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int` label directly.
Missing type entries, incompatible terminal pointees, projected cast operands, allocation mutation and remaining allocation operations, other zero-sized TypeInfo constructors, and the opaque-cast and subtype projection kinds remain deferred.

## Source mapping

- `kmir.md`: block-index lookup, block expansion, ordered statement execution, assignment dispatch, `Goto`, ordered `SwitchInt` selection, `Assert`, `Drop`, `Unreachable`, regular call setup, argument transfer, return restoration, program-error stopping, and top-level `Return`;
- `body.md`: `BasicBlock`, `StatementKind::Assign`, `Rvalue`, `Operand`, `Goto`, `SwitchInt`, and `Return` syntax families;
- `rt/configuration.md`: computation, current body, locals, return-value state, static type lookup table, and allocation-memory cell;
- `rt/data.md`: typed local-list lookup, whole-local and projected move invalidation, `#setLocalValue`, ordinary ADT/array/tuple/closure, active-field union, and raw-pointer aggregate construction, aggregate and same-active union fields, transparent-wrapper, and downcast plus dynamic and constant range-index traversal, wrapper-context reconstruction, same-frame and allocation-backed reference dereferencing, metadata-preserving list update, `rvalueUse`, `rvalueCopyForDeref`, `rvalueDiscriminant`, `rvalueNullaryOp`, staged casts, ordinary and checked binary operations, unary operations, disabled UB checks, width truncation, arithmetic, comparisons, bitwise operations, and shifts;
- `alloc.md`, `rt/value.md`, and `rt/decoding.md`: `AllocId`, `AllocRef`, allocation-memory lookup, concrete read traversal shapes, recursive fixed/dynamic array decoding, layout-offset struct/tuple decoding, and fieldless plus direct-tag enum decoding;
- `rt/types.md`: concrete `Ty` to `TypeInfo` lookup, source-shaped `Ty < MaybeTy`, total retained projection-type derivation, primitive and layout-backed `#sizeOf` and `#alignOf`, fixed/dynamic array and thin/fat pointer/reference sizes, source-first recursive array and transparent-wrapper projections, inverse projection cancellation, and target metadata conversion;
- `ty.md`: source-shaped primitive, aggregate, enum, union, dynamic, array, pointer/reference, function, and void `TypeInfo`, `FloatTy`, `Tys`/`Tyss`, discriminants, direct integer-tag scalar metadata, multiple-variant layout lists, and arbitrary-field offsets;
- `schema-parse/basicblock1`, `statementassign1`, `terminatorgoto`, and `terminatorreturn`: concrete serialized constructor shapes;
- `prove-rs/if.rs`, `else.rs`, `const-arithm-simple.rs`, `arith.rs`, `checked_arithmetic.rs`, `bitwise-not-shift.rs`, `bitwise-shift.rs`, `struct.rs`, `array_write.rs`, `array_match.rs`, and `enum-direct-tag-decode.rs`: representative Boolean branch, arithmetic, comparison, overflow, bitwise, shift, aggregate-field, local-indexed range, subslice, mutable-reference, and direct-tag enum programs exercised by KMIR's integration suite;
- `decode-value/enum-2-variants-1-field.json` and `.expected`: serialized and concrete evidence for direct-tag selection of a nonzero variant and decoding of its arbitrary-offset field list;
- `decode-value/enum-option-ref-none.json` and `.expected`: serialized and concrete evidence for the all-zero niche-pointer Option representation and its empty variant-zero aggregate;
- `prove-rs/const-empty.rs` and `exec-smir/call-with-args/closure-call.smir.json`: source and serialized evidence for ordinary unit and zero-sized function-item/closure operands;
- `exec-smir/enum/enum.smir.json` and `enum.state`: serialized and concrete source-shaped evidence for empty and nonempty ADT aggregates, nonzero variants, generic arguments, allocated operands, copies, moves, and whole-local discriminant inspection.
- `exec-smir/arrays/array_write.state`: concrete retained-reference evidence for the source-shaped front-relative constant-index place.
- `exec-smir/arrays/array_write.smir.json`: serialized `Rvalue::Ref`, dynamic `Index`, `Deref` assignment, and later indexed-copy evidence.
- `prove-rs/arith.smir.json`: serialized checked addition/multiplication followed by an `Assert` whose condition is a projected `Move` of the aggregate overflow flag.
- `exec-smir/main-a-b-c/main-a-b-c.smir.json`: serialized nested zero-argument call and return evidence.
- `exec-smir/call-with-args/main-a-b-with-int.smir.json`: serialized constant and copied argument-transfer evidence.
- `exec-smir/references/refAsArg.smir.json` and `refAsArg.state`: serialized and concrete evidence for a copied reference argument dereferenced by its callee.
- `exec-smir/references/refReturned.smir.json` and `refReturned.state`: serialized and concrete evidence for reference transfer through returns and caller-side dereference.
- `exec-smir/references/mutableRef.rs`, `mutableRef.smir.json`, and `mutableRef.state`: source, serialized, and concrete evidence for mutable-reference writes both across and within call frames.
- `exec-smir/references/doubleRef.rs`, `doubleRef.smir.json`, and `doubleRef.state`: source, serialized, and concrete evidence for repeated dereference through a reference-to-reference value.
- `exec-smir/references/refAsArg2.rs`, `refAsArg2.smir.json`, and `refAsArg2.state`: source, serialized, and concrete evidence for a reference transferred through two nested calls.
- `exec-smir/references/weirdRefs.rs`, `weirdRefs.smir.json`, and `weirdRefs.state`: source, serialized, and concrete evidence for `CopyForDeref`, nested mutable dereference, and reference/field projection chains.
- `exec-smir/pointers/offset_read`, `offset_write`, `offset_struct_field_read`, and `offset_struct_field_write`: source, serialized, and concrete evidence for raw-pointer aggregate construction, retained pointer offsets, dynamic metadata truncation, nested aggregate traversal, and persistent writes.
- `exec-smir/pointers/ref_ptr_cases.rs`, `ref_ptr_cases.smir.json`, and `ref_ptr_cases.state`: source, serialized, and concrete evidence for local addresses, reference-to-pointer conversion, raw-pointer dereference, frozen array-element identity, and mutation.
- `exec-smir/pointers/offset_get_unchecked.rs`, `offset_get_unchecked.smir.json`, and `offset_get_unchecked.state`: source, serialized, and concrete evidence for pointer unsizing, metadata extraction, bounded offset operations, and offset-element reads.
- `prove-rs/pointer-cast.rs` and `exec-smir/pointers/pointer-cast-length-test-fail`: source, serialized, and concrete evidence for slice/array `PtrToPtr` projection and metadata conversion, including the upstream specimen's deliberate invalid-length boundary.
- `prove-rs/align_and_size.rs`: source evidence for generic `size_of` and `align_of` type reification.
- `exec-smir/pointers/pointer-cast-zst.state`: concrete evidence for `nullOpAlignOf` in a zero-sized pointer-cast execution path.
- `run-smir-random/complex-types/test.smir.json`: serialized Stable MIR evidence for repeated `nullOpUbChecks` control flow plus union types, construction, and field access.

## Unsupported shapes recorded before implementation

Protocol-16 ordinary fixed-cell rewrites already scale to the selected state, and the IMP milestone already qualifies finite-map matching and persistent update.
Constructor-pattern branch rules avoid rule-table guards.
Explicit evaluation commands preserve read-before-write staging without claiming K's full strictness protocol.

The initial milestone exposed one independent-expansion gap, K1.
A source module that both authored `map!` in a claim and used readable map extras required an explicit `use k::map`, while reference expansion unconditionally inserted the same import for the readable rules.
The resulting duplicate macro import made the independently expanded crate fail to compile.
KRS detects an existing equivalent use tree before inserting its generated map-macro import.
The focused compiler regression proves that attributes do not hide an existing import and that unrelated imports do not suppress insertion.
K1 is an import-hygiene fix only.

The current milestone adds K's associative builtin `List` as a shared KRS surface in descriptor protocol 18 and Definition IR schema 11.
The closed operation catalog is `.List`, `ListItem`, associative concatenation, indexed lookup, persistent indexed update, and `size`.
Element sorts remain explicit in Semantic and Definition IR so indexed lookup emits the required typed projection, such as `{PROGRAM:List [ INDEX:Int ]}:>BasicBlock`.
The source emitter and native `k-rust` adapter use the pinned `LIST` labels, and focused tests cover registry identity, descriptor arity, IR validation, exact K source, reference expansion, and native adaptation.

The typed-local tranche exposed a KRS lowering gap: readable fixed-cell updates recognized only `map::update`, even though the typed operation catalog and both IRs already supported `list::update`.
Head-rule lowering now validates the updated cell's resolved collection sort and accepts the registered persistent update for either `Map` or `List`.
The KMIR collection/lowering test and emitted definition qualify the List-cell route without changing the descriptor protocol or Definition IR schema.

The subslice tranche extends the shared closed List operation catalog with `LIST.range` and `LIST.updateAll` in descriptor protocol 33 and Definition IR schema 25.
Readable K emits `range(LIST, FROM_FRONT, FROM_BACK)` and `updateList(LIST, INDEX, REPLACEMENT)`.
The K-Rust adapter targets the pinned frontend's explicit `List:range` symbol and its synthesized `updateList(_,_,_)_LIST_List_List_Int_List` label.
A focused regression resolves that synthesized label through the production carrying the `LIST.updateAll` hook, so a prelude identity change fails closed.

The aggregate-allocation tranche extends the shared Bytes operation catalog with half-open `BYTES.substr` in descriptor protocol 34 and Definition IR schema 26.
Readable K emits `substrBytes(BYTES, START, END)`, and the K-Rust adapter targets the pinned frontend label directly.
Focused shared tests cover registry identity, typed arity, canonical K emission, readable expansion, and native adaptation.

The array-rvalue tranche extends the shared closed List operation catalog with `LIST.make` in descriptor protocol 35 and Definition IR schema 27.
Readable K emits `makeList(LENGTH, VALUE)`, and the K-Rust adapter targets the pinned frontend's synthesized `makeList(_,_)_LIST_List_Int_KItem` label.
Focused shared tests resolve the marker through the production carrying the existing `LIST.make` hook, while KMIR qualifies the operation through source-shaped `Repeat` execution.

The place-rvalue tranche retains source-shaped `rvalueCopyForDeref(PLACE)` and `rvalueDiscriminant(PLACE)` constructors.
`CopyForDeref` reuses the complete ordinary copy route, including arbitrary selected projections, without invalidating its source.
Enum discriminants copy the whole or projected aggregate, resolve its exact `TypeInfo` through the local type and `<types>` map, and recursively select the declared discriminant at the aggregate's variant index.
The result is `Integer(DISCRIMINANT, 0, false)`, preserving pinned KMIR's flexible-width unsigned representation and nonconsecutive user discriminants.

The projection-type tranche preserves pinned KMIR's direct `Ty` subsort of `MaybeTy` and its fail-closed `TyUnknown` result without a wrapper adapter.
The total concrete `getTyOf` equations traverse retained dereference, field, dynamic-index, constant-index, subslice, and downcast projections.
Projected `PtrToPtr`, `Transmute`, and `Discriminant` evaluation reuse that single type boundary; unsupported internal or not-yet-retained projection shapes resolve to `TyUnknown` and remain undefined at the consuming operation.

The nullary-operation tranche retains source-shaped `nullOpSizeOf`, `nullOpAlignOf`, and `nullOpUbChecks` constructors without a synthesized type query.
UB checks return `BoolVal(false)` because pinned KMIR independently signals undefined unchecked-arithmetic overflow.
Size and alignment results use the pinned 64-bit unsigned `usize` representation and cover signed/unsigned integers, all four float widths, Boolean, character, string, enum, struct, union, tuple, fixed and dynamic arrays, plus thin and fat raw pointers and references.
Aggregate values read size bits and ABI alignment bytes from `LayoutShape`, missing aggregate layouts retain the pinned zero-size and unit-alignment defaults, and explicit void-type queries remain undefined at the rvalue boundary.
`nullOpOffsetOf` remains a separate unselected semantic boundary.

The union-rvalue tranche retains the source `aggregateKindAdt(..., someFieldIdx(fieldIdx(FIELD)))` boundary and requires exactly one evaluated operand before constructing `Union(fieldIdx(FIELD), VALUE)`.
Projection traversal selects that value only when the requested field is the active field, retains `CtxFieldUnion` for persistent reconstruction and reference creation, and rebuilds the same active field on writes and projected moves.
Pinned KMIR marks cross-field reinterpretation as a TODO and supplies no rule, so that case remains deliberately undefined.

The raw-pointer aggregate tranche retains `aggregateKindRawPtr(TY, MUTABILITY)` and the ordinary ordered operand-evaluation boundary.
A pointer followed by `Integer(LENGTH, 64, false)` produces dynamic-size metadata and removes only a trailing zero `ConstantIndex`, matching pinned `removeIndexTail`.
A pointer followed by an empty aggregate unit produces `noMetadataSize` without changing its place.
Both forms apply the aggregate's requested mutability while preserving frame height, pointer offset, and origin size; the pinned rules leave their commented validity guards unenforced, so KRS does not add a stronger local guard.

Deferred corpus shapes include `nullOpOffsetOf`, cross-field union reinterpretation, opaque-cast and subtype projections, remaining raw-pointer operations beyond raw-pointer/reference outer metadata, allocation mutation and remaining memory operations, multiplicity cells, indirect calls, intrinsics, remaining assertion-message and unwind forms, panic paths, remaining binary operators, symbolic generated lookup functions, and KMIR's Python-generated proof workflow.
A later slice may extend KRS only when one of these shapes is selected as acceptance evidence.

## Acceptance contract

The checked-in default gate must establish deterministic collection and expansion, formatting, warnings-denied Clippy, focused rust-analyzer probes, direct Definition IR compilation through K-Rust, and K-Rust behavior for the selected graph and local-state paths.
The all-path proof and K toolchain comparison are deliberate final-reference evidence selected with `--java-reference`.
Pins may be updated only after reviewing emitted K and structured behavior; re-record them by running the gate with `--record` (add `--java-reference` to re-record the kompiled reference digest) and review the pin diff.
`python3 tests/kmir/verify.py --artifacts-only` stops after the emitted-artifact and native KORE pins and skips the behavior and proof comparisons; it passes only when every artifact is byte-identical to its pin (see `semantics/README.md`).

The canonical KRS port is `semantics/kmir`, the corpus is `tests/kmir/corpus.toml`, and the fail-closed entry point is `python3 tests/kmir/verify.py`.

## Qualification result

The complete fixture gate passes with native builtin-list program storage and lookup:

```text
PASS readable KMIR operational slice: 1228 descriptors; 184 K-Rust executions; 1 reference proof deferred to --java-reference; protocol 35
```

The behavior matrix covers direct top-level return, constant assignment, ordered copied-local assignment, width-aware ordinary and checked integer arithmetic, all three unchecked arithmetic constructors on defined inputs, checked-add assertion success and overflow failure, signed division and remainder, integer and Boolean comparisons, integer/Boolean bitwise and unary operations, signed/unsigned checked and unchecked shifts, comparison-driven control flow, sequential and nonadjacent indexed `Goto`, Boolean and width-aware integer `SwitchInt` matching with ordered branch scanning and otherwise fallback, no-op `Drop`, terminal `Unreachable`, read-before-overwrite staging, third-block lookup in a three-element list, both outcomes of the combined four-block specimen, whole-local and projected move invalidation, reassignment of a moved local, single/nested aggregate field reads and writes, aggregate downcast reads and writes, dynamic plus constant range-index reads and writes, front- and end-relative subslice reads and nested writes, shared/mutable same-frame reference creation, frozen dynamic indices, dereference reads, pointee-directed dereference writes, returned-value placement, nested zero-argument calls, constant and copied arguments, moved-argument invalidation in the caller, copied reference arguments dereferenced through a saved frame, returned-reference height restoration, caller-local mutation through a callee reference, caller-coordinate restoration for a reference-valued cross-frame write, repeated dereference, nested cross-frame reference reads and writes, reference reads through two saved call frames, cross-frame projected move invalidation with enclosing caller-value reconstruction, pointer-offset slice reads and writes, metadata-provided offsets, aggregate-contained pointer offsets, cross-frame pointer-offset mutation, raw local address creation, frozen raw-pointer indices, reference-to-pointer writes, pointer argument transfer, raw-pointer offset writes, aliasing equality across mutability, pointer inequality by local, array element, metadata, and frame height, dynamic pointer/reference metadata extraction, zero-offset thin pointers, interior pointer offsets followed by reads, one-past-end pointer construction, raw-pointer and reference unsizing with exact provenance preservation, move invalidation through casts, metadata extraction from an unsized pointer, copy/move `PtrToPtr` casts between distinct raw-pointer/reference outer types with the same pointee metadata, slice-to-element pointer reads across raw-pointer/reference type metadata, element-to-slice reference-type pointer construction, inverse array-projection cancellation, nested slice-to-element conversion, slice/static-array metadata conversion, fixed-array length changes with retained source-size provenance, material/ZST pointer conversion, inverse ZST projection cancellation, transparent-wrapper-to-field reads, field-to-wrapper reads, wrapper roundtrip cancellation, persistent writes through wrapper pointers, direct allocation-backed scalar reads, retained allocation-field projection, dynamic allocation-slice truncation, allocation-reference unsizing, and allocation-reference metadata extraction.
Successful executions restore or preserve the expected builtin current-body list, observe its exact block count, finish with an empty call stack, halt with an empty computation, and match their locals and return value; expected program-error cases retain the pinned terminal error ahead of any continuation.
The behavior matrix additionally covers same-representation `Transmute` identity for allocation references, local references, and moved raw pointers.
It also covers allocation-element reborrowing with frozen projection identity and allocation-slice reborrowing with recomputed dynamic metadata.
It also covers source-shaped allocated constants with singleton provenance, including a thin reference followed by scalar dereference and a fat reference followed by dynamic metadata extraction and allocation-view truncation.
It also covers source-shaped allocated scalar constants through Boolean negation, signed `i16` addition after negative-value decoding, and unsigned `u128` multiplication.
It also covers fixed `u16` array decoding followed by indexed projection, dynamic signed-integer slice decoding followed by indexed projection, padded and reordered struct layout decoding followed by field projection, and nested fixed-array decoding inside a struct followed by field and index projection.
It also covers zero-byte empty-tuple materialization and padded, reordered tuple decoding followed by field projection.
It also covers a fieldless enum whose one-byte tag selects a nonzero variant index from nonconsecutive declared discriminants.
It also covers direct-tag enums with fields across I8, I16, I32, I64, and I128 tag widths, including nonconsecutive and high-byte discriminants, signed tag metadata, per-variant offsets, and selection beyond the second variant.
It also covers the source niche-pointer Option layout whose all-zero allocation decodes to the empty variant-zero aggregate.
It also covers zero-sized struct, tuple, fixed zero-length array, and function-item constants, including their distinct empty aggregate and range representations.
It also covers source-shaped ordinary aggregate construction for empty and nonempty ADTs, arrays, tuples, and closures, including ordered constant/copy/move evaluation, copy preservation, move invalidation, allocated operands, generic arguments, nonzero ADT variants, and exact `Aggregate` or `Range` results.
It also covers source-shaped active-field union construction, same-field reads, persistent writes, projected move invalidation, and reference-mediated writes with a frozen field projection.
It also covers source-shaped fat and thin raw-pointer aggregate construction, trailing zero-index removal, dynamic versus absent metadata, requested mutability, preserved pointer provenance, copy preservation, and move invalidation.
It also covers source-shaped array repetition with allocated, copied, and moved elements; allocation-backed zero, two, and three-element lengths; copy preservation; move invalidation; and exact whole-local or projected range lengths.
It also covers projected `CopyForDeref` without source mutation and whole-local enum discriminants at the first and third variants, including the nonconsecutive user discriminant `9090`.
It also covers projected discriminants through downcast and field, dynamic index, reference dereference, and subslice plus constant-index chains, as well as projected pointer casts and projected transmute moves with enclosing aggregate reconstruction.
It also covers disabled UB checks; primitive integer, float, Boolean, character, and string size/alignment constants; aggregate layout size and alignment including absent layouts; fixed and dynamic array size/alignment; and thin/fat raw-pointer and reference size/alignment.
The structured behavior SHA-256 is `e4bae64f34415d319cf2ac153f2972a8788cfefee66a7ece17e2e84b28ad36f9`.

The concrete all-path claim spans four builtin-list block lookups, ordered statements, constant and copied operands, integer addition, `Goto`, true `SwitchInt`, local `_0`, and top-level return.
It remains pinned for `python3 tests/kmir/verify.py --java-reference` and is not run during routine development.

The definition contains 259 equations, 181 machine rules, and one claim across 1,228 descriptors.
The direct K-Rust `definition.kore` SHA-256 is `58b4971b8b0cb21aeddef634d3c814ca326568645df8dbd7acdf5da75dbc36bb`.
Six focused definition and hover probes pass with zero rust-analyzer diagnostics.
