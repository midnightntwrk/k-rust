#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KMIR operational slice."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, semantics, entry  # noqa: E402
from support.kdefinition import parse_kore_pattern  # noqa: E402
from support.lock import k_version, krs_ir_schema  # noqa: E402
from support.pins import Ledger, load_toml  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, scratch_root  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import native  # noqa: E402


PORT = semantics.Port(
    label="KMIR",
    key="kmir",
    checkout=ROOT.parent / "inspirations/runtimeverification/mir-semantics",
    descriptors=1222,
)


def definition_checks(readable: str) -> None:
    """Require the emitted definition to carry the KMIR constructs the corpus exercises."""

    if "  imports LIST\n" not in readable:
        raise GateError("emitted KMIR definition does not import pinned LIST")
    if "BlockProgram" in readable or "<blocks>" in readable:
        raise GateError("emitted KMIR definition retained the recursive block adapter")
    if "<locals> $LOCALS:List </locals>" not in readable:
        raise GateError("emitted KMIR definition does not initialize typed List locals")
    if " <- typedValue ( Moved ," not in readable:
        raise GateError("emitted KMIR definition omits move invalidation")
    if "projectionElemField" not in readable or "Aggregate" not in readable:
        raise GateError("emitted KMIR definition omits aggregate field projection")
    if "projectionElemIndex" not in readable or "Range" not in readable or "# expectUsize" not in readable:
        raise GateError("emitted KMIR definition omits local-indexed range projection")
    if "projectionElemConstantIndex" not in readable or "size" not in readable:
        raise GateError("emitted KMIR definition omits guarded constant-index projection")
    if "rvalueRef" not in readable or "Reference" not in readable or "projectionElemDeref" not in readable:
        raise GateError("emitted KMIR definition omits same-frame reference traversal")
    if "# freezeProjections" not in readable or "# appendProjections" not in readable:
        raise GateError("emitted KMIR definition omits frozen reference-place reconstruction")
    if (
        "referenceProjection" not in readable
        or "# projectionsFor" not in readable
        or "# projectionMetadataSize" not in readable
        or "traverse-projection-reference-allocation-done" not in readable
        or "traverse-projection-allocation-reference-reborrow" not in readable
    ):
        raise GateError("emitted KMIR definition omits traversal-based reference creation")
    if "# readProjection" not in readable or "# writeProjection" not in readable:
        raise GateError("emitted KMIR definition omits recursive projection traversal")
    if "# traverseProjection" not in readable or "# buildProjectionUpdate" not in readable:
        raise GateError("emitted KMIR definition omits shared projection traversal")
    if "moveProjection" not in readable or "toStack" not in readable:
        raise GateError("emitted KMIR definition omits cross-frame projected moves")
    if "# readMovedProjectedLocal" not in readable:
        raise GateError("emitted KMIR definition omits projected move invalidation")
    if "projectionElemSubslice" not in readable:
        raise GateError("emitted KMIR definition omits source-shaped subslice projection")
    if "PointerOffset" not in readable or "# originSize" not in readable:
        raise GateError("emitted KMIR definition omits pointer-offset projection")
    if "# derefTruncate" not in readable or "dynamicSize" not in readable:
        raise GateError("emitted KMIR definition omits dereference metadata truncation")
    if "rvalueAddressOf" not in readable or "PtrLocal" not in readable:
        raise GateError("emitted KMIR definition omits raw local pointer creation")
    if "# addressOf" not in readable or "# adjustRef" not in readable:
        raise GateError("emitted KMIR definition omits pointer resolution or frame adjustment")
    if "finish-pointer-eq-same" not in readable or "finish-pointer-ne-different" not in readable:
        raise GateError("emitted KMIR definition omits raw-pointer identity comparison")
    if "unOpPtrMetadata" not in readable or "finish-pointer-metadata" not in readable:
        raise GateError("emitted KMIR definition omits pointer metadata extraction")
    if "binOpOffset" not in readable or "finish-pointer-offset-dynamic" not in readable:
        raise GateError("emitted KMIR definition omits bounded pointer arithmetic")
    if "rvalueCast" not in readable or "castKindPointerCoercion" not in readable:
        raise GateError("emitted KMIR definition omits source-shaped pointer coercion")
    if "pointerCoercionUnsize" not in readable or "finish-pointer-unsize" not in readable:
        raise GateError("emitted KMIR definition omits raw-pointer unsizing")
    if (
        "<types> $TYPES:Map </types>" not in readable
        or "typeInfoPtrType" not in readable
        or "typeInfoRefType" not in readable
    ):
        raise GateError("emitted KMIR definition omits concrete pointer type metadata")
    if (
        "<memory> $MEMORY:Map </memory>" not in readable
        or "AllocRef" not in readable
        or "allocId" not in readable
        or "toAlloc" not in readable
        or "finish-allocation-reference-unsize" not in readable
        or "finish-allocation-reference-metadata" not in readable
    ):
        raise GateError("emitted KMIR definition omits allocation-reference memory traversal")
    if (
        "constantKindAllocated" not in readable
        or "provenanceMapEntry" not in readable
        or "# decodeAllocatedReference" not in readable
        or "eval-allocated-reference-constant" not in readable
    ):
        raise GateError("emitted KMIR definition omits allocated-reference constant decoding")
    if (
        "primTypeBool" not in readable
        or "primTypeInt" not in readable
        or "primTypeUint" not in readable
        or "# decodeAllocatedValue" not in readable
        or "eval-allocated-value-constant" not in readable
    ):
        raise GateError("emitted KMIR definition omits allocated scalar constant decoding")
    if (
        "# decodeArrayAllocation" not in readable
        or "# decodeArrayElements" not in readable
        or "# decodeSliceAllocation" not in readable
        or "# elementSize" not in readable
        or "substrBytes(" not in readable
    ):
        raise GateError("emitted KMIR definition omits recursive array allocation decoding")
    if (
        "# decodeFieldsWithOffsets" not in readable
        or "# neededBytesForOffsets" not in readable
        or "fieldsShapeArbitrary" not in readable
        or "machineSize" not in readable
    ):
        raise GateError("emitted KMIR definition omits layout-aware struct allocation decoding")
    if "typeInfoTupleType" not in readable or "typeInfoTupleType ( . Tys" not in readable:
        raise GateError("emitted KMIR definition omits empty or layout-aware tuple decoding")
    if (
        "typeInfoEnumType" not in readable
        or "# noFields" not in readable
        or "# findVariantIdx" not in readable
        or "# findVariantIdxAux" not in readable
    ):
        raise GateError("emitted KMIR definition omits fieldless enum discriminant decoding")
    if (
        "variantsShapeMultiple" not in readable
        or "tagEncodingDirect" not in readable
        or "integerLengthI128" not in readable
        or "# decodeEnumDirectFields" not in readable
        or "# decodeEnumDirectTag" not in readable
        or "# nthTys" not in readable
        or "# nthVariantOffsets" not in readable
    ):
        raise GateError("emitted KMIR definition omits direct-tag enum field decoding")
    if (
        "primitivePointer" not in readable
        or "addressSpace" not in readable
        or "tagEncodingNiche" not in readable
        or "wrappingRange ( 1 , 0 )" not in readable
    ):
        raise GateError("emitted KMIR definition omits niche-pointer None decoding")
    if (
        "constantKindZeroSized" not in readable
        or "typeInfoFunType" not in readable
        or "# decodeZeroSizedConstant" not in readable
        or "eval-zero-sized-constant" not in readable
    ):
        raise GateError("emitted KMIR definition omits zero-sized constant materialization")
    if (
        "rvalueAggregate" not in readable
        or "aggregateKindAdt" not in readable
        or "aggregateKindArray" not in readable
        or "aggregateKindTuple" not in readable
        or "aggregateKindClosure" not in readable
        or "# mkAggregate" not in readable
        or "eval-aggregate-empty" not in readable
        or "continue-aggregate-next" not in readable
    ):
        raise GateError("emitted KMIR definition omits ordinary aggregate construction")
    if (
        "castKindPtrToPtr" not in readable
        or "finish-same-pointee-ptr-cast" not in readable
        or "finish-same-pointee-ref-to-ptr-ptr-cast" not in readable
    ):
        raise GateError("emitted KMIR definition omits same-pointee pointer casts")
    if "typeInfoArrayType" not in readable or "typeInfoPrimitiveType" not in readable:
        raise GateError("emitted KMIR definition omits array or primitive type metadata")
    if "someTyConst" not in readable or "tyConstKindValue" not in readable:
        raise GateError("emitted KMIR definition omits source-shaped fixed-array lengths")
    if "# readTyConstInt" not in readable or "staticSize" not in readable:
        raise GateError("emitted KMIR definition omits fixed-array metadata decoding")
    if "typeInfoVoidType" not in readable or "# zeroSizedType" not in readable:
        raise GateError("emitted KMIR definition omits zero-sized pointee classification")
    if "typeInfoStructType" not in readable or "# zeroFieldOffset" not in readable:
        raise GateError("emitted KMIR definition omits transparent struct metadata")
    if "projectionElemWrapStruct" not in readable or "CtxWrapStruct" not in readable:
        raise GateError("emitted KMIR definition omits transparent-wrapper traversal")
    if "projectionElemToZST" not in readable or "projectionElemFromZST" not in readable:
        raise GateError("emitted KMIR definition omits zero-sized pointer-cast projections")
    if "projectionElemSingletonArray" not in readable or "# appendCastProjections" not in readable:
        raise GateError("emitted KMIR definition omits pointer-cast projections or cancellation")
    if "# resolvePtrCast" not in readable or "resolve-ptr-cast-source-array" not in readable:
        raise GateError("emitted KMIR definition omits recursive source-first pointer casts")
    if "# convertPointerMetadata" not in readable:
        raise GateError("emitted KMIR definition omits pointer-cast metadata conversion")
    if (
        "castKindTransmute" not in readable
        or "finish-reference-transmute-identity" not in readable
        or "finish-pointer-transmute-identity" not in readable
        or "finish-allocation-reference-transmute-identity" not in readable
    ):
        raise GateError("emitted KMIR definition omits same-representation pointer transmutation")
    if "projectionElemDowncast" not in readable:
        raise GateError("emitted KMIR definition omits source-shaped downcast projection")
    if "range(" not in readable:
        raise GateError("emitted KMIR definition omits builtin List subslice extraction")
    if "updateList(" not in readable:
        raise GateError("emitted KMIR definition omits builtin List subslice replacement")
    if "makeList(" not in readable or "rvalueRepeat" not in readable or "rvalueLen" not in readable:
        raise GateError("emitted KMIR definition omits Repeat or Len array rvalues")
    if (
        "syntax MaybeTy ::= Ty" not in readable
        or "getTyOf" not in readable
        or "TyUnknown" not in readable
        or "# lookupMaybeTy" not in readable
    ):
        raise GateError("emitted KMIR definition omits projected type derivation")
    if (
        "rvalueNullaryOp" not in readable
        or "nullOpSizeOf" not in readable
        or "nullOpAlignOf" not in readable
        or "nullOpUbChecks" not in readable
        or "# sizeOf" not in readable
        or "# alignOf" not in readable
        or "typeInfoUnionType" not in readable
        or "primTypeFloat" not in readable
    ):
        raise GateError("emitted KMIR definition omits nullary type reification")
    if "rvalueBinaryOp" not in readable or "# finishBinary" not in readable:
        raise GateError("emitted KMIR definition omits staged binary operations")
    if "rvalueCheckedBinaryOp" not in readable or "# truncateInteger" not in readable:
        raise GateError("emitted KMIR definition omits checked width-aware arithmetic")
    if "binOpAddUnchecked" not in readable or "binOpMulUnchecked" not in readable:
        raise GateError("emitted KMIR definition omits unchecked arithmetic constructors")
    if "assertMessageOverflow" not in readable or "# expect" not in readable:
        raise GateError("emitted KMIR definition omits source-shaped Assert evaluation")
    if "# ProgramError" not in readable or "AssertError" not in readable:
        raise GateError("emitted KMIR definition omits terminal assertion errors")
    if "terminatorKindDrop" not in readable or "ReachedUnreachable" not in readable:
        raise GateError("emitted KMIR definition omits Drop or Unreachable control effects")
    if "<currentFrame>" not in readable or "<stack>" not in readable or "<functions>" not in readable:
        raise GateError("emitted KMIR definition omits nested call-frame state")
    if "terminatorKindCall" not in readable or "StackFrame" not in readable:
        raise GateError("emitted KMIR definition omits function-call or stack-frame syntax")
    if "#setArgsFromStack" not in readable or "#setArgFromStack" not in readable:
        raise GateError("emitted KMIR definition omits call-argument transfer")
    if "functionBlocks" not in readable or "functionLocals" not in readable:
        raise GateError("emitted KMIR definition omits function-body activation")
    if "adjustRef" not in readable or "localFromFrame" not in readable:
        raise GateError("emitted KMIR definition omits cross-frame reference adjustment")
    if "updateProjectedStackLocal" not in readable or "writeProjectedEntry" not in readable:
        raise GateError("emitted KMIR definition omits cross-frame reference writes")
    if "binOpGt" not in readable or ">Int" not in readable:
        raise GateError("emitted KMIR definition omits integer comparison")
    if "binOpBitXor" not in readable or "xorInt" not in readable:
        raise GateError("emitted KMIR definition omits integer bitwise operations")
    if "binOpShlUnchecked" not in readable or "<<Int" not in readable:
        raise GateError("emitted KMIR definition omits integer shifts")
    if "rvalueUnaryOp" not in readable or "unOpNeg" not in readable:
        raise GateError("emitted KMIR definition omits unary operations")
    if "binOpDiv" not in readable or "/Int" not in readable:
        raise GateError("emitted KMIR definition omits integer division")
    if "switchTargets" not in readable or "# selectBlock" not in readable:
        raise GateError("emitted KMIR definition omits ordered SwitchInt targets")
    if re.search(r"\{V[0-9A-F]+:List \[ V[0-9A-F]+:Int \]\}:>BasicBlock", readable) is None:
        raise GateError("emitted KMIR definition omits typed builtin-list lookup")


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Ledger,
    corpus: Mapping[str, Any],
    native_outcomes: list[dict[str, Any]],
) -> int:
    definition, spec = semantics.reference_definition(
        PORT, workspace, artifacts, k["kompile"], 1, pins
    )

    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    outcomes: list[dict[str, Any]] = []
    for case in behavior:
        current_func = str(case.get("current_func", "ty(-1)"))
        caller = str(case.get("caller", "ty(-1)"))
        destination = str(
            case.get("destination", "place(local(-1), .ProjectionElems)")
        )
        target = str(case.get("target", "noBasicBlockIdx"))
        unwind = str(case.get("unwind", "unwindActionContinue"))
        stack = str(case.get("stack", ".List"))
        functions = str(case.get("functions", ".Map"))
        types = str(case.get("types", ".Map"))
        memory = str(case.get("memory", ".Map"))
        result = run(
            [
                k["krun"],
                "--definition",
                definition,
                "-cPGM=run",
                f"-cPROGRAM={case['program']}",
                f"-cLOCALS={case['locals']}",
                "-cRETVAL=noReturn",
                f"-cCURRENTFUNC={current_func}",
                f"-cCALLER={caller}",
                f"-cDEST={destination}",
                f"-cTARGET={target}",
                f"-cUNWIND={unwind}",
                f"-cSTACK={stack}",
                f"-cFUNCTIONS={functions}",
                f"-cTYPES={types}",
                f"-cMEMORY={memory}",
                "--output",
                "kore",
            ],
            timeout=120,
        ).stdout
        state = parse_kore_pattern(result)
        outcomes.append(native.observed(case, state))

    semantics.compare_routes(PORT.label, native_outcomes, outcomes, {})
    cases_by_id = {str(case["id"]): case for case in behavior}
    for outcome in outcomes:
        native.checked(cases_by_id[str(outcome["id"])], outcome)

    semantics.reference_proof(PORT, definition, spec, k["kprove"])
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="also run the pinned K toolchain behavior comparison and proof",
    )
    parser.add_argument(
        "--record",
        action="store_true",
        help="run the gate and rewrite the output pins it measured",
    )
    semantics.add_artifacts_only_argument(parser)
    arguments = parser.parse_args()
    semantics.reject_artifacts_only_conflicts(parser, arguments)
    try:
        pins = Ledger(PORT.pins_path, record=arguments.record, artifacts_only=arguments.artifacts_only)
        corpus = load_toml(PORT.corpus_path)
        environment = semantics.preflight(PORT, pins, corpus)
        with tempfile.TemporaryDirectory(prefix="krs-kmir-", dir=scratch_root()) as temporary:
            workspace = Path(temporary)
            krs, compiler, runner = semantics.rust_gate(PORT, environment)
            artifacts = semantics.artifact_gate(PORT, workspace, krs, pins, environment)
            definition_checks((artifacts / "definition.k").read_text(encoding="utf-8"))
            definition = semantics.native_definition(workspace, artifacts, compiler, pins, environment)
            if arguments.artifacts_only:
                print(f"PASS readable KMIR operational slice: {semantics.artifacts_only_summary(PORT)}")
                return 0
            executions, native_outcomes = semantics.native_behavior(PORT, runner, definition, pins, corpus, environment)
            proofs = 0
            if arguments.java_reference:
                k = {name: k_tool(name, k_version()) for name in ("kompile", "krun", "kprove")}
                proofs = java_reference_gate(
                    workspace, artifacts, k, pins, corpus, native_outcomes
                )
        pins.finish("readable KMIR operational slice")
        proof_status = (
            f"{proofs} reference proof"
            if arguments.java_reference
            else "1 reference proof deferred to --java-reference"
        )
        print(
            f"PASS readable KMIR operational slice: {PORT.descriptors} descriptors; "
            f"{executions} K-Rust executions; {proof_status}; KRS schema {krs_ir_schema()}"
        )
        return 0
    except (GateError, OSError) as error:
        print(f"FAIL readable KMIR operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    entry("readable KMIR operational slice", main)
