#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KMIR operational slice."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.checkouts import verify_checkout  # noqa: E402
from support.hashing import canonical_json, exact_directory, json_sha256, sha256_file, sha256_text  # noqa: E402
from support.kdefinition import EMITTED_ARTIFACTS, normalized_kore_sha256, split_claims  # noqa: E402
from support.pins import load_toml, table  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, rust_analyzer, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = ROOT / "semantics/kmir/Cargo.toml"
SOURCE = ROOT / "semantics/kmir/src/lib.rs"
LOCK = ROOT / "semantics/Cargo.lock"
CORPUS_PATH = HERE / "corpus.toml"
PINS_PATH = HERE / "pins.toml"
KMIR = ROOT.parent / "inspirations/runtimeverification/mir-semantics"
PACKAGE = "krs-kmir-semantics"
DEFINITION = "main"
MODULE = "KRS-KMIR"
SPEC_MODULE = f"{MODULE}-SPEC"
DESCRIPTORS = 1228
SOURCE_LEDGER_PATHS = (
    "crates/krs-compiler/src/collect.rs",
    "crates/krs-compiler/src/emit.rs",
    "crates/krs-compiler/src/lowering.rs",
    "crates/krs-compiler/src/overlap.rs",
    "crates/krs-compiler/src/reference.rs",
    "crates/krs-compiler/src/semantic.rs",
    "crates/krs-compiler/src/sidecar.rs",
    "crates/krs-ir/src/definition.rs",
    "crates/krs-ir/src/grammar.rs",
    "crates/krs-ir/src/head_rule.rs",
    "crates/krs-ir/src/ir.rs",
    "crates/krs-ir/src/lib.rs",
    "crates/krs-ir/src/protocol_v6.rs",
    "crates/krs-ir/src/protocol_v7_rule.rs",
    "crates/krs-ir/src/semantic.rs",
    "crates/krs-ir/src/state.rs",
    "crates/krs-k-rust/src/lib.rs",
    "crates/krs-k-rust/src/bin/krs-native-compile.rs",
    "crates/krs-k-rust/src/bin/krs-native-runner.rs",
    "crates/krs-expand/src/environment.rs",
    "crates/krs-expand/src/expand.rs",
    "crates/krs-expand/src/islands.rs",
    "crates/krs-expand/src/lib.rs",
    "crates/krs-expand/src/provenance.rs",
    "crates/krs-macros/src/environment.rs",
    "crates/krs-macros/src/lib.rs",
    "crates/krs-syntax/src/provenance.rs",
    "crates/krs-syntax/src/rule.rs",
    "crates/krs-syntax/src/state_rule.rs",
    "crates/krs-syntax/src/term.rs",
    "crates/krs/src/lib.rs",
    "tests/kmir/source-map.md",
    "tests/kmir/corpus.toml",
    "tests/kmir/lsp_probe.py",
    "tests/kmir/native.py",
    "semantics/Cargo.lock",
    "semantics/Cargo.toml",
    "semantics/README.md",
    "semantics/coverage.toml",
    "semantics/kmir/Cargo.toml",
    "semantics/kmir/src/lib.rs",
    "tests/kmir/verify.py",
)

def preflight(pins: Mapping[str, Any], corpus: Mapping[str, Any]) -> dict[str, str]:
    if pins.get("schema") != 1 or corpus.get("schema") != 1:
        raise GateError("KMIR gate schema differs from 1")
    if sha256_file(CORPUS_PATH) != pins.get("corpus_sha256"):
        raise GateError("corpus.toml differs from its pin")
    kmir_pin = table(pins.get("kmir"), "pins.kmir")
    verify_checkout(KMIR, str(kmir_pin.get("commit")), label="KMIR evidence")
    if (KMIR / "deps/k_release").read_text(encoding="utf-8").strip() != kmir_pin.get(
        "version"
    ):
        raise GateError("KMIR K release differs")

    schemas = table(pins.get("schemas"), "pins.schemas")
    protocol = (ROOT / "crates/krs-ir/src/lib.rs").read_text(encoding="utf-8")
    ir = (ROOT / "crates/krs-ir/src/ir.rs").read_text(encoding="utf-8")
    if f"pub const CURRENT: Self = Self({schemas.get('descriptor_protocol')});" not in protocol:
        raise GateError("descriptor protocol differs")
    if f"pub const CURRENT: Self = Self({schemas.get('definition_ir')});" not in ir:
        raise GateError("Definition IR schema differs")

    expected_sources = table(pins.get("source_sha256"), "pins.source_sha256")
    if set(expected_sources) != set(SOURCE_LEDGER_PATHS):
        raise GateError("KMIR source-ledger path set differs")
    for relative in SOURCE_LEDGER_PATHS:
        if sha256_file(ROOT / relative) != expected_sources[relative]:
            raise GateError(f"KMIR source ledger differs: {relative}")

    expected_external = table(pins.get("external_sha256"), "pins.external_sha256")
    evidence = corpus.get("source_evidence")
    if not isinstance(evidence, list) or not evidence:
        raise GateError("source evidence is empty")
    evidence_paths = {str(entry["path"]) for entry in evidence}
    if set(expected_external) != evidence_paths:
        raise GateError("external evidence-ledger path set differs")
    for relative in evidence_paths:
        if sha256_file(KMIR / relative) != expected_external[relative]:
            raise GateError(f"external KMIR evidence differs: {relative}")

    return {**z3_environment(), "CARGO_NET_OFFLINE": "true"}


def rust_gate(environment: Mapping[str, str]) -> tuple[Path, Path, Path]:
    root_target = Path(
        os.environ.get("KRS_KMIR_ROOT_TARGET", "/var/tmp/krs-kmir-gate-root-target")
    )
    fixture_target = Path(
        os.environ.get(
            "KRS_KMIR_FIXTURE_TARGET", "/var/tmp/krs-kmir-gate-fixture-target"
        )
    )
    run(
        ["cargo", "build", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
    )
    run(
        ["cargo", "build", "--locked", "--offline", "--release", "-p", "krs-k-rust", "--bins"],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(root_target)},
        timeout=900,
    )
    common = ["--manifest-path", MANIFEST, "--locked", "--offline"]
    fixture_env = {
        **environment,
        "CARGO_TARGET_DIR": os.fspath(fixture_target),
    }
    run(["cargo", "check", *common, "--all-targets"], environment=fixture_env)
    run(["cargo", "test", *common], environment=fixture_env, timeout=900)
    run(
        ["cargo", "clippy", *common, "--all-targets", "--", "-D", "warnings"],
        environment=fixture_env,
        timeout=900,
    )
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(
        [root_target / "debug/krs", "fmt", "--check", "--manifest-path", MANIFEST, SOURCE],
        environment=environment,
    )
    run(
        ["cargo", "+1.88.0", "check", *common, "--all-targets"],
        environment=fixture_env,
        timeout=900,
    )
    analyzer = rust_analyzer()
    lsp_env = {
        **environment,
        "PATH": os.pathsep.join([os.fspath(analyzer.parent), os.environ["PATH"]]),
    }
    run([sys.executable, HERE / "lsp_probe.py"], environment=lsp_env, timeout=900)
    return (
        root_target / "debug/krs",
        root_target / "release/krs-native-compile",
        root_target / "release/krs-native-runner",
    )


def artifact_gate(
    workspace: Path,
    krs: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    base = [
        "--manifest-path",
        MANIFEST,
        "--package",
        PACKAGE,
        "--definition",
        DEFINITION,
    ]
    check = run([krs, "check", *base], environment=environment)
    if f"{DESCRIPTORS} descriptors" not in check.stdout:
        raise GateError(f"unexpected descriptor count: {check.stdout.strip()}")
    expansions = [run([krs, "expand", *base], environment=environment).stdout for _ in range(2)]
    if expansions[0] != expansions[1]:
        raise GateError("readable expansion is nondeterministic")
    digest = sha256_text(expansions[0])
    if digest != pins.get("expansion_sha256"):
        raise GateError(f"expansion hash differs: {digest}")

    expanded = workspace / "expanded"
    expanded.joinpath("src").mkdir(parents=True)
    manifest = MANIFEST.read_text(encoding="utf-8")
    for relative, absolute in {
        "../../crates/krs": ROOT / "crates/krs",
        "../../crates/krs-compiler": ROOT / "crates/krs-compiler",
        "../../crates/krs-ir": ROOT / "crates/krs-ir",
    }.items():
        manifest = manifest.replace(relative, os.fspath(absolute))
    expanded.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
    shutil.copy2(LOCK, expanded / "Cargo.lock")
    expanded.joinpath("src/lib.rs").write_text(expansions[0], encoding="utf-8")
    expanded_target = workspace / "expanded-target"
    run(
        [
            "cargo",
            "check",
            "--manifest-path",
            expanded / "Cargo.toml",
            "--locked",
            "--offline",
        ],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )

    outputs = [workspace / "emit-a", workspace / "emit-b"]
    for output in outputs:
        run([krs, "emit-k", *base, "--output", output], environment=environment)
    hashes = exact_directory(outputs[0], outputs[1], EMITTED_ARTIFACTS)
    if hashes != dict(table(pins.get("artifact_sha256"), "pins.artifact_sha256")):
        raise GateError(f"emitted artifact hashes differ: {canonical_json(hashes)}")

    expanded_output = workspace / "expanded-emit"
    run(
        [
            krs,
            "emit-k",
            "--manifest-path",
            expanded / "Cargo.toml",
            "--package",
            PACKAGE,
            "--definition",
            DEFINITION,
            "--output",
            expanded_output,
        ],
        environment={**environment, "CARGO_TARGET_DIR": os.fspath(expanded_target)},
        timeout=900,
    )
    readable = (outputs[0] / "definition.k").read_text(encoding="utf-8")
    expanded_k = (expanded_output / "definition.k").read_text(encoding="utf-8")
    sentence = re.compile(r"^  (rule|claim)(?: \[([^]]+)\])?", re.MULTILINE)
    if readable.split("\n  rule ", 1)[0] != expanded_k.split("\n  rule ", 1)[0]:
        raise GateError("independent expansion changed syntax or configuration")
    if sentence.findall(readable) != sentence.findall(expanded_k):
        raise GateError("independent expansion changed rule or claim identities")
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
    return outputs[0]


def normalize_term(value: str) -> str:
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    value = re.sub(r"\.\s+", ".", value)
    return value


def observed_cell(result: str, name: str) -> str:
    match = re.search(rf"<{name}>\s*(.*?)\s*</{name}>", result, re.DOTALL)
    if match is None:
        raise GateError(f"native output omitted <{name}>: {result}")
    return normalize_term(match.group(1))


def compile_native_definition(
    workspace: Path,
    artifacts: Path,
    compiler: Path,
    pins: Mapping[str, Any],
    environment: Mapping[str, str],
) -> Path:
    definition = workspace / "native-definition.kore"
    run(
        [compiler, artifacts / "definition-ir.json", definition],
        environment=environment,
        timeout=900,
    )
    kore_hash = sha256_file(definition)
    if kore_hash != pins.get("native_definition_kore_sha256"):
        raise GateError(f"native K-Rust definition.kore hash differs: {kore_hash}")
    return definition


def k_rust_gate(
    runner: Path,
    definition: Path,
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
    environment: Mapping[str, str],
) -> int:
    behavior = corpus.get("behavior")
    if not isinstance(behavior, list) or not behavior:
        raise GateError("behavior corpus is empty")
    result = run(
        [sys.executable, HERE / "native.py", runner, definition, MODULE, CORPUS_PATH],
        environment=environment,
        timeout=900,
    )
    expected = f"PASS native KMIR behavior: {len(behavior)} executions; sha256={pins.get('behavior_sha256')}"
    if result.stdout.strip() != expected:
        raise GateError(f"K-Rust behavior evidence differs: {result.stdout.strip()}")
    return len(behavior)


def java_reference_gate(
    workspace: Path,
    artifacts: Path,
    k: Mapping[str, str],
    pins: Mapping[str, Any],
    corpus: Mapping[str, Any],
) -> tuple[int, int]:
    claim_free, _, claims = split_claims(
        (artifacts / "definition.k").read_text(encoding="utf-8"), 1
    )
    semantics = workspace / "semantics.k"
    semantics.write_text(claim_free, encoding="utf-8")
    definition = workspace / "semantics-kompiled"
    run(
        [
            k["kompile"],
            semantics,
            "--backend",
            "haskell",
            "--main-module",
            MODULE,
            "--syntax-module",
            MODULE,
            "--emit-json",
            "--output-definition",
            definition,
        ],
        timeout=900,
    )
    kore_hash = normalized_kore_sha256(
        definition / "definition.kore", semantics
    )
    if kore_hash != pins.get("definition_kore_sha256"):
        raise GateError(f"native definition.kore hash differs: {kore_hash}")

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
                "pretty",
            ],
            timeout=120,
        ).stdout
        if observed_cell(result, "k") != ".K":
            raise GateError(f"{case['id']} did not halt: {result}")
        program = observed_cell(result, "currentBody")
        block_count = len(re.findall(r"ListItem\(basicBlock", program))
        observed = {
            "id": str(case["id"]),
            "program": program,
            "block_count": block_count,
            "locals": observed_cell(result, "locals"),
            "return": observed_cell(result, "retVal"),
            "stack_depth": len(re.findall(r"ListItem\(StackFrame", observed_cell(result, "stack"))),
        }
        expected = {
            "block_count": int(case["expected_block_count"]),
            "locals": normalize_term(str(case["expected_locals"])),
            "return": normalize_term(str(case["expected_return"])),
            "stack_depth": int(case.get("expected_stack_depth", 0)),
        }
        if {key: observed[key] for key in expected} != expected:
            raise GateError(
                f"{case['id']} differs: expected={expected}, actual={observed}"
            )
        outcomes.append(observed)
    behavior_hash = json_sha256(outcomes)
    if behavior_hash != pins.get("behavior_sha256"):
        raise GateError(
            f"behavior hash differs: {behavior_hash}; outcomes={canonical_json(outcomes)}"
        )

    spec_path = workspace / "spec.k"
    spec_path.write_text(
        f'requires "{semantics.name}"\n\nmodule {SPEC_MODULE}\n  imports {MODULE}\n\n{claims}endmodule\n',
        encoding="utf-8",
    )
    dry = run(
        [
            k["kprove"],
            spec_path,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
            "--dry-run",
        ],
        timeout=180,
    )
    if "kore-exec" not in dry.stdout or "--prove" not in dry.stdout:
        raise GateError("proof dry run did not select the native Haskell prover")
    proof = run(
        [
            k["kprove"],
            spec_path,
            "--definition",
            definition,
            "--spec-module",
            SPEC_MODULE,
        ],
        timeout=300,
    )
    if proof.stdout.strip() != "#Top":
        raise GateError(f"KMIR claim did not close: {proof.stdout.strip()}")
    return len(outcomes), 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--java-reference",
        action="store_true",
        help="run the deferred K toolchain behavior comparison and proof",
    )
    arguments = parser.parse_args()
    try:
        pins = load_toml(PINS_PATH)
        corpus = load_toml(CORPUS_PATH)
        environment = preflight(pins, corpus)
        with tempfile.TemporaryDirectory(prefix="krs-kmir-", dir="/var/tmp") as temporary:
            workspace = Path(temporary)
            krs, compiler, runner = rust_gate(environment)
            artifacts = artifact_gate(workspace, krs, pins, environment)
            definition = compile_native_definition(
                workspace, artifacts, compiler, pins, environment
            )
            executions = k_rust_gate(runner, definition, pins, corpus, environment)
            proofs = 0
            if arguments.java_reference:
                k_version = str(table(pins.get("k"), "pins.k")["version"])
                k = {name: k_tool(name, k_version) for name in ("kompile", "krun", "kprove")}
                reference_executions, proofs = java_reference_gate(
                    workspace, artifacts, k, pins, corpus
                )
                if reference_executions != executions:
                    raise GateError("K-Rust and reference execution counts differ")
        proof_status = (
            f"{proofs} reference proof" if arguments.java_reference else "1 reference proof deferred to --java-reference"
        )
        print(
            f"PASS readable KMIR operational slice: {DESCRIPTORS} descriptors; "
            f"{executions} K-Rust executions; {proof_status}; protocol "
            f"{pins['schemas']['descriptor_protocol']}"
        )
        return 0
    except (GateError, OSError) as error:
        print(f"FAIL readable KMIR operational slice: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
