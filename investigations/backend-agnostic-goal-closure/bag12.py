#!/usr/bin/env python3
"""BAG-12 typed oracle-kind schemas, fixtures, and zero-backend semantics.

This module is deliberately backend-free.  The refresh half only builds the
reviewed finite JSON/byte fixtures; the verification half only resolves those
fixtures and runs the frozen portable algorithms below.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Callable


KINDS = (
    "exit-stop", "final-result", "concrete-output", "reachability",
    "execution-pattern", "structured-predicate",
)
REGISTRY = {
    "exit-stop": (("terminal-class-and-declared-exit-v1", "exact-terminal-class-and-exit-v1"),),
    "final-result": (
        ("whole-portable-term-v1", "exact-portable-term-v1"),
        ("selected-term-paths-v1", "exact-ordered-path-values-v1"),
    ),
    "concrete-output": (
        ("ordered-output-bytes-v1", "exact-ordered-output-bytes-v1"),
        ("ordered-output-utf8-lines-v1", "exact-ordered-output-utf8-lines-v1"),
    ),
    "reachability": (("reachability-truth-v1", "exact-reachability-truth-v1"),),
    "execution-pattern": (
        ("pattern-outcome-v1", "exact-pattern-outcome-v1"),
        ("pattern-outcome-bindings-v1", "exact-pattern-outcome-bindings-v1"),
    ),
    "structured-predicate": (("predicate-bool-v1", "exact-predicate-bool-v1"),),
}
PROJECTION_IDS = tuple(pair[0] for pairs in REGISTRY.values() for pair in pairs)
COMPARATOR_IDS = tuple(pair[1] for pairs in REGISTRY.values() for pair in pairs)
NEW_ROLES = (
    "baseline-oracle-gate-result", "oracle-comparison-result", "oracle-declaration",
    "oracle-evaluator-conformance", "oracle-operand", "corpus-manifest",
    "oracle-projection-source", "oracle-projection-plan", "oracle-projection-query",
    "oracle-comparison-spec", "oracle-conformance-suite", "predicate-conformance-table",
    "predicate-plan", "predicate-query", "predicate-source", "reachability-conformance-table",
    "reachability-plan", "reachability-query", "reachability-source", "reachability-witness",
    "semantic-output-bytes", "semantic-output-finite-table",
)
OBSOLETE_ORACLE_ROLES = {"oracle-comparison", "oracle-projection", "oracle-value"}


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def digest(domain: str, value: Any) -> str:
    return hashlib.sha256(domain.encode("ascii") + b"\0" + canonical(value).encode("utf-8")).hexdigest()


def raw_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def without(value: dict[str, Any], *fields: str) -> dict[str, Any]:
    result = deepcopy(value)
    for field in fields:
        result.pop(field, None)
    return result


def key(role: str, artifact_digest: str) -> dict[str, str]:
    return {"role": role, "digest": artifact_digest}


def typed_key(role: str) -> dict[str, Any]:
    return {
        "type": "object", "additionalProperties": False, "required": ["role", "digest"],
        "properties": {"role": {"const": role}, "digest": {"$ref": "common.schema.json#/$defs/digest"}},
    }


def obj(required: list[str], properties: dict[str, Any], *, extra: dict[str, Any] | None = None) -> dict[str, Any]:
    value: dict[str, Any] = {"type": "object", "additionalProperties": False, "required": required, "properties": properties}
    if extra:
        value.update(extra)
    return value


def nullable(schema: dict[str, Any]) -> dict[str, Any]:
    return {"oneOf": [schema, {"type": "null"}]}


def array(schema: dict[str, Any], *, minimum: int | None = None, unique: bool = False) -> dict[str, Any]:
    value: dict[str, Any] = {"type": "array", "items": schema}
    if minimum is not None:
        value["minItems"] = minimum
    if unique:
        value["uniqueItems"] = True
    return value


DIGEST_REF = {"$ref": "common.schema.json#/$defs/digest"}
TERM_REF = {"$ref": "common.schema.json#/$defs/term"}
PATH_REF = {"$ref": "common.schema.json#/$defs/path"}
BINDING_REF = {"$ref": "common.schema.json#/$defs/binding"}
ARTIFACT_REF = {"$ref": "common.schema.json#/$defs/artifactKey"}


def oracle_schema() -> dict[str, Any]:
    variable = obj(["name", "sort"], {
        "name": {"type": "string", "pattern": "^[A-Z][A-Za-z0-9_]*$"},
        "sort": {"type": "string", "minLength": 1},
    })
    path_value = obj(["path", "sort", "value"], {
        "path": PATH_REF, "sort": {"type": "string", "minLength": 1}, "value": TERM_REF,
    })
    channel_value = obj(["name", "mediaType", "contentSha256", "bytesArtifact", "text"], {
        "name": {"type": "string", "minLength": 1},
        "mediaType": {"type": "string", "minLength": 1},
        "contentSha256": DIGEST_REF,
        "bytesArtifact": typed_key("semantic-output-bytes"),
        "text": {"type": ["string", "null"]},
    })
    tuple_binding = obj(["name", "sort", "value"], {
        "name": {"type": "string", "pattern": "^[A-Z][A-Za-z0-9_]*$"},
        "sort": {"type": "string", "minLength": 1}, "value": TERM_REF,
    })
    normalized_by_kind = {
        "exit-stop": obj(["terminalClass", "exitCode"], {
            "terminalClass": {"enum": ["normal", "stuck"]},
            "exitCode": {"oneOf": [{"type": "integer"}, {"type": "null"}]},
        }),
        "final-result": {
            "oneOf": [
                obj(["terminalState", "projection", "term"], {
                    "terminalState": typed_key("terminal-state"), "projection": {"const": "whole-portable-term-v1"}, "term": TERM_REF,
                }),
                obj(["terminalState", "projection", "paths"], {
                    "terminalState": typed_key("terminal-state"), "projection": {"const": "selected-term-paths-v1"},
                    "paths": array(path_value, minimum=1),
                }),
            ]
        },
        "concrete-output": obj(["channels"], {"channels": array(channel_value, minimum=1)}),
        "reachability": obj(["status", "witnesses"], {
            "status": {"enum": ["reached", "not-reached"]},
            "witnesses": array(typed_key("reachability-witness")),
        }),
        "execution-pattern": obj(["patternResult", "outcome", "bindingTuples"], {
            "patternResult": typed_key("pattern-result"), "outcome": {"enum": ["match", "no-match"]},
            "bindingTuples": array(array(tuple_binding)),
        }),
        "structured-predicate": obj(["query", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result"], {
            "query": typed_key("predicate-query"), "input": ARTIFACT_REF, "inputProjectionDigest": DIGEST_REF,
            "bindings": array(BINDING_REF), "bindingsDigest": DIGEST_REF, "result": {"type": "boolean"},
        }),
    }
    normalized = {"oneOf": [normalized_by_kind[kind] for kind in KINDS]}
    portable_projection = obj(["mode", "projectionId"], {
        "mode": {"const": "portable-built-in"}, "projectionId": {"enum": list(PROJECTION_IDS)},
    })
    k_projection = obj(["mode", "source", "plan", "query", "conformanceRequirement"], {
        "mode": {"const": "k-authored"}, "source": typed_key("oracle-projection-source"),
        "plan": typed_key("oracle-projection-plan"), "query": typed_key("oracle-projection-query"),
        "conformanceRequirement": {"const": "rust-proof-required"},
    })
    portable_comparison = obj(["mode", "comparatorId"], {
        "mode": {"const": "portable-built-in"}, "comparatorId": {"enum": list(COMPARATOR_IDS)},
    })
    k_comparison = obj(["mode", "comparisonArtifact", "conformanceRequirement"], {
        "mode": {"const": "k-authored"}, "comparisonArtifact": typed_key("oracle-comparison-spec"),
        "conformanceRequirement": {"const": "rust-proof-required"},
    })
    expected_side = {
        "oneOf": [
            *[
                obj(["kind", "normalizedValue"], {
                    "kind": {"const": kind}, "normalizedValue": normalized_by_kind[kind],
                })
                for kind in KINDS
            ],
            typed_key("semantic-crash"),
        ]
    }
    baseline_gate = {
        "oneOf": [
            obj(["mode"], {"mode": {"const": "reference-only"}}),
            obj(["mode", "expectedSide"], {"mode": {"const": "assert"}, "expectedSide": expected_side}),
        ]
    }
    final_config = {
        "oneOf": [
            obj(["kind", "stuckResultPolicy"], {"kind": {"const": "final-result"}, "stuckResultPolicy": {"enum": ["incomplete", "comparable"]}}),
            obj(["kind", "stuckResultPolicy", "paths"], {
                "kind": {"const": "final-result"}, "stuckResultPolicy": {"enum": ["incomplete", "comparable"]},
                "paths": array(PATH_REF, minimum=1, unique=True),
            }),
        ]
    }
    kind_config = {
        "oneOf": [
            obj(["kind", "exitCodeMode"], {"kind": {"const": "exit-stop"}, "exitCodeMode": {"enum": ["none", "declared-program-exit"]}}),
            final_config,
            obj(["kind", "channels"], {"kind": {"const": "concrete-output"}, "channels": array({"type": "string", "minLength": 1}, minimum=1, unique=True)}),
            obj(["kind", "query"], {"kind": {"const": "reachability"}, "query": typed_key("reachability-query")}),
            obj(["kind", "patternSource", "patternPlan", "patternQuery", "searchPolicy"], {
                "kind": {"const": "execution-pattern"}, "patternSource": typed_key("pattern-source"),
                "patternPlan": typed_key("pattern-plan"), "patternQuery": typed_key("pattern-query"),
                "searchPolicy": {"enum": ["exhaustive", "existential-first"]},
            }),
            obj(["kind", "query"], {"kind": {"const": "structured-predicate"}, "query": typed_key("predicate-query")}),
        ]
    }
    declaration = obj(
        ["schemaVersion", "declarationId", "testInvocationDigest", "slotOrdinal", "slotId", "oracleId", "oracleVersion", "kind",
         "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest", "boundsDigest", "baselineTerminalPolicy",
         "crashPolicy", "baselineGate", "projectionSpec", "comparisonSpec", "kindConfig"],
        {
            "schemaVersion": {"const": 1}, "declarationId": DIGEST_REF, "testInvocationDigest": DIGEST_REF,
            "slotOrdinal": {"type": "integer", "minimum": 0}, "slotId": {"type": "string", "pattern": "^[a-z0-9]+(?:-[a-z0-9]+)*$"},
            "oracleId": {"type": "string", "minLength": 1}, "oracleVersion": {"const": 1}, "kind": {"enum": list(KINDS)},
            "compatibilityProfileDigest": DIGEST_REF, "executionProfileDigest": DIGEST_REF, "solverProfileDigest": DIGEST_REF,
            "boundsDigest": DIGEST_REF, "baselineTerminalPolicy": {"enum": ["normal-only", "normal-or-stuck", "normal-or-crash", "normal-stuck-or-crash"]},
            "crashPolicy": {"enum": ["semantic-crash-distinguishes", "semantic-crash-incomparable"]},
            "baselineGate": baseline_gate, "projectionSpec": {"oneOf": [portable_projection, k_projection]},
            "comparisonSpec": {"oneOf": [portable_comparison, k_comparison]}, "kindConfig": kind_config,
        },
    )
    subject = {
        "oneOf": [
            obj(["side", "definitionDigest"], {"side": {"const": "baseline"}, "definitionDigest": DIGEST_REF}),
            obj(["side", "baselineDefinitionDigest", "mutantId", "mutantDefinitionDigest"], {
                "side": {"const": "mutant"}, "baselineDefinitionDigest": DIGEST_REF, "mutantId": DIGEST_REF,
                "mutantDefinitionDigest": DIGEST_REF,
            }),
        ]
    }
    terminal_evidence = obj(["kind", "terminal", "producerTrace"], {
        "kind": {"const": "execution-terminal"},
        "producerTrace": typed_key("event-trace"),
        "terminal": {
            "oneOf": [
                obj(["kind", "artifact"], {"kind": {"const": "normal"}, "artifact": typed_key("terminal-state")}),
                obj(["kind", "artifact"], {"kind": {"const": "stuck"}, "artifact": typed_key("terminal-state")}),
            ]
        },
    })
    output_row = obj(["rowId", "declaration", "testInvocationDigest", "subject", "terminal", "producerTrace", "channels"], {
        "rowId": DIGEST_REF, "declaration": typed_key("oracle-declaration"),
        "testInvocationDigest": DIGEST_REF, "subject": subject,
        "terminal": terminal_evidence["properties"]["terminal"], "producerTrace": typed_key("event-trace"),
        "channels": array(channel_value, minimum=1),
    })
    output_table = obj(["schemaVersion", "tableId", "rows"], {
        "schemaVersion": {"const": 1}, "tableId": DIGEST_REF, "rows": array(output_row, minimum=1),
    })
    completion = {
        "oneOf": [
            terminal_evidence,
            obj(["kind", "table", "rowId"], {
                "kind": {"const": "semantic-output-finite-row"},
                "table": typed_key("semantic-output-finite-table"), "rowId": DIGEST_REF,
            }),
            obj(["kind", "patternResult"], {"kind": {"const": "pattern-result"}, "patternResult": typed_key("pattern-result")}),
            obj(["kind", "table", "query", "inputVectorDigest", "producerTraces"], {
                "kind": {"const": "reachability-finite-row"}, "table": typed_key("reachability-conformance-table"),
                "query": typed_key("reachability-query"), "inputVectorDigest": DIGEST_REF,
                "producerTraces": array(typed_key("event-trace"), minimum=1),
            }),
            obj(["kind", "table", "query", "input", "bindingsDigest", "producerTrace"], {
                "kind": {"const": "predicate-finite-row"}, "table": typed_key("predicate-conformance-table"),
                "query": typed_key("predicate-query"), "input": ARTIFACT_REF, "bindingsDigest": DIGEST_REF,
                "producerTrace": typed_key("event-trace"),
            }),
        ]
    }
    operand = obj(
        ["schemaVersion", "operandId", "declaration", "subject", "testInvocationDigest", "compatibilityProfileDigest",
         "executionProfileDigest", "solverProfileDigest", "completionEvidence", "normalizedValue"],
        {
            "schemaVersion": {"const": 1}, "operandId": DIGEST_REF, "declaration": typed_key("oracle-declaration"),
            "subject": subject, "testInvocationDigest": DIGEST_REF, "compatibilityProfileDigest": DIGEST_REF,
            "executionProfileDigest": DIGEST_REF, "solverProfileDigest": DIGEST_REF,
            "completionEvidence": completion, "normalizedValue": normalized,
        },
    )
    comparison_side = obj(["side", "normalOperand", "semanticCrash"], {
        "side": {"enum": ["baseline", "mutant"]}, "normalOperand": nullable(typed_key("oracle-operand")),
        "semanticCrash": nullable(typed_key("semantic-crash")),
    }, extra={"oneOf": [
        {"properties": {"normalOperand": typed_key("oracle-operand"), "semanticCrash": {"type": "null"}}},
        {"properties": {"normalOperand": {"type": "null"}, "semanticCrash": typed_key("semantic-crash")}},
    ]})
    sides = {
        "type": "array", "prefixItems": [
            {"allOf": [{"$ref": "#/$defs/comparisonSide"}, {"properties": {"side": {"const": "baseline"}}}]},
            {"allOf": [{"$ref": "#/$defs/comparisonSide"}, {"properties": {"side": {"const": "mutant"}}}]},
        ], "items": False, "minItems": 2, "maxItems": 2,
    }
    comparison = obj(
        ["schemaVersion", "comparisonId", "declaration", "sides", "projectionId", "comparatorId", "normalizedValueDigests", "outcome"],
        {
            "schemaVersion": {"const": 1}, "comparisonId": DIGEST_REF, "declaration": typed_key("oracle-declaration"),
            "sides": sides, "projectionId": {"oneOf": [{"enum": list(PROJECTION_IDS)}, {"type": "string", "pattern": "^k-authored-projection:[0-9a-f]{64}$"}]},
            "comparatorId": {"oneOf": [{"enum": list(COMPARATOR_IDS)}, {"type": "string", "pattern": "^k-authored-comparator:[0-9a-f]{64}$"}]},
            "normalizedValueDigests": {"type": "array", "prefixItems": [nullable(DIGEST_REF), nullable(DIGEST_REF)], "items": False, "minItems": 2, "maxItems": 2},
            "outcome": {"enum": ["agree", "distinguish", "incomparable"]},
        },
    )
    gate = obj(["schemaVersion", "gateResultId", "declaration", "actualSide", "assertionOutcome", "status", "failure"], {
        "schemaVersion": {"const": 1}, "gateResultId": DIGEST_REF, "declaration": typed_key("oracle-declaration"),
        "actualSide": {"allOf": [{"$ref": "#/$defs/comparisonSide"}, {"properties": {"side": {"const": "baseline"}}}]},
        "assertionOutcome": nullable({"enum": ["agree", "distinguish", "incomparable"]}),
        "status": {"enum": ["accepted", "error"]}, "failure": nullable({"$ref": "common.schema.json#/$defs/baselineOracleGateFailure"}),
    })
    conformance_common = {
        "schemaVersion": {"const": 1}, "conformanceId": DIGEST_REF,
        "operationKind": {"enum": ["projection", "comparison", "reachability-query", "predicate-query"]},
        "source": ARTIFACT_REF, "plan": ARTIFACT_REF, "query": ARTIFACT_REF, "comparisonArtifact": ARTIFACT_REF,
        "compilerId": {"type": "string", "minLength": 1}, "compilerVersion": {"type": "string", "minLength": 1},
        "evaluatorId": {"type": "string", "minLength": 1}, "evaluatorVersion": {"type": "string", "minLength": 1},
        "compatibilityProfileDigest": DIGEST_REF, "executionProfileDigest": DIGEST_REF, "solverProfileDigest": DIGEST_REF,
        "conformanceSuite": typed_key("oracle-conformance-suite"), "result": {"enum": ["conformant", "nonconformant"]},
    }
    common_required = ["schemaVersion", "conformanceId", "operationKind", "compilerId", "compilerVersion", "evaluatorId", "evaluatorVersion",
                       "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest", "conformanceSuite", "result"]
    projection_properties = deepcopy(conformance_common)
    projection_properties.update({"operationKind": {"const": "projection"}, "source": typed_key("oracle-projection-source"),
                                  "plan": typed_key("oracle-projection-plan"), "query": typed_key("oracle-projection-query")})
    projection_conformance = obj(common_required + ["source", "plan", "query"], projection_properties)
    reachability_properties = deepcopy(conformance_common)
    reachability_properties.update({"operationKind": {"const": "reachability-query"}, "source": typed_key("reachability-source"),
                                    "plan": typed_key("reachability-plan"), "query": typed_key("reachability-query")})
    reachability_conformance = obj(common_required + ["source", "plan", "query"], reachability_properties)
    predicate_properties = deepcopy(conformance_common)
    predicate_properties.update({"operationKind": {"const": "predicate-query"}, "source": typed_key("predicate-source"),
                                 "plan": typed_key("predicate-plan"), "query": typed_key("predicate-query")})
    predicate_conformance = obj(common_required + ["source", "plan", "query"], predicate_properties)
    comparison_properties = deepcopy(conformance_common)
    comparison_properties.update({"operationKind": {"const": "comparison"}, "comparisonArtifact": typed_key("oracle-comparison-spec")})
    second = obj(common_required + ["comparisonArtifact"], comparison_properties)
    conformance = {"oneOf": [projection_conformance, reachability_conformance, predicate_conformance, second]}
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/oracle-semantics.schema.json",
        "title": "Typed oracle declarations, operands, comparisons, gates, and evaluator authority v1",
        "oneOf": [{"$ref": f"#/$defs/{name}"} for name in ("declaration", "operand", "comparison", "baselineGateResult", "evaluatorConformance", "outputFiniteTable")],
        "$defs": {
            "oracleKind": {"enum": list(KINDS)}, "variable": variable, "normalizedValue": normalized,
            "declarationKey": typed_key("oracle-declaration"), "operandKey": typed_key("oracle-operand"),
            "crashKey": typed_key("semantic-crash"), "comparisonSide": comparison_side,
            "declaration": declaration, "operand": operand, "comparison": comparison,
            "baselineGateResult": gate, "evaluatorConformance": conformance, "outputFiniteTable": output_table,
        },
    }


def reachability_schema() -> dict[str, Any]:
    variable = obj(["name", "sort"], {"name": {"type": "string", "pattern": "^[A-Z][A-Za-z0-9_]*$"}, "sort": {"type": "string", "minLength": 1}})
    subject = {"oneOf": [
        obj(["side", "definitionDigest"], {"side": {"const": "baseline"}, "definitionDigest": DIGEST_REF}),
        obj(["side", "baselineDefinitionDigest", "mutantId", "mutantDefinitionDigest"], {
            "side": {"const": "mutant"}, "baselineDefinitionDigest": DIGEST_REF,
            "mutantId": DIGEST_REF, "mutantDefinitionDigest": DIGEST_REF,
        }),
    ]}
    plan = obj(["schemaVersion", "planId", "variables", "statePattern", "sideCondition"], {
        "schemaVersion": {"const": 1}, "planId": DIGEST_REF, "variables": array(variable, unique=True), "statePattern": TERM_REF,
        "sideCondition": nullable(typed_key("predicate-query")),
    })
    query = obj(["schemaVersion", "queryId", "source", "plan"], {
        "schemaVersion": {"const": 1}, "queryId": DIGEST_REF, "source": typed_key("reachability-source"), "plan": typed_key("reachability-plan"),
    })
    witness = obj(["schemaVersion", "witnessId", "query", "terminalState", "bindings"], {
        "schemaVersion": {"const": 1}, "witnessId": DIGEST_REF, "query": typed_key("reachability-query"),
        "terminalState": typed_key("terminal-state"), "bindings": array(BINDING_REF),
        "pathIdentityDigest": DIGEST_REF, "replayManifest": typed_key("replay-manifest"),
    }, extra={"dependentRequired": {"pathIdentityDigest": ["replayManifest"], "replayManifest": ["pathIdentityDigest"]}})
    row = obj(["query", "testInvocationDigest", "subject", "terminalStates", "producerTraces", "finiteComplete", "inputVectorDigest", "witnesses"], {
        "query": typed_key("reachability-query"), "terminalStates": array(typed_key("terminal-state"), minimum=1),
        "testInvocationDigest": DIGEST_REF, "subject": subject,
        "producerTraces": array(typed_key("event-trace"), minimum=1),
        "finiteComplete": {"type": "boolean"}, "inputVectorDigest": DIGEST_REF,
        "witnesses": array(typed_key("reachability-witness")),
    })
    table = obj(["schemaVersion", "tableId", "rows"], {
        "schemaVersion": {"const": 1}, "tableId": DIGEST_REF, "rows": array(row, minimum=1),
    })
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/reachability-semantics.schema.json",
        "title": "Finite reachability plan, query, witness, and conformance table v1",
        "oneOf": [{"$ref": f"#/$defs/{name}"} for name in ("plan", "query", "witness", "table")],
        "$defs": {"plan": plan, "query": query, "witness": witness, "table": table},
    }


def predicate_schema() -> dict[str, Any]:
    variable = obj(["name", "sort"], {"name": {"type": "string", "pattern": "^[A-Z][A-Za-z0-9_]*$"}, "sort": {"type": "string", "minLength": 1}})
    subject = {"oneOf": [
        obj(["side", "definitionDigest"], {"side": {"const": "baseline"}, "definitionDigest": DIGEST_REF}),
        obj(["side", "baselineDefinitionDigest", "mutantId", "mutantDefinitionDigest"], {
            "side": {"const": "mutant"}, "baselineDefinitionDigest": DIGEST_REF,
            "mutantId": DIGEST_REF, "mutantDefinitionDigest": DIGEST_REF,
        }),
    ]}
    plan = obj(["schemaVersion", "planId", "inputRole", "inputSchemaDigest", "inputProjectionDigest", "variables", "resultSort", "evaluationMode"], {
        "schemaVersion": {"const": 1}, "planId": DIGEST_REF, "inputRole": {"$ref": "common.schema.json#/$defs/artifactRole"},
        "inputSchemaDigest": DIGEST_REF, "inputProjectionDigest": DIGEST_REF, "variables": array(variable, unique=True),
        "resultSort": {"const": "Bool"}, "evaluationMode": {"enum": ["finite-table-v1", "k-authored-v1"]},
    })
    query = obj(["schemaVersion", "queryId", "source", "plan"], {
        "schemaVersion": {"const": 1}, "queryId": DIGEST_REF, "source": typed_key("predicate-source"), "plan": typed_key("predicate-plan"),
    })
    row = obj(["query", "testInvocationDigest", "subject", "producerTrace", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result"], {
        "query": typed_key("predicate-query"), "input": ARTIFACT_REF, "inputProjectionDigest": DIGEST_REF,
        "testInvocationDigest": DIGEST_REF, "subject": subject, "producerTrace": typed_key("event-trace"),
        "bindings": array(BINDING_REF), "bindingsDigest": DIGEST_REF, "result": {"type": "boolean"},
    })
    table = obj(["schemaVersion", "tableId", "rows"], {
        "schemaVersion": {"const": 1}, "tableId": DIGEST_REF, "rows": array(row, minimum=1),
    })
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/predicate-semantics.schema.json",
        "title": "Structured predicate plan, query, and finite conformance table v1",
        "oneOf": [{"$ref": f"#/$defs/{name}"} for name in ("plan", "query", "table")],
        "$defs": {"plan": plan, "query": query, "table": table},
    }


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def manifest_schema() -> dict[str, Any]:
    test = obj(
        ["testId", "programDigest", "parserDigest", "startSymbol", "optionsDigest", "boundsDigest", "invocationDigest", "patternQueries", "oracleDeclarations"],
        {
            "testId": {"type": "string", "minLength": 1}, "programDigest": DIGEST_REF, "parserDigest": DIGEST_REF,
            "startSymbol": {"type": "string", "minLength": 1}, "optionsDigest": DIGEST_REF, "boundsDigest": DIGEST_REF,
            "invocationDigest": DIGEST_REF, "patternQueries": array({"$ref": "common.schema.json#/$defs/patternQueryRoot"}),
            "oracleDeclarations": array(typed_key("oracle-declaration"), minimum=1),
        },
    )
    lowering = {
        "oneOf": [typed_key("lowering-cycle-proof"), typed_key("lowering-proof-check-receipt")]
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/mutation-manifest.schema.json",
        "title": "Mutation campaign input manifest with ordered typed oracle declarations v1",
        "type": "object", "additionalProperties": False,
        "required": ["schemaVersion", "manifestId", "artifactCatalogDigest", "definitionDigest", "operatorDigest", "siteRegistryDigest",
                     "corpusManifestDigest", "loweringProfileDigest", "loweringEvidence", "tests"],
        "properties": {
            "schemaVersion": {"const": 1}, "manifestId": DIGEST_REF, "artifactCatalogDigest": DIGEST_REF,
            "definitionDigest": DIGEST_REF, "operatorDigest": DIGEST_REF, "siteRegistryDigest": DIGEST_REF,
            "corpusManifestDigest": DIGEST_REF, "loweringProfileDigest": DIGEST_REF,
            "loweringEvidence": array(lowering, unique=True), "tests": array(test, minimum=1),
        },
    }


def patch_campaign_schema(path: Path) -> None:
    document = read_json(path)
    baseline = document["properties"]["baseline"]
    baseline["required"] = ["oracleGateResults" if value == "oracleResults" else value for value in baseline["required"]]
    baseline["properties"].pop("oracleResults", None)
    baseline["properties"]["oracleGateResults"] = {"type": "array", "items": typed_key("baseline-oracle-gate-result")}
    declaration_array = array(typed_key("oracle-declaration"), minimum=1)
    baseline_test = document["$defs"]["baselineTest"]
    baseline_test["required"] = ["oracleDeclarations" if value == "oracleIds" else value for value in baseline_test["required"]]
    baseline_test["properties"].pop("oracleIds", None)
    baseline_test["properties"]["oracleDeclarations"] = declaration_array
    mutant_test = document["$defs"]["mutant"]["properties"]["tests"]["items"]
    mutant_test["required"] = ["oracleDeclarations" if value == "oracleIds" else value for value in mutant_test["required"]]
    mutant_test["properties"].pop("oracleIds", None)
    mutant_test["properties"]["oracleDeclarations"] = declaration_array
    outer_side = nullable({"$ref": "oracle-semantics.schema.json#/$defs/comparisonSide"})
    failure_wrapper = {"oneOf": [
        obj(["sourceSide", "failure"], {"sourceSide": {"const": "baseline-execution"}, "failure": {"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}}),
        obj(["sourceSide", "failure"], {"sourceSide": {"const": "baseline-operand-production"}, "failure": {"$ref": "common.schema.json#/$defs/oracleOperandProductionFailure"}}),
        obj(["sourceSide", "failure"], {"sourceSide": {"const": "mutant-execution"}, "failure": {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}}),
        obj(["sourceSide", "failure"], {"sourceSide": {"const": "mutant-operand-production"}, "failure": {"$ref": "common.schema.json#/$defs/oracleOperandProductionFailure"}}),
        obj(["sourceSide", "failure"], {"sourceSide": {"const": "comparison"}, "failure": {"$ref": "common.schema.json#/$defs/oracleComparisonFailure"}}),
    ]}
    outer = obj(["declaration", "outcome", "baselineSide", "mutantSide", "comparison", "failure"], {
        "declaration": typed_key("oracle-declaration"),
        "outcome": {"enum": ["agree", "distinguish", "incomparable", "timeout", "unknown", "error", "skipped"]},
        "baselineSide": outer_side, "mutantSide": outer_side,
        "comparison": nullable(typed_key("oracle-comparison-result")), "failure": nullable(failure_wrapper),
    })
    document["$defs"]["oracleResult"] = outer
    for obsolete in ("baselineOracleResult", "operandTerminal", "oracleFailure", "oracleContextFailure"):
        document["$defs"].pop(obsolete, None)
    write_json(path, document)


def patch_policy_schema(path: Path) -> None:
    document = read_json(path)
    # BAG-14 retired the suite-level cacheKey.  Oracle identity is now carried
    # by each exact oracle-evaluation key, so BAG-12 has no policy field to
    # patch after that migration.
    if "cacheKey" not in document.get("properties", {}):
        return
    cache = document["properties"]["cacheKey"]
    if "oracleDeclarations" not in cache["required"]:
        cache["required"].insert(cache["required"].index("oracleManifestDigest"), "oracleDeclarations")
    cache["properties"]["oracleDeclarations"] = array(typed_key("oracle-declaration"), minimum=1)
    write_json(path, document)


def role_specs() -> dict[str, dict[str, Any]]:
    structured = {
        "oracle-declaration": ("oracle-semantics.schema.json#/$defs/declaration", "k-in-k/oracle-declaration/v1", "declarationId"),
        "oracle-operand": ("oracle-semantics.schema.json#/$defs/operand", "k-in-k/oracle-operand/v1", "operandId"),
        "oracle-comparison-result": ("oracle-semantics.schema.json#/$defs/comparison", "k-in-k/oracle-comparison-result/v1", "comparisonId"),
        "baseline-oracle-gate-result": ("oracle-semantics.schema.json#/$defs/baselineGateResult", "k-in-k/baseline-oracle-gate-result/v1", "gateResultId"),
        "oracle-evaluator-conformance": ("oracle-semantics.schema.json#/$defs/evaluatorConformance", "k-in-k/oracle-evaluator-conformance/v1", "conformanceId"),
        "reachability-plan": ("reachability-semantics.schema.json#/$defs/plan", "k-in-k/reachability-plan/v1", "planId"),
        "reachability-query": ("reachability-semantics.schema.json#/$defs/query", "k-in-k/reachability-query/v1", "queryId"),
        "reachability-witness": ("reachability-semantics.schema.json#/$defs/witness", "k-in-k/reachability-witness/v1", "witnessId"),
        "reachability-conformance-table": ("reachability-semantics.schema.json#/$defs/table", "k-in-k/reachability-conformance-table/v1", "tableId"),
        "predicate-plan": ("predicate-semantics.schema.json#/$defs/plan", "k-in-k/predicate-plan/v1", "planId"),
        "predicate-query": ("predicate-semantics.schema.json#/$defs/query", "k-in-k/predicate-query/v1", "queryId"),
        "predicate-conformance-table": ("predicate-semantics.schema.json#/$defs/table", "k-in-k/predicate-conformance-table/v1", "tableId"),
        "semantic-output-finite-table": ("oracle-semantics.schema.json#/$defs/outputFiniteTable", "k-in-k/semantic-output-finite-table/v1", "tableId"),
        "corpus-manifest": ("corpus-manifest.schema.json", "k-in-k/corpus-manifest/v1", "manifestId"),
    }
    return {
        role: {
            "role": role, "contentModel": "canonical-json", "mediaType": "application/json", "schema": schema,
            "digestDomain": domain, "projection": {"kind": "without-field"}, "selfIdField": identity,
        }
        for role, (schema, domain, identity) in structured.items()
    } | {
        role: {
            "role": role, "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None,
            "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None,
        }
        for role in (
            "semantic-output-bytes", "reachability-source", "predicate-source",
            "oracle-projection-source", "oracle-projection-plan", "oracle-projection-query",
            "oracle-comparison-spec", "oracle-conformance-suite",
        )
    }


def install_schemas_and_roles(root: Path) -> None:
    schemas = root / "schemas"
    write_json(schemas / "oracle-semantics.schema.json", oracle_schema())
    write_json(schemas / "reachability-semantics.schema.json", reachability_schema())
    write_json(schemas / "predicate-semantics.schema.json", predicate_schema())
    write_json(schemas / "mutation-manifest.schema.json", manifest_schema())
    patch_campaign_schema(schemas / "mutation-campaign.schema.json")
    patch_policy_schema(schemas / "mutation-execution-policy.schema.json")
    common_path = schemas / "common.schema.json"
    common = read_json(common_path)
    # The three BAG-09 roles remain registered solely so immutable historical
    # execution-catalog snapshots stay schema-valid.  The active BAG-12
    # catalog and every live manifest/result exclude them.
    roles = set(common["$defs"]["artifactRole"]["enum"]) | OBSOLETE_ORACLE_ROLES | set(NEW_ROLES)
    common["$defs"]["artifactRole"]["enum"] = sorted(roles)
    write_json(common_path, common)
    specs_path = root / "artifact-role-specs.json"
    specs = read_json(specs_path)
    by_role = {item["role"]: item for item in specs["specs"]}
    by_role.update({
        "oracle-comparison": {"role": "oracle-comparison", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        "oracle-projection": {"role": "oracle-projection", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        "oracle-value": {"role": "oracle-value", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "oracle-value.schema.json", "digestDomain": "k-in-k/oracle-value/v1", "projection": {"kind": "without-field"}, "selfIdField": "oracleValueDigest"},
    })
    by_role.update(role_specs())
    specs["specs"] = [by_role[role] for role in sorted(by_role)]
    write_json(specs_path, specs)


def fixture_registry(fixtures: Path, prefix: str, id_field: str) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for path in sorted(fixtures.glob(f"{prefix}*.json")):
        value = read_json(path)
        if id_field in value:
            result[value[id_field]] = value
    return result


def prepare_refresh(root: Path) -> None:
    """Convert a previous BAG-12 result to the old in-process build seed.

    The historical refresh body is still responsible for BAG-06..11 and 13.
    This reversible seed conversion lets that body run twice; finalize_refresh
    replaces the seed before the refresh exits, so no global join is published.
    """
    fixtures = root / "fixtures"
    manifest_path = fixtures / "mutation-manifest.json"
    manifest = read_json(manifest_path)
    if "oracles" in manifest:
        return
    declarations = fixture_registry(fixtures, "oracle-declaration-", "declarationId")
    operands = fixture_registry(fixtures, "oracle-operand-", "operandId")
    gates = fixture_registry(fixtures, "baseline-oracle-gate-", "gateResultId")
    comparisons = fixture_registry(fixtures, "oracle-comparison-", "comparisonId")
    flattened: list[dict[str, Any]] = []
    for test in manifest["tests"]:
        test["oracleIds"] = []
        for declaration_key in test.pop("oracleDeclarations"):
            declaration = declarations[declaration_key["digest"]]
            test["oracleIds"].append(declaration["oracleId"])
            flattened.append(declaration)
    old_oracles = []
    for declaration in flattened:
        projection_id = declaration["projectionSpec"].get("projectionId", canonical(declaration["projectionSpec"]))
        comparator_id = declaration["comparisonSpec"].get("comparatorId", canonical(declaration["comparisonSpec"]))
        old = {
            "oracleId": declaration["oracleId"], "version": 1, "kind": declaration["kind"],
            "projectionDigest": raw_sha256(projection_id.encode("utf-8")), "comparisonDigest": raw_sha256(comparator_id.encode("utf-8")),
            "crashPolicy": declaration["crashPolicy"],
            "baselineTerminalPolicy": "normal-required" if declaration["baselineTerminalPolicy"] == "normal-only" else "semantic-crash-allowed",
            "artifacts": [],
        }
        old["artifacts"] = [key("oracle-projection", old["projectionDigest"]), key("oracle-comparison", old["comparisonDigest"])]
        if declaration["kind"] == "execution-pattern":
            config = declaration["kindConfig"]
            old.update({name: deepcopy(config[name]) for name in ("patternSource", "patternPlan", "patternQuery")})
        old_oracles.append(old)
    manifest["oracles"] = old_oracles
    write_json(manifest_path, manifest)

    campaign_path = fixtures / "mutation-campaign.json"
    campaign = read_json(campaign_path)
    declaration_by_digest = declarations
    for test in campaign["baseline"]["tests"]:
        test["oracleIds"] = [declaration_by_digest[item["digest"]]["oracleId"] for item in test.pop("oracleDeclarations")]
    baseline_results = []
    for gate_key in campaign["baseline"].pop("oracleGateResults"):
        gate = gates[gate_key["digest"]]
        declaration = declarations[gate["declaration"]["digest"]]
        side = gate["actualSide"]
        artifact = None
        if side["normalOperand"] is not None:
            operand = operands[side["normalOperand"]["digest"]]
            if declaration["kind"] == "execution-pattern":
                artifact = operand["normalizedValue"]["patternResult"]
            else:
                legacy_value = read_json(fixtures / "oracle-value-baseline.json")
                artifact = key("oracle-value", legacy_value["oracleValueDigest"])
            terminal = {"kind": "normal", "artifact": artifact}
        else:
            terminal = {"kind": "semantic-crash", "artifact": side["semanticCrash"]}
        baseline_results.append({
            "oracleId": declaration["oracleId"], "kind": declaration["kind"],
            "projectionDigest": raw_sha256(str(declaration["projectionSpec"]).encode()),
            "comparisonDigest": raw_sha256(str(declaration["comparisonSpec"]).encode()),
            "outcome": "accepted" if gate["status"] == "accepted" else "error",
            "operand": {"side": "baseline", "terminal": terminal}, "failure": None,
        })
    campaign["baseline"]["oracleResults"] = baseline_results
    for mutant in campaign["mutants"]:
        for test in mutant["tests"]:
            test["oracleIds"] = [declaration_by_digest[item["digest"]]["oracleId"] for item in test.pop("oracleDeclarations")]
        old_results = []
        for result in mutant["oracleResults"]:
            declaration = declarations[result["declaration"]["digest"]]
            terminals = []
            for side_name, side in (("baseline", result["baselineSide"]), ("mutant", result["mutantSide"])):
                if side is None:
                    terminal = None
                elif side["semanticCrash"] is not None:
                    terminal = {"kind": "semantic-crash", "artifact": side["semanticCrash"]}
                elif declaration["kind"] == "execution-pattern":
                    operand = operands[side["normalOperand"]["digest"]]
                    terminal = {"kind": "normal", "artifact": operand["normalizedValue"]["patternResult"]}
                else:
                    legacy = read_json(fixtures / f"oracle-value-{'baseline' if side_name == 'baseline' else 'mutant'}.json")
                    terminal = {"kind": "normal", "artifact": key("oracle-value", legacy["oracleValueDigest"])}
                terminals.append({"side": side_name, "terminal": terminal})
            old_results.append({
                "oracleId": declaration["oracleId"], "kind": declaration["kind"],
                "projectionDigest": raw_sha256(str(declaration["projectionSpec"]).encode()),
                "comparisonDigest": raw_sha256(str(declaration["comparisonSpec"]).encode()),
                "outcome": result["outcome"], "operands": terminals, "witnessDigest": None, "failure": result["failure"],
            })
        mutant["oracleResults"] = old_results
    write_json(campaign_path, campaign)


def self_identify(value: dict[str, Any], field: str, domain: str) -> dict[str, Any]:
    value[field] = digest(domain, without(value, field))
    return value


def declaration_for(test: dict[str, Any], corpus: dict[str, Any], slot: int, slot_id: str, oracle_id: str,
                    kind: str, projection_id: str, comparator_id: str, config: dict[str, Any],
                    *, gate: dict[str, Any] | None = None, terminal_policy: str = "normal-only",
                    crash_policy: str = "semantic-crash-distinguishes") -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "declarationId": "0" * 64, "testInvocationDigest": test["invocationDigest"],
        "slotOrdinal": slot, "slotId": slot_id, "oracleId": oracle_id, "oracleVersion": 1, "kind": kind,
        "compatibilityProfileDigest": corpus["compatibilityProfileDigest"],
        "executionProfileDigest": corpus["executionProfileDigest"], "solverProfileDigest": corpus["solverProfileDigest"],
        "boundsDigest": test["boundsDigest"], "baselineTerminalPolicy": terminal_policy, "crashPolicy": crash_policy,
        "baselineGate": gate or {"mode": "reference-only"},
        "projectionSpec": {"mode": "portable-built-in", "projectionId": projection_id},
        "comparisonSpec": {"mode": "portable-built-in", "comparatorId": comparator_id}, "kindConfig": config,
    }
    return self_identify(value, "declarationId", "k-in-k/oracle-declaration/v1")


def operand_for(declaration: dict[str, Any], subject: dict[str, Any], completion: dict[str, Any], normalized: dict[str, Any]) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "operandId": "0" * 64, "declaration": key("oracle-declaration", declaration["declarationId"]),
        "subject": subject, "testInvocationDigest": declaration["testInvocationDigest"],
        "compatibilityProfileDigest": declaration["compatibilityProfileDigest"],
        "executionProfileDigest": declaration["executionProfileDigest"], "solverProfileDigest": declaration["solverProfileDigest"],
        "completionEvidence": completion, "normalizedValue": normalized,
    }
    return self_identify(value, "operandId", "k-in-k/oracle-operand/v1")


def side(side_name: str, operand: dict[str, Any] | None = None, crash: dict[str, str] | None = None) -> dict[str, Any]:
    return {
        "side": side_name, "normalOperand": None if operand is None else key("oracle-operand", operand["operandId"]),
        "semanticCrash": crash,
    }


def normalized_digest(declaration: dict[str, Any], normalized: dict[str, Any]) -> str:
    projection_id = declaration["projectionSpec"].get("projectionId")
    if projection_id is None:
        projection_id = "k-authored-projection:" + declaration["projectionSpec"]["query"]["digest"]
    return digest("k-in-k/oracle-normalized-value/v1", {
        "kind": declaration["kind"], "projectionId": projection_id, "normalizedValue": normalized,
    })


def comparison_for(declaration: dict[str, Any], left: dict[str, Any], right: dict[str, Any], outcome: str,
                   operands: dict[str, dict[str, Any]]) -> dict[str, Any]:
    projection_id = declaration["projectionSpec"].get("projectionId", "k-authored-projection:" + declaration["projectionSpec"].get("query", {"digest": "0" * 64})["digest"])
    comparator_id = declaration["comparisonSpec"].get("comparatorId", "k-authored-comparator:" + declaration["comparisonSpec"].get("comparisonArtifact", {"digest": "0" * 64})["digest"])
    digests = []
    for item in (left, right):
        digests.append(None if item["normalOperand"] is None else normalized_digest(declaration, operands[item["normalOperand"]["digest"]]["normalizedValue"]))
    value = {
        "schemaVersion": 1, "comparisonId": "0" * 64, "declaration": key("oracle-declaration", declaration["declarationId"]),
        "sides": [left, right], "projectionId": projection_id, "comparatorId": comparator_id,
        "normalizedValueDigests": digests, "outcome": outcome,
    }
    return self_identify(value, "comparisonId", "k-in-k/oracle-comparison-result/v1")


def gate_for(declaration: dict[str, Any], actual: dict[str, Any], status: str = "accepted",
             assertion: str | None = None, failure: dict[str, Any] | None = None) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "gateResultId": "0" * 64, "declaration": key("oracle-declaration", declaration["declarationId"]),
        "actualSide": actual, "assertionOutcome": assertion, "status": status, "failure": failure,
    }
    return self_identify(value, "gateResultId", "k-in-k/baseline-oracle-gate-result/v1")


def binding_tuple(result: dict[str, Any], plan: dict[str, Any]) -> list[list[dict[str, Any]]]:
    variables = [item["name"] for item in plan["variables"]]
    tuples = []
    for witness in result["witnesses"]:
        by_name = {binding["name"]: binding["term"] for binding in witness["bindings"]}
        tuples.append([{"name": name, "sort": by_name[name]["sort"], "value": by_name[name]} for name in variables])
    tuples.sort(key=lambda item: (digest("k-in-k/pattern-oracle-binding-tuple/v1", item), canonical(item)))
    return tuples


def opaque_record(role: str, file_name: str, content: bytes) -> tuple[dict[str, str], dict[str, Any]]:
    content_hash = raw_sha256(content)
    artifact_digest = digest("k-in-k/opaque-artifact/v1", {"role": role, "mediaType": "application/octet-stream", "contentSha256": content_hash})
    return key(role, artifact_digest), {
        "role": role, "digest": artifact_digest, "contentModel": "opaque-bytes", "mediaType": "application/octet-stream",
        "contentSha256": content_hash, "availability": "bundled",
        "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{file_name}", "resolverId": "repo-v1",
    }


def structured_catalog_entry(root: Path, role: str, artifact_digest: str, value: dict[str, Any], file_name: str) -> dict[str, Any]:
    data = canonical(value).encode("utf-8")
    (root / "material" / file_name).write_bytes(data)
    return {
        "role": role, "digest": artifact_digest, "contentModel": "canonical-json", "mediaType": "application/json",
        "contentSha256": raw_sha256(data), "availability": "bundled",
        "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{file_name}", "resolverId": "repo-v1",
    }


def subject_definition(subject: dict[str, Any]) -> str:
    return subject["definitionDigest"] if subject["side"] == "baseline" else subject["mutantDefinitionDigest"]


def trace_digest(trace: dict[str, Any]) -> str:
    return digest("k-in-k/event-trace/v1", trace)


def refresh_trace(trace: dict[str, Any]) -> dict[str, Any]:
    trace["pathIdentityDigest"] = digest(
        "k-in-k/unkeyed-path/v1", without(trace, "pathOrdinal", "pathKey", "pathIdentityDigest")
    )
    return trace


def build_finite_authority(
    root: Path,
    test: dict[str, Any],
    subjects: dict[str, dict[str, Any]],
    terminals: dict[str, dict[str, Any]],
    producer_traces: dict[str, dict[str, str]],
) -> tuple[dict[str, Any], list[tuple[str, str, dict[str, Any]]], dict[str, Any]]:
    fixtures = root / "fixtures"
    material = root / "material"
    reach_source, reach_source_entry = opaque_record("reachability-source", "reachability-source.bin", b"BAG-12 opaque K reachability source; not evaluated by Python.\n")
    pred_sources = []
    pred_source_entries = []
    for label in ("agree", "distinguish"):
        payload = f"BAG-12 opaque K predicate source ({label}); finite rows only.\n".encode("ascii")
        source, entry = opaque_record("predicate-source", f"predicate-source-{label}.bin", payload)
        (material / f"predicate-source-{label}.bin").write_bytes(payload)
        pred_sources.append(source)
        pred_source_entries.append(entry)
    (material / "reachability-source.bin").write_bytes(b"BAG-12 opaque K reachability source; not evaluated by Python.\n")
    state_sort = next(iter(terminals.values()))["value"]["sort"]
    assert all(item["value"]["sort"] == state_sort for item in terminals.values()), "finite authority inputs must share the declared STATE sort"
    terminal_schema = read_json(root / "schemas" / "terminal-state.schema.json")
    schema_digest = raw_sha256(canonical(terminal_schema).encode("utf-8"))
    projection_spec_digest = digest("k-in-k/predicate-input-projection-spec/v1", {"inputRole": "terminal-state", "inputSchemaDigest": schema_digest})
    predicate_plan = self_identify({
        "schemaVersion": 1, "planId": "0" * 64, "inputRole": "terminal-state", "inputSchemaDigest": schema_digest,
        "inputProjectionDigest": projection_spec_digest, "variables": [{"name": "STATE", "sort": state_sort}],
        "resultSort": "Bool", "evaluationMode": "finite-table-v1",
    }, "planId", "k-in-k/predicate-plan/v1")
    predicate_queries = [self_identify({
        "schemaVersion": 1, "queryId": "0" * 64, "source": source, "plan": key("predicate-plan", predicate_plan["planId"]),
    }, "queryId", "k-in-k/predicate-query/v1") for source in pred_sources]
    predicate_rows = []
    for query_index, predicate_query in enumerate(predicate_queries):
      for side_name in ("baseline", "mutant"):
        terminal = terminals[side_name]
        input_key = key("terminal-state", terminal["terminalStateDigest"])
        bindings = [{"name": "STATE", "term": deepcopy(terminal["value"])}]
        binding_digest = digest("k-in-k/bindings/v1", bindings)
        input_projection = digest("k-in-k/predicate-input-projection/v1", {
            "inputRole": "terminal-state", "inputSchemaDigest": schema_digest, "inputArtifact": input_key, "inputValue": terminal,
        })
        predicate_rows.append({
            "query": key("predicate-query", predicate_query["queryId"]), "input": input_key,
            "testInvocationDigest": test["invocationDigest"], "subject": deepcopy(subjects[side_name]),
            "producerTrace": deepcopy(producer_traces[side_name]),
            "inputProjectionDigest": input_projection, "bindings": bindings, "bindingsDigest": binding_digest,
            "result": query_index == 0 or side_name == "baseline",
        })
    predicate_rows.sort(key=lambda row: (row["query"]["digest"], row["input"]["role"], row["input"]["digest"], row["bindingsDigest"]))
    predicate_table = self_identify({"schemaVersion": 1, "tableId": "0" * 64, "rows": predicate_rows}, "tableId", "k-in-k/predicate-conformance-table/v1")

    state_variable = {"encoding": "portable-term-v1", "sort": state_sort, "node": {"kind": "variable", "name": "STATE"}}
    reached_plan = self_identify({
        "schemaVersion": 1, "planId": "0" * 64, "variables": [{"name": "STATE", "sort": state_sort}],
        "statePattern": state_variable, "sideCondition": None,
    }, "planId", "k-in-k/reachability-plan/v1")
    distinguish_plan = self_identify({
        "schemaVersion": 1, "planId": "0" * 64, "variables": [{"name": "STATE", "sort": state_sort}],
        "statePattern": state_variable, "sideCondition": key("predicate-query", predicate_queries[1]["queryId"]),
    }, "planId", "k-in-k/reachability-plan/v1")
    missing_term = {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "token", "text": "never-present"}}
    absent_plan = self_identify({
        "schemaVersion": 1, "planId": "0" * 64, "variables": [], "statePattern": missing_term, "sideCondition": None,
    }, "planId", "k-in-k/reachability-plan/v1")
    reached_query = self_identify({
        "schemaVersion": 1, "queryId": "0" * 64, "source": reach_source,
        "plan": key("reachability-plan", reached_plan["planId"]),
    }, "queryId", "k-in-k/reachability-query/v1")
    distinguish_query = self_identify({
        "schemaVersion": 1, "queryId": "0" * 64, "source": reach_source,
        "plan": key("reachability-plan", distinguish_plan["planId"]),
    }, "queryId", "k-in-k/reachability-query/v1")
    absent_query = self_identify({
        "schemaVersion": 1, "queryId": "0" * 64, "source": reach_source,
        "plan": key("reachability-plan", absent_plan["planId"]),
    }, "queryId", "k-in-k/reachability-query/v1")
    # The positive finite row deliberately contains the one terminal for which
    # this package publishes a complete witness.  Both fixture terminals have
    # the same portable value, so including both would require two distinct
    # witnesses even though their binding tuples are equal.
    witnesses = []
    rows = []
    input_digests = {}
    for query_name, query in (("agree", reached_query), ("distinguish", distinguish_query), ("absent", absent_query)):
      for side_name in ("baseline", "mutant"):
        terminal = terminals[side_name]
        terminal_keys = [key("terminal-state", terminal["terminalStateDigest"])]
        input_digest = digest("k-in-k/reachability-finite-input/v1", {"terminalStates": terminal_keys, "finiteComplete": True})
        input_digests[(query_name, side_name)] = input_digest
        matched = query_name == "agree" or query_name == "distinguish" and side_name == "baseline"
        row_witnesses = []
        if matched:
            witness = self_identify({
                "schemaVersion": 1, "witnessId": "0" * 64, "query": key("reachability-query", query["queryId"]),
                "terminalState": terminal_keys[0], "bindings": [{"name": "STATE", "term": deepcopy(terminal["value"])}],
            }, "witnessId", "k-in-k/reachability-witness/v1")
            witnesses.append(witness)
            row_witnesses = [key("reachability-witness", witness["witnessId"])]
        rows.append({
            "query": key("reachability-query", query["queryId"]), "testInvocationDigest": test["invocationDigest"],
            "subject": deepcopy(subjects[side_name]), "terminalStates": terminal_keys,
            "producerTraces": [deepcopy(producer_traces[side_name])], "finiteComplete": True,
            "inputVectorDigest": input_digest, "witnesses": row_witnesses,
        })
    rows.sort(key=lambda row: (row["query"]["digest"], row["inputVectorDigest"]))
    reach_table = self_identify({"schemaVersion": 1, "tableId": "0" * 64, "rows": rows}, "tableId", "k-in-k/reachability-conformance-table/v1")

    artifacts: list[tuple[str, str, dict[str, Any]]] = []
    named = [
        ("reachability-plan-reached.json", "reachability-plan", reached_plan["planId"], reached_plan),
        ("reachability-plan-distinguish.json", "reachability-plan", distinguish_plan["planId"], distinguish_plan),
        ("reachability-plan-not-reached.json", "reachability-plan", absent_plan["planId"], absent_plan),
        ("reachability-query-reached.json", "reachability-query", reached_query["queryId"], reached_query),
        ("reachability-query-distinguish.json", "reachability-query", distinguish_query["queryId"], distinguish_query),
        ("reachability-query-not-reached.json", "reachability-query", absent_query["queryId"], absent_query),
        ("reachability-conformance-table.json", "reachability-conformance-table", reach_table["tableId"], reach_table),
        ("predicate-plan.json", "predicate-plan", predicate_plan["planId"], predicate_plan),
        ("predicate-query-agree.json", "predicate-query", predicate_queries[0]["queryId"], predicate_queries[0]),
        ("predicate-query-distinguish.json", "predicate-query", predicate_queries[1]["queryId"], predicate_queries[1]),
        ("predicate-conformance-table.json", "predicate-conformance-table", predicate_table["tableId"], predicate_table),
    ]
    for index, witness in enumerate(witnesses):
        named.append((f"reachability-witness-{index}.json", "reachability-witness", witness["witnessId"], witness))
    for name, role, identity, value in named:
        write_json(fixtures / name, value)
        artifacts.append((role, identity, value))
    authority = {
        "reachSource": reach_source, "reachSourceEntry": reach_source_entry, "predicateSources": pred_sources,
        "predicateSourceEntries": pred_source_entries, "reachedQuery": reached_query, "distinguishQuery": distinguish_query,
        "absentQuery": absent_query, "reachTable": reach_table, "witnesses": witnesses,
        "predicateQueries": predicate_queries, "predicatePlan": predicate_plan,
        "predicateTable": predicate_table,
    }
    return authority, artifacts, {"inputVectorDigests": input_digests, "schemaDigest": schema_digest}


def output_fixtures(root: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    material = root / "material"
    entries = []
    values = []
    payloads = [
        ("semantic-output-crlf.bin", b"alpha\r\nbeta\rfinal\n"),
        ("semantic-output-lf.bin", b"alpha\nbeta\nfinal\n"),
        ("semantic-output-different.bin", b"different\n"),
        ("semantic-output-invalid-utf8.bin", b"\xff\xfe"),
    ]
    for index, (name, payload) in enumerate(payloads):
        (material / name).write_bytes(payload)
        artifact, entry = opaque_record("semantic-output-bytes", name, payload)
        entries.append(entry)
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError:
            text = None
        values.append({
            "name": "program-output", "mediaType": entry["mediaType"], "contentSha256": raw_sha256(payload),
            "bytesArtifact": artifact, "text": text,
        })
    return values, entries


def failure(stage: str, classification: str, disposition: str = "error") -> dict[str, Any]:
    retry = "same-input-after-resource-change" if classification == "solver-unknown" else "never"
    return {
        "stage": stage, "classification": classification, "context": "oracle-operand-production", "scope": "test",
        "retryability": retry, "semanticEvidence": [], "details": {"derivedDisposition": disposition},
    }


def _finalize_refresh_legacy(root: Path) -> None:
    install_schemas_and_roles(root)
    fixtures, vectors = root / "fixtures", root / "vectors"
    manifest = read_json(fixtures / "mutation-manifest.json")
    corpus = read_json(fixtures / "corpus-manifest.json")
    campaign = read_json(fixtures / "mutation-campaign.json")
    baseline_terminal = read_json(fixtures / "terminal-state.json")
    mutant_terminal = read_json(fixtures / "terminal-state-mutant.json")
    terminals = [baseline_terminal, mutant_terminal]
    baseline_definition = manifest["definitionDigest"]
    mutant = campaign["mutants"][0]
    mutant_subject = {
        "side": "mutant", "baselineDefinitionDigest": baseline_definition, "mutantId": mutant["mutantId"],
        "mutantDefinitionDigest": mutant["outputDefinitionDigest"],
    }
    baseline_subject = {"side": "baseline", "definitionDigest": baseline_definition}
    tests = {test["testId"]: test for test in manifest["tests"]}
    pattern_source = read_json(fixtures / "pattern-query-write-eventually-load.json")["patternSource"]
    pattern_plan_key = read_json(fixtures / "pattern-query-write-eventually-load.json")["patternPlan"]
    pattern_query_key = key("pattern-query", read_json(fixtures / "pattern-query-write-eventually-load.json")["queryId"])
    declarations = [
        declaration_for(tests["write-load"], corpus, 0, "final", "final", "final-result", "whole-portable-term-v1", "exact-portable-term-v1",
                        {"kind": "final-result", "stuckResultPolicy": "incomplete"}),
        declaration_for(tests["write-load"], corpus, 1, "write-load-pattern", "write-load-pattern", "execution-pattern", "pattern-outcome-v1", "exact-pattern-outcome-v1",
                        {"kind": "execution-pattern", "patternSource": pattern_source, "patternPlan": pattern_plan_key,
                         "patternQuery": pattern_query_key, "searchPolicy": "exhaustive"}),
        declaration_for(tests["write-only"], corpus, 0, "write-only-final", "write-only-final", "final-result", "whole-portable-term-v1", "exact-portable-term-v1",
                        {"kind": "final-result", "stuckResultPolicy": "incomplete"}),
    ]
    by_oracle = {(item["testInvocationDigest"], item["oracleId"]): item for item in declarations}
    structured: list[tuple[str, str, dict[str, Any], str]] = []
    for declaration in declarations:
        name = f"oracle-declaration-{declaration['slotId']}-{'write-only' if declaration['testInvocationDigest'] == tests['write-only']['invocationDigest'] else 'write-load'}.json"
        write_json(fixtures / name, declaration)
        structured.append(("oracle-declaration", declaration["declarationId"], declaration, name))

    operands: dict[str, dict[str, Any]] = {}
    sides_by_declaration: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}
    pattern_baseline = read_json(fixtures / "pattern-result.json")
    pattern_mutant = read_json(fixtures / "mutation-pattern-result.json")
    pattern_plan = read_json(fixtures / "pattern-plan-write-eventually-load.json")
    for declaration in declarations:
        is_pattern = declaration["kind"] == "execution-pattern"
        if is_pattern:
            baseline_normalized = {"patternResult": key("pattern-result", pattern_baseline["resultId"]), "outcome": pattern_baseline["outcome"], "bindingTuples": []}
            mutant_normalized = {"patternResult": key("pattern-result", pattern_mutant["resultId"]), "outcome": pattern_mutant["outcome"], "bindingTuples": []}
            baseline_completion = {"kind": "pattern-result", "patternResult": baseline_normalized["patternResult"]}
            mutant_completion = {"kind": "pattern-result", "patternResult": mutant_normalized["patternResult"]}
        else:
            baseline_normalized = {"terminalState": key("terminal-state", baseline_terminal["terminalStateDigest"]), "projection": "whole-portable-term-v1", "term": deepcopy(baseline_terminal["value"])}
            mutant_normalized = {"terminalState": key("terminal-state", mutant_terminal["terminalStateDigest"]), "projection": "whole-portable-term-v1", "term": deepcopy(mutant_terminal["value"])}
            baseline_completion = {"kind": "execution-terminal", "terminal": {"kind": "normal", "artifact": baseline_normalized["terminalState"]}}
            mutant_completion = {"kind": "execution-terminal", "terminal": {"kind": "normal", "artifact": mutant_normalized["terminalState"]}}
        left = operand_for(declaration, baseline_subject, baseline_completion, baseline_normalized)
        right = operand_for(declaration, mutant_subject, mutant_completion, mutant_normalized)
        operands[left["operandId"]] = left
        operands[right["operandId"]] = right
        sides_by_declaration[declaration["declarationId"]] = (side("baseline", left), side("mutant", right))
        suffix = "pattern" if is_pattern else ("write-only-final" if declaration["testInvocationDigest"] == tests["write-only"]["invocationDigest"] else "final")
        for side_name, operand in (("baseline", left), ("mutant", right)):
            name = f"oracle-operand-{suffix}-{side_name}.json"
            write_json(fixtures / name, operand)
            structured.append(("oracle-operand", operand["operandId"], operand, name))

    comparisons: dict[str, dict[str, Any]] = {}
    gates: dict[str, dict[str, Any]] = {}
    for declaration in declarations:
        left, right = sides_by_declaration[declaration["declarationId"]]
        outcome = "distinguish" if declaration["kind"] == "execution-pattern" else "agree"
        comparison = comparison_for(declaration, left, right, outcome, operands)
        comparisons[comparison["comparisonId"]] = comparison
        suffix = "pattern" if declaration["kind"] == "execution-pattern" else ("write-only-final" if declaration["testInvocationDigest"] == tests["write-only"]["invocationDigest"] else "final")
        comparison_name = f"oracle-comparison-{suffix}.json"
        write_json(fixtures / comparison_name, comparison)
        structured.append(("oracle-comparison-result", comparison["comparisonId"], comparison, comparison_name))
        gate = gate_for(declaration, left)
        gates[gate["gateResultId"]] = gate
        gate_name = f"baseline-oracle-gate-{suffix}.json"
        write_json(fixtures / gate_name, gate)
        structured.append(("baseline-oracle-gate-result", gate["gateResultId"], gate, gate_name))

    authority, finite_artifacts, finite_meta = build_finite_authority(root, terminals)
    for role, identity, value in finite_artifacts:
        identity_field = next(field for field in ("planId", "queryId", "witnessId", "tableId") if field in value)
        name = next(path.name for path in fixtures.glob("*.json") if (candidate := read_json(path)).get(identity_field) == identity)
        structured.append((role, identity, value, name))
    conformance = self_identify({
        "schemaVersion": 1, "conformanceId": "0" * 64, "operationKind": "predicate-query",
        "source": authority["predicateSource"], "plan": key("predicate-plan", authority["predicatePlan"]["planId"]),
        "query": key("predicate-query", authority["predicateQuery"]["queryId"]), "compilerId": "future-rust-k-compiler",
        "compilerVersion": "pending", "evaluatorId": "future-rust-k-evaluator", "evaluatorVersion": "pending",
        "compatibilityProfileDigest": corpus["compatibilityProfileDigest"], "executionProfileDigest": corpus["executionProfileDigest"],
        "solverProfileDigest": corpus["solverProfileDigest"], "conformanceSuite": authority["predicateSource"], "result": "nonconformant",
    }, "conformanceId", "k-in-k/oracle-evaluator-conformance/v1")
    write_json(fixtures / "oracle-evaluator-conformance-nonconformant.json", conformance)
    structured.append(("oracle-evaluator-conformance", conformance["conformanceId"], conformance, "oracle-evaluator-conformance-nonconformant.json"))

    output_values, output_entries = output_fixtures(root)
    catalog = read_json(fixtures / "artifact-catalog.json")
    # Corpus execution/replay remains bound to the pre-BAG-12 input catalog.
    # The mutation manifest selects the extended oracle catalog below.  Keeping
    # both immutable catalog versions avoids a self-referential output-catalog
    # fixed point through replayInvocationDigest -> pattern-result -> operand.
    write_json(fixtures / "execution-artifact-catalog.json", catalog)
    catalog["entries"] = [entry for entry in catalog["entries"] if entry["role"] not in OBSOLETE_ORACLE_ROLES and entry["role"] not in set(NEW_ROLES)]
    catalog["entries"].extend([authority["reachSourceEntry"], authority["predicateSourceEntry"], *output_entries])
    for pattern_name, pattern_value in (("pattern-result.json", pattern_baseline), ("mutation-pattern-result.json", pattern_mutant)):
        if not any(entry["role"] == "pattern-result" and entry["digest"] == pattern_value["resultId"] for entry in catalog["entries"]):
            catalog["entries"].append(structured_catalog_entry(root, "pattern-result", pattern_value["resultId"], pattern_value, pattern_name))
    for role, identity, value, name in structured:
        catalog["entries"].append(structured_catalog_entry(root, role, identity, value, name))
    catalog["entries"] = sorted(catalog["entries"], key=lambda entry: (entry["role"], entry["digest"]))
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(catalog, "catalogId"))
    write_json(fixtures / "artifact-catalog.json", catalog)

    for test in manifest["tests"]:
        old_ids = test.pop("oracleIds")
        selected = [by_oracle[(test["invocationDigest"], oracle_id)] for oracle_id in old_ids]
        test["oracleDeclarations"] = [key("oracle-declaration", value["declarationId"]) for value in selected]
    manifest.pop("oracles", None)
    manifest["artifactCatalogDigest"] = catalog["catalogId"]
    manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(manifest, "manifestId"))
    write_json(fixtures / "mutation-manifest.json", manifest)

    flattened_keys = [deepcopy(item) for test in manifest["tests"] for item in test["oracleDeclarations"]]
    policy = read_json(fixtures / "mutation-execution-policy.json")
    if "cacheKey" in policy:
        policy["cacheKey"]["oracleDeclarations"] = flattened_keys
        policy["cacheKey"]["testManifestDigest"] = digest("k-in-k/mutation-test-manifest/v1", manifest["tests"])
        policy["cacheKey"]["oracleManifestDigest"] = digest("k-in-k/mutation-oracle-manifest/v1", flattened_keys)
        policy["cacheKey"]["keyDigest"] = digest("k-in-k/mutation-cache-key/v1", without(policy["cacheKey"], "domain", "keyDigest"))
        policy["policyId"] = digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId"))
        write_json(fixtures / "mutation-execution-policy.json", policy)

    declaration_by_oracle = {(item["testInvocationDigest"], item["oracleId"]): item for item in declarations}
    for report_test in campaign["baseline"]["tests"]:
        manifest_test = tests[report_test["id"]]
        old_ids = report_test.pop("oracleIds")
        report_test["oracleDeclarations"] = [key("oracle-declaration", declaration_by_oracle[(manifest_test["invocationDigest"], item)]["declarationId"]) for item in old_ids]
    campaign["baseline"].pop("oracleResults", None)
    campaign["baseline"]["oracleGateResults"] = [key("baseline-oracle-gate-result", gates_by_decl["gateResultId"])
                                                     for declaration in declarations
                                                     for gates_by_decl in [next(value for value in gates.values() if value["declaration"]["digest"] == declaration["declarationId"])]]
    for mutant_report in campaign["mutants"]:
        for report_test in mutant_report["tests"]:
            manifest_test = tests[report_test["id"]]
            old_ids = report_test.pop("oracleIds")
            report_test["oracleDeclarations"] = [key("oracle-declaration", declaration_by_oracle[(manifest_test["invocationDigest"], item)]["declarationId"]) for item in old_ids]
        results = []
        for declaration in declarations:
            left, right = sides_by_declaration[declaration["declarationId"]]
            comparison = next(value for value in comparisons.values() if value["declaration"]["digest"] == declaration["declarationId"])
            results.append({
                "declaration": key("oracle-declaration", declaration["declarationId"]), "outcome": comparison["outcome"],
                "baselineSide": left, "mutantSide": right,
                "comparison": key("oracle-comparison-result", comparison["comparisonId"]), "failure": None,
            })
        mutant_report["oracleResults"] = results
    campaign["manifestDigest"] = manifest["manifestId"]
    campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
    campaign["reportId"] = digest("k-in-k/mutation-report/v1", without(campaign, "reportId"))
    write_json(fixtures / "mutation-campaign.json", campaign)

    vector_values = {
        "exit-stop": {"left": {"terminalClass": "normal", "exitCode": None}, "different": {"terminalClass": "stuck", "exitCode": None}},
        "final-result/whole": {"left": {"terminalState": key("terminal-state", baseline_terminal["terminalStateDigest"]), "projection": "whole-portable-term-v1", "term": baseline_terminal["value"]},
                               "different": {"terminalState": key("terminal-state", baseline_terminal["terminalStateDigest"]), "projection": "whole-portable-term-v1", "term": {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "token", "text": "different"}}}},
        "final-result/paths": {"left": {"terminalState": key("terminal-state", baseline_terminal["terminalStateDigest"]), "projection": "selected-term-paths-v1", "paths": [{"path": [], "sort": baseline_terminal["value"]["sort"], "value": baseline_terminal["value"]}]},
                               "different": {"terminalState": key("terminal-state", baseline_terminal["terminalStateDigest"]), "projection": "selected-term-paths-v1", "paths": [{"path": [], "sort": "K", "value": {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "token", "text": "different"}}}]}},
        "concrete-output/bytes": {"left": {"channels": [output_values[0]]}, "different": {"channels": [output_values[1]]}},
        "concrete-output/lines": {"left": {"channels": [output_values[0]]}, "different": {"channels": [{**output_values[1], "text": "different\n"}]}},
        "reachability": {"left": {"status": "reached", "witnesses": [key("reachability-witness", authority["witness"]["witnessId"])]}, "different": {"status": "not-reached", "witnesses": []}},
        "execution-pattern/outcome": {"left": {"patternResult": key("pattern-result", pattern_baseline["resultId"]), "outcome": "match", "bindingTuples": []}, "different": {"patternResult": key("pattern-result", pattern_mutant["resultId"]), "outcome": "no-match", "bindingTuples": []}},
        "execution-pattern/bindings": {"left": {"patternResult": key("pattern-result", pattern_baseline["resultId"]), "outcome": "match", "bindingTuples": binding_tuple(pattern_baseline, pattern_plan)}, "different": {"patternResult": key("pattern-result", pattern_mutant["resultId"]), "outcome": "no-match", "bindingTuples": []}},
        "structured-predicate": {"left": {"query": key("predicate-query", authority["predicateQuery"]["queryId"]), "input": authority["predicateTable"]["rows"][0]["input"], "inputProjectionDigest": authority["predicateTable"]["rows"][0]["inputProjectionDigest"], "bindings": authority["predicateTable"]["rows"][0]["bindings"], "bindingsDigest": authority["predicateTable"]["rows"][0]["bindingsDigest"], "result": authority["predicateTable"]["rows"][0]["result"]},
                                 "different": {"query": key("predicate-query", authority["predicateQuery"]["queryId"]), "input": authority["predicateTable"]["rows"][1]["input"], "inputProjectionDigest": authority["predicateTable"]["rows"][1]["inputProjectionDigest"], "bindings": authority["predicateTable"]["rows"][1]["bindings"], "bindingsDigest": authority["predicateTable"]["rows"][1]["bindingsDigest"], "result": authority["predicateTable"]["rows"][1]["result"]}},
    }
    adversaries = [
        "kind-operand-mismatch", "missing-operand-artifact", "extra-operand-artifact", "baseline-mutant-reversal",
        "declaration-projection-comparison-test-profile-drift", "self-asserted-comparison", "equal-digest-unequal-value",
        "unequal-bytes-claimed-agree", "infrastructure-stderr-as-output", "reachability-absence-without-exhaustion",
        "reachability-witness-other-query", "pattern-cross-query-plan-bounds", "predicate-result-without-input",
        "unknown-reported-agree", "arbitrary-enum-kill", "operand-id-as-value", "incomplete-attempt-as-operand",
        "failed-side-retained", "comparison-without-two-sides", "backend-exit-as-object-exit", "final-path-order-overlap-sort",
        "channel-coverage-order-text-mismatch", "proof-byte-inequality", "pattern-witness-result-search-drift",
        "predicate-binding-plan-drift", "baseline-gate-expectation-drift", "crash-satisfies-normal-assertion",
        "declaration-spans-tests", "oracle-coverage-order", "unknown-registry-pair", "unknown-evaluator",
        "finite-row-root-drift", "global-oracle-join", "slot-invocation-drift", "redundant-artifact-list",
        "wrong-self-id-domain", "copied-profile-root-drift", "gate-status-failure-drift", "crash-normal-digest",
        "valid-utf8-null-text", "invalid-utf8-lines", "missing-input-wrong-failure", "receipt-as-conformance",
        "conformance-root-drift", "reachability-proof-identity", "incomplete-not-reached", "pattern-tuple-order",
        "existential-bindings", "predicate-row-root-drift", "bag11-observation-vocabulary-drift", "bag11-pattern-result-declaration-drift",
    ]
    vectors_value = {
        "schemaVersion": 1, "registry": [{"kind": kind, "projectionId": projection, "comparatorId": comparator} for kind, pairs in REGISTRY.items() for projection, comparator in pairs],
        "comparatorCases": [{"id": name, "left": values["left"], "agreeRight": deepcopy(values["left"]), "distinguishRight": values["different"]} for name, values in vector_values.items()],
        "crashPolicyCases": [
            {"id": "normal-vs-crash-incomparable", "orientation": "baseline-normal", "policy": "semantic-crash-incomparable", "expected": "incomparable"},
            {"id": "crash-vs-normal-incomparable", "orientation": "baseline-crash", "policy": "semantic-crash-incomparable", "expected": "incomparable"},
        ],
        "incompleteCases": [
            {"id": "reachability-bounded-unknown", "failure": failure("oracle", "evaluator-unavailable", "unknown"), "expected": "unknown"},
            {"id": "predicate-missing-row", "failure": failure("oracle", "evaluator-unavailable", "unknown"), "expected": "unknown"},
            {"id": "projection-invalid-utf8", "failure": failure("oracle", "projection-invalid"), "expected": "error"},
            {"id": "missing-output-bytes", "failure": failure("input", "missing-artifact"), "expected": "error"},
            {"id": "solver-indeterminate", "failure": failure("execution", "solver-unknown", "unknown"), "expected": "unknown"},
        ],
        "authority": {"reachabilityReached": key("reachability-query", authority["reachedQuery"]["queryId"]), "reachabilityNotReached": key("reachability-query", authority["absentQuery"]["queryId"]), "predicate": key("predicate-query", authority["predicateQuery"]["queryId"]), "finiteInput": finite_meta["inputVectorDigest"]},
        "adversaries": adversaries,
    }
    write_json(vectors / "oracle-semantics-vectors.json", vectors_value)


def finalize_refresh(root: Path) -> None:
    """Build the repaired BAG-12 closure from the backend-neutral seed."""
    install_schemas_and_roles(root)
    fixtures, vectors = root / "fixtures", root / "vectors"
    manifest = read_json(fixtures / "mutation-manifest.json")
    corpus = read_json(fixtures / "corpus-manifest.json")
    campaign = read_json(fixtures / "mutation-campaign.json")
    baseline_terminal = read_json(fixtures / "terminal-state.json")
    mutant_terminal = read_json(fixtures / "terminal-state-mutant.json")
    generated_fixture_patterns = (
        "oracle-declaration-*.json", "oracle-operand-*.json", "oracle-comparison-*.json",
        "baseline-oracle-gate-*.json", "reachability-plan-*.json", "reachability-query-*.json",
        "reachability-witness*.json", "predicate-query*.json", "bag12-*-event-trace.json",
        "bag12-*-pattern-result.json", "bag12-*-pattern-replay.json",
        "pattern-result-write-only-*-no-match.json", "replay-write-only-*-no-match.json",
        "terminal-state-*-live.json", "semantic-crash-*-live.json",
    )
    for pattern in generated_fixture_patterns:
        for path in fixtures.glob(pattern):
            if path.name in {"predicate-query.json", "reachability-witness.json"}:
                continue
            path.unlink()
    generated_material_patterns = (
        "oracle-declaration-*.json", "oracle-operand-*.json", "oracle-comparison-*.json",
        "baseline-oracle-gate-*.json", "reachability-*.json", "predicate-*.json",
        "bag12-*.json", "pattern-result-write-only-*.json", "replay-write-only-*.json",
        "terminal-state-*-live.json", "semantic-crash-*-live.json",
    )
    for pattern in generated_material_patterns:
        for path in (root / "material").glob(pattern):
            if path.name in {"predicate-query.json", "reachability-witness.json"}:
                continue
            path.unlink()
    baseline_definition = manifest["definitionDigest"]
    mutant = campaign["mutants"][0]
    subjects = {
        "baseline": {"side": "baseline", "definitionDigest": baseline_definition},
        "mutant": {"side": "mutant", "baselineDefinitionDigest": baseline_definition, "mutantId": mutant["mutantId"],
                   "mutantDefinitionDigest": mutant["outputDefinitionDigest"]},
    }
    tests = {test["testId"]: test for test in manifest["tests"]}
    corpus_tests = {test["testId"]: test for test in corpus["tests"]}

    def invocation_payload(test: dict[str, Any]) -> dict[str, Any]:
        return {
            "testId": test["testId"], "programDigest": test["programDigest"], "parserDigest": test["parserDigest"],
            "startSymbol": test["startSymbol"], "optionsDigest": test["optionsDigest"], "bounds": corpus["bounds"],
            "executionMode": corpus["executionMode"], "solverProfileDigest": corpus["solverProfileDigest"],
            "executionProfileDigest": corpus["executionProfileDigest"], "compatibilityProfileDigest": corpus["compatibilityProfileDigest"],
            "observationManifestDigest": corpus["observationManifestDigest"], "patternQueries": test["patternQueries"],
        }

    write_load_root = {name: deepcopy(read_json(fixtures / "pattern-query-write-eventually-load.json")[field])
                       for name, field in (("patternSource", "patternSource"), ("patternPlan", "patternPlan"))}
    write_load_root["patternQuery"] = key("pattern-query", read_json(fixtures / "pattern-query-write-eventually-load.json")["queryId"])
    write_only_inputs = read_json(fixtures / "write-only-pattern-result.json")["inputs"]
    write_only_root = {name: deepcopy(write_only_inputs[name]) for name in ("patternSource", "patternPlan", "patternQuery")}
    # Two pattern pairs are selected for each outcome mode. Repetitions are
    # intentional slots and therefore remain in the invocation identity.
    tests["write-load"]["patternQueries"] = [deepcopy(write_load_root), deepcopy(write_load_root)]
    tests["write-only"]["patternQueries"] = [deepcopy(write_only_root), deepcopy(write_only_root)]
    for test_id, test in tests.items():
        source = corpus_tests[test_id]
        for field in ("programDigest", "parserDigest", "startSymbol", "optionsDigest"):
            test[field] = deepcopy(source[field])
        test["boundsDigest"] = digest("k-in-k/bounds/v1", corpus["bounds"])
        test["invocationDigest"] = digest("k-in-k/test-invocation/v1", invocation_payload(test))

    structured: list[tuple[str, str, dict[str, Any], str]] = []

    def add_structured(role: str, identity: str, value: dict[str, Any], name: str) -> dict[str, str]:
        write_json(fixtures / name, value)
        structured.append((role, identity, value, name))
        return key(role, identity)

    def change_first_token(term: dict[str, Any]) -> bool:
        node = term["node"]
        if node["kind"] == "token":
            node["text"] = node["text"] + "-bag12-distinct"
            return True
        children = node.get("args", node.get("items", []))
        if node["kind"] == "rewrite":
            children = [node["left"], node["right"]]
        elif node["kind"] == "injection":
            children = [node["term"]]
        return any(change_first_token(child) for child in children)

    distinct_terminal = deepcopy(mutant_terminal)
    if not change_first_token(distinct_terminal["value"]):
        distinct_terminal["value"]["node"] = {"kind": "token", "text": "bag12-distinct-terminal"}
    distinct_terminal["terminalStateDigest"] = digest("k-in-k/terminal-state/v1", without(distinct_terminal, "terminalStateDigest"))
    add_structured("terminal-state", distinct_terminal["terminalStateDigest"], distinct_terminal, "terminal-state-mutant-distinct.json")

    crashes = {side_name: read_json(fixtures / ("semantic-crash.json" if side_name == "baseline" else "semantic-crash-mutant.json"))
               for side_name in ("baseline", "mutant")}
    terminal_values = {"baseline": baseline_terminal, "mutant": mutant_terminal, "mutant-distinct": distinct_terminal}
    for side_name, terminal in (("baseline", baseline_terminal), ("mutant", mutant_terminal)):
        add_structured("terminal-state", terminal["terminalStateDigest"], terminal, f"terminal-state-{side_name}-live.json")
        crash = crashes[side_name]
        add_structured("semantic-crash", crash["crashDigest"], crash, f"semantic-crash-{side_name}-live.json")

    base_traces = {
        "baseline": read_json(fixtures / "event-trace.json"),
        "mutant": read_json(fixtures / "mutation-event-trace.json"),
        "write-only-seed": read_json(fixtures / "write-only-event-trace.json"),
    }
    trace_values: dict[str, dict[str, Any]] = {}

    def add_trace(label: str, trace: dict[str, Any]) -> dict[str, str]:
        refresh_trace(trace)
        trace_values[label] = trace
        return add_structured("event-trace", trace_digest(trace), trace, f"bag12-{label}-event-trace.json")

    trace_keys = {"baseline": add_trace("baseline", deepcopy(base_traces["baseline"])),
                  "mutant": add_trace("mutant", deepcopy(base_traces["mutant"]))}
    distinct_trace = deepcopy(base_traces["mutant"])
    distinct_trace["executionTerminal"] = {"kind": "normal", "artifact": key("terminal-state", distinct_terminal["terminalStateDigest"])}
    trace_keys["mutant-distinct"] = add_trace("mutant-distinct", distinct_trace)
    stuck_trace = deepcopy(base_traces["mutant"])
    stuck_trace.update({"stopReason": "stuck", "complete": True,
                        "executionTerminal": {"kind": "stuck", "artifact": key("terminal-state", mutant_terminal["terminalStateDigest"])}})
    trace_keys["mutant-stuck"] = add_trace("mutant-stuck", stuck_trace)
    for side_name in ("baseline", "mutant"):
        crash_trace = deepcopy(base_traces[side_name])
        crash_trace.update({"stopReason": "terminal", "complete": True,
                            "executionTerminal": {"kind": "semantic-crash", "artifact": key("semantic-crash", crashes[side_name]["crashDigest"])}})
        trace_keys[f"{side_name}-crash"] = add_trace(f"{side_name}-crash", crash_trace)

    for side_name, terminal in (("baseline", baseline_terminal), ("mutant", mutant_terminal)):
        trace = deepcopy(base_traces["write-only-seed"])
        trace.update({"definitionDigest": subject_definition(subjects[side_name]), "testId": "write-only", "complete": True,
                      "stopReason": "terminal", "executionTerminal": {"kind": "normal", "artifact": key("terminal-state", terminal["terminalStateDigest"])},
                      "events": []})
        trace_keys[f"write-only-{side_name}"] = add_trace(f"write-only-{side_name}", trace)

    def replay_payload(replay: dict[str, Any]) -> dict[str, Any]:
        payload = {name: deepcopy(value) for name, value in replay.items() if name not in {"replayId", "invocationDigest", "expectedResultDigest"}}
        payload["steps"] = [{name: deepcopy(value) for name, value in step.items() if name != "expectedArtifacts"} for step in replay["steps"]]
        return payload

    def build_no_match(side_name: str) -> tuple[dict[str, Any], dict[str, Any]]:
        trace = trace_values[f"write-only-{side_name}"]
        trace_key = trace_keys[f"write-only-{side_name}"]
        replay = deepcopy(read_json(fixtures / "write-only-replay-manifest.json"))
        old_definition = replay["definitionDigest"]
        old_trace = replay["steps"][2]["expectedArtifacts"][0]
        replay["definitionDigest"] = subject_definition(subjects[side_name])
        if side_name == "mutant":
            mutation_replay = read_json(fixtures / "mutation-pattern-replay-manifest.json")
            old_transformation = replay["transformationDigests"][0]
            replay["transformationDigests"] = deepcopy(mutation_replay["transformationDigests"])
            replay["observationManifestDigest"] = mutation_replay["observationManifestDigest"]
            for step in replay["steps"]:
                for artifact in step["inputArtifacts"]:
                    if artifact == key("transformation", old_transformation):
                        artifact["digest"] = replay["transformationDigests"][0]
        for step in replay["steps"]:
            for field in ("inputArtifacts", "expectedArtifacts"):
                for artifact in step[field]:
                    if artifact["digest"] == old_definition and artifact["role"] in {"definition", "instrumented-definition"}:
                        artifact["digest"] = replay["definitionDigest"]
                    if artifact == old_trace:
                        artifact.update(trace_key)
        replay["invocationDigest"] = digest("k-in-k/replay-invocation/v1", replay_payload(replay))
        result = deepcopy(read_json(fixtures / "write-only-pattern-result.json"))
        result.update({"outcome": "no-match", "completeCoverage": True, "witnesses": [], "failures": []})
        result["inputs"].update({"definitionDigest": replay["definitionDigest"], "observationManifestDigest": replay["observationManifestDigest"],
                                 "transformationId": replay["transformationDigests"][0], "replayInvocationDigest": replay["invocationDigest"],
                                 "artifacts": [trace_key]})
        result["pathResults"] = [{"pathOrdinal": 0, "pathKey": "root", "status": "no-match", "completeCoverage": True,
                                  "stopReason": "terminal", "traceDigest": trace_key["digest"], "failures": [],
                                  "pathIdentityDigest": trace["pathIdentityDigest"], "executionStopReason": "terminal",
                                  "executionTerminal": deepcopy(trace["executionTerminal"])}]
        result["resultId"] = digest("k-in-k/pattern-result/v1", without(result, "resultId"))
        replay["expectedResultDigest"] = result["resultId"]
        replay["steps"][3]["expectedArtifacts"] = [key("pattern-result", result["resultId"])]
        replay["replayId"] = digest("k-in-k/replay-manifest/v1", without(replay, "replayId"))
        add_structured("pattern-result", result["resultId"], result, f"pattern-result-write-only-{side_name}-no-match.json")
        add_structured("replay-manifest", replay["replayId"], replay, f"replay-write-only-{side_name}-no-match.json")
        return result, replay

    write_only_patterns = {side_name: build_no_match(side_name) for side_name in ("baseline", "mutant")}
    pattern_results = {
        "baseline": read_json(fixtures / "pattern-result.json"),
        "mutant": read_json(fixtures / "mutation-pattern-result.json"),
        "write-only-baseline": write_only_patterns["baseline"][0],
        "write-only-mutant": write_only_patterns["mutant"][0],
    }
    for name, replay_name in (("baseline", "replay-manifest.json"), ("mutant", "mutation-pattern-replay-manifest.json")):
        result = pattern_results[name]
        replay = read_json(fixtures / replay_name)
        add_structured("pattern-result", result["resultId"], result, f"bag12-{name}-pattern-result.json")
        add_structured("replay-manifest", replay["replayId"], replay, f"bag12-{name}-pattern-replay.json")

    authority, finite_artifacts, finite_meta = build_finite_authority(
        root, tests["write-load"], subjects, {"baseline": baseline_terminal, "mutant": mutant_terminal},
        {"baseline": trace_keys["baseline"], "mutant": trace_keys["mutant"]},
    )
    for role, identity, value in finite_artifacts:
        id_field = next(field for field in ("planId", "queryId", "witnessId", "tableId") if field in value)
        name = next(path.name for path in fixtures.glob("*.json") if read_json(path).get(id_field) == identity)
        structured.append((role, identity, value, name))

    output_values, output_entries = output_fixtures(root)
    output_by_name = {Path(entry["logicalPath"].removeprefix("repo://")).name: value for entry, value in zip(output_entries, output_values)}

    pair_specs = [(kind, projection, comparator, outcome) for kind, pairs in REGISTRY.items()
                  for projection, comparator in pairs for outcome in ("agree", "distinguish")]
    case_specs: list[dict[str, Any]] = []
    slot_counts = {test_id: 0 for test_id in tests}

    def kind_config(kind: str, projection: str, outcome: str, test_id: str) -> dict[str, Any]:
        if kind == "exit-stop":
            return {"kind": kind, "exitCodeMode": "none"}
        if kind == "final-result":
            value: dict[str, Any] = {"kind": kind, "stuckResultPolicy": "incomplete"}
            if projection == "selected-term-paths-v1":
                value["paths"] = [[]]
            return value
        if kind == "concrete-output":
            return {"kind": kind, "channels": ["program-output"]}
        if kind == "reachability":
            query = authority["reachedQuery"] if outcome == "agree" else authority["distinguishQuery"]
            return {"kind": kind, "query": key("reachability-query", query["queryId"])}
        if kind == "execution-pattern":
            root_value = write_only_root if test_id == "write-only" else write_load_root
            return {"kind": kind, **deepcopy(root_value), "searchPolicy": "exhaustive"}
        query = authority["predicateQueries"][0 if outcome == "agree" else 1]
        return {"kind": kind, "query": key("predicate-query", query["queryId"])}

    for kind, projection, comparator, outcome in pair_specs:
        test_id = "write-only" if kind == "execution-pattern" and outcome == "agree" else "write-load"
        slug = f"{kind}-{projection}-{outcome}".replace("-v1", "")
        slot = slot_counts[test_id]
        slot_counts[test_id] += 1
        case_specs.append({"id": slug, "kind": kind, "projection": projection, "comparator": comparator,
                           "outcome": outcome, "testId": test_id, "slot": slot,
                           "config": kind_config(kind, projection, outcome, test_id)})
    for orientation in ("baseline-normal", "baseline-crash"):
        slot = slot_counts["write-load"]
        slot_counts["write-load"] += 1
        case_specs.append({"id": f"incomparable-{orientation}", "kind": "final-result", "projection": "whole-portable-term-v1",
                           "comparator": "exact-portable-term-v1", "outcome": "incomparable", "testId": "write-load", "slot": slot,
                           "config": {"kind": "final-result", "stuckResultPolicy": "incomplete"}, "orientation": orientation})
    for kind in ("reachability", "structured-predicate"):
        slot = slot_counts["write-load"]
        slot_counts["write-load"] += 1
        projection, comparator = REGISTRY[kind][0]
        case_specs.append({"id": f"{kind}-unknown", "kind": kind, "projection": projection, "comparator": comparator,
                           "outcome": "unknown", "testId": "write-load", "slot": slot,
                           "config": kind_config(kind, projection, "agree", "write-load")})

    declarations: dict[str, dict[str, Any]] = {}
    for spec in case_specs:
        test = tests[spec["testId"]]
        gate = None
        if spec["kind"] == "exit-stop" and spec["outcome"] == "agree":
            gate = {
                "mode": "assert",
                "expectedSide": {
                    "kind": "exit-stop",
                    "normalizedValue": {"terminalClass": "normal", "exitCode": None},
                },
            }
        declaration = declaration_for(
            test, corpus, spec["slot"], spec["id"], spec["id"], spec["kind"], spec["projection"], spec["comparator"], spec["config"],
            gate=gate,
            terminal_policy="normal-or-crash" if spec.get("orientation") else "normal-only",
            crash_policy="semantic-crash-incomparable" if spec.get("orientation") else "semantic-crash-distinguishes",
        )
        declarations[declaration["declarationId"]] = declaration
        spec["declaration"] = declaration
        add_structured("oracle-declaration", declaration["declarationId"], declaration, f"oracle-declaration-{spec['id']}.json")

    output_rows = []
    for spec in case_specs:
        if spec["kind"] != "concrete-output":
            continue
        if spec["projection"] == "ordered-output-bytes-v1":
            channel_values = (output_by_name["semantic-output-crlf.bin"], output_by_name["semantic-output-crlf.bin"] if spec["outcome"] == "agree" else output_by_name["semantic-output-different.bin"])
        else:
            channel_values = (output_by_name["semantic-output-crlf.bin"], output_by_name["semantic-output-lf.bin"] if spec["outcome"] == "agree" else output_by_name["semantic-output-different.bin"])
        spec["outputChannels"] = [deepcopy(value) for value in channel_values]
        for side_name, channel in zip(("baseline", "mutant"), channel_values):
            terminal = baseline_terminal if side_name == "baseline" else mutant_terminal
            row = {"rowId": "0" * 64, "declaration": key("oracle-declaration", spec["declaration"]["declarationId"]),
                   "testInvocationDigest": spec["declaration"]["testInvocationDigest"], "subject": deepcopy(subjects[side_name]),
                   "terminal": {"kind": "normal", "artifact": key("terminal-state", terminal["terminalStateDigest"])},
                   "producerTrace": deepcopy(trace_keys[side_name]), "channels": [deepcopy(channel)]}
            row["rowId"] = digest("k-in-k/semantic-output-finite-row/v1", without(row, "rowId"))
            output_rows.append(row)
            spec[f"{side_name}OutputRow"] = row
    output_rows.sort(key=lambda row: row["rowId"])
    output_table = self_identify({"schemaVersion": 1, "tableId": "0" * 64, "rows": output_rows}, "tableId", "k-in-k/semantic-output-finite-table/v1")
    output_table_key = add_structured("semantic-output-finite-table", output_table["tableId"], output_table, "semantic-output-finite-table.json")

    def terminal_projection(spec: dict[str, Any], side_name: str) -> tuple[dict[str, Any], dict[str, Any]]:
        distinct = spec["outcome"] == "distinguish" and side_name == "mutant" and spec["kind"] == "final-result"
        stuck = spec["outcome"] == "distinguish" and side_name == "mutant" and spec["kind"] == "exit-stop"
        terminal = distinct_terminal if distinct else baseline_terminal if side_name == "baseline" else mutant_terminal
        trace_label = "mutant-distinct" if distinct else "mutant-stuck" if stuck else side_name
        evidence = {"kind": "execution-terminal", "terminal": {"kind": "stuck" if stuck else "normal",
                    "artifact": key("terminal-state", terminal["terminalStateDigest"])}, "producerTrace": deepcopy(trace_keys[trace_label])}
        if spec["kind"] == "exit-stop":
            normalized = {"terminalClass": "stuck" if stuck else "normal", "exitCode": None}
        elif spec["projection"] == "whole-portable-term-v1":
            normalized = {"terminalState": key("terminal-state", terminal["terminalStateDigest"]), "projection": spec["projection"], "term": deepcopy(terminal["value"])}
        else:
            normalized = {"terminalState": key("terminal-state", terminal["terminalStateDigest"]), "projection": spec["projection"],
                          "paths": [{"path": [], "sort": terminal["value"]["sort"], "value": deepcopy(terminal["value"])}]}
        return evidence, normalized

    def finite_row(table: dict[str, Any], query_key: dict[str, str], side_name: str) -> dict[str, Any]:
        matches = [row for row in table["rows"] if row["query"] == query_key and row["subject"] == subjects[side_name]]
        assert len(matches) == 1
        return matches[0]

    operands: dict[str, dict[str, Any]] = {}
    comparisons: dict[str, dict[str, Any]] = {}
    gates: dict[str, dict[str, Any]] = {}
    outer_by_declaration: dict[str, dict[str, Any]] = {}
    evidence_cases = []
    taxonomy = read_json(root / "failure-taxonomy.json")

    def taxonomy_failure(stage: str, classification: str, context: str, scope: str) -> dict[str, Any]:
        matches = [(entry, placement) for entry in taxonomy["entries"] if (entry["stage"], entry["classification"]) == (stage, classification)
                   for placement in entry["placements"] if (placement["context"], placement["scope"]) == (context, scope)]
        assert len(matches) == 1
        entry, _ = matches[0]
        return {"stage": stage, "classification": classification, "context": context, "scope": scope,
                "retryability": entry["retryability"], "semanticEvidence": [], "details": {}}

    for spec in case_specs:
        declaration = spec["declaration"]
        sides: dict[str, dict[str, Any]] = {}
        normal_operands: dict[str, dict[str, Any]] = {}
        for side_name in ("baseline", "mutant"):
            use_crash = spec.get("orientation") == "baseline-crash" and side_name == "baseline" or spec.get("orientation") == "baseline-normal" and side_name == "mutant"
            if use_crash:
                sides[side_name] = side(side_name, crash=key("semantic-crash", crashes[side_name]["crashDigest"]))
                continue
            if spec["outcome"] == "unknown" and side_name == "mutant":
                continue
            if spec["kind"] in {"exit-stop", "final-result"}:
                evidence, normalized = terminal_projection(spec, side_name)
            elif spec["kind"] == "concrete-output":
                row = spec[f"{side_name}OutputRow"]
                evidence = {"kind": "semantic-output-finite-row", "table": output_table_key, "rowId": row["rowId"]}
                normalized = {"channels": deepcopy(row["channels"])}
            elif spec["kind"] == "reachability":
                row = finite_row(authority["reachTable"], declaration["kindConfig"]["query"], side_name)
                evidence = {"kind": "reachability-finite-row", "table": key("reachability-conformance-table", authority["reachTable"]["tableId"]),
                            "query": deepcopy(row["query"]), "inputVectorDigest": row["inputVectorDigest"],
                            "producerTraces": deepcopy(row["producerTraces"])}
                normalized = {"status": "reached" if row["witnesses"] else "not-reached", "witnesses": deepcopy(row["witnesses"])}
            elif spec["kind"] == "execution-pattern":
                pattern_key = f"write-only-{side_name}" if spec["testId"] == "write-only" else side_name
                result = pattern_results[pattern_key]
                evidence = {"kind": "pattern-result", "patternResult": key("pattern-result", result["resultId"])}
                normalized = {"patternResult": evidence["patternResult"], "outcome": result["outcome"],
                              "bindingTuples": [] if spec["projection"] == "pattern-outcome-v1" else binding_tuple(result, read_json(fixtures / ("pattern-plan-write-next-load.json" if spec["testId"] == "write-only" else "pattern-plan-write-eventually-load.json")))}
            else:
                row = finite_row(authority["predicateTable"], declaration["kindConfig"]["query"], side_name)
                evidence = {"kind": "predicate-finite-row", "table": key("predicate-conformance-table", authority["predicateTable"]["tableId"]),
                            "query": deepcopy(row["query"]), "input": deepcopy(row["input"]), "bindingsDigest": row["bindingsDigest"],
                            "producerTrace": deepcopy(row["producerTrace"])}
                normalized = {field: deepcopy(row[field]) for field in ("query", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result")}
            operand = operand_for(declaration, deepcopy(subjects[side_name]), evidence, normalized)
            operands[operand["operandId"]] = operand
            normal_operands[side_name] = operand
            sides[side_name] = side(side_name, operand)
            add_structured("oracle-operand", operand["operandId"], operand, f"oracle-operand-{spec['id']}-{side_name}.json")

        baseline_side = sides["baseline"]
        assertion = "agree" if declaration["baselineGate"]["mode"] == "assert" else None
        gate = gate_for(declaration, baseline_side, assertion=assertion)
        gates[gate["gateResultId"]] = gate
        add_structured("baseline-oracle-gate-result", gate["gateResultId"], gate, f"baseline-oracle-gate-{spec['id']}.json")
        comparison = None
        if spec["outcome"] != "unknown":
            comparison = comparison_for(declaration, sides["baseline"], sides["mutant"], spec["outcome"], operands)
            comparisons[comparison["comparisonId"]] = comparison
            add_structured("oracle-comparison-result", comparison["comparisonId"], comparison, f"oracle-comparison-{spec['id']}.json")
            wrapper = None
            if spec["outcome"] == "incomparable":
                wrapper = {"sourceSide": "comparison", "failure": taxonomy_failure("oracle", "incomparable-result", "oracle-comparison", "mutant")}
            outer = {"declaration": key("oracle-declaration", declaration["declarationId"]), "outcome": spec["outcome"],
                     "baselineSide": sides["baseline"], "mutantSide": sides["mutant"],
                     "comparison": key("oracle-comparison-result", comparison["comparisonId"]), "failure": wrapper}
        else:
            wrapper = {"sourceSide": "mutant-operand-production", "failure": taxonomy_failure("oracle", "evaluator-unavailable", "oracle-operand-production", "test")}
            outer = {"declaration": key("oracle-declaration", declaration["declarationId"]), "outcome": "unknown",
                     "baselineSide": sides["baseline"], "mutantSide": None, "comparison": None, "failure": wrapper}
        outer_by_declaration[declaration["declarationId"]] = outer
        evidence_cases.append({"id": spec["id"], "kind": spec["kind"], "projectionId": spec["projection"],
                               "comparatorId": spec["comparator"], "expectedOutcome": spec["outcome"],
                               "declaration": key("oracle-declaration", declaration["declarationId"]),
                               "baselineGate": key("baseline-oracle-gate-result", gate["gateResultId"]),
                               "baselineOperand": None if baseline_side["normalOperand"] is None else baseline_side["normalOperand"],
                               "mutantOperand": None if sides.get("mutant", {}).get("normalOperand") is None else sides["mutant"]["normalOperand"],
                               "comparison": None if comparison is None else key("oracle-comparison-result", comparison["comparisonId"]),
                               "outerResult": outer})

    suite_payload = b"BAG-12 evaluator conformance suite identifier; future Rust execution required.\n"
    (root / "material" / "oracle-conformance-suite.bin").write_bytes(suite_payload)
    suite_key, suite_entry = opaque_record("oracle-conformance-suite", "oracle-conformance-suite.bin", suite_payload)
    conformance = self_identify({
        "schemaVersion": 1, "conformanceId": "0" * 64, "operationKind": "predicate-query",
        "source": authority["predicateSources"][0], "plan": key("predicate-plan", authority["predicatePlan"]["planId"]),
        "query": key("predicate-query", authority["predicateQueries"][0]["queryId"]), "compilerId": "future-rust-k-compiler",
        "compilerVersion": "pending", "evaluatorId": "future-rust-k-evaluator", "evaluatorVersion": "pending",
        "compatibilityProfileDigest": corpus["compatibilityProfileDigest"], "executionProfileDigest": corpus["executionProfileDigest"],
        "solverProfileDigest": corpus["solverProfileDigest"], "conformanceSuite": suite_key, "result": "nonconformant",
    }, "conformanceId", "k-in-k/oracle-evaluator-conformance/v1")
    add_structured("oracle-evaluator-conformance", conformance["conformanceId"], conformance, "oracle-evaluator-conformance-nonconformant.json")

    # The old catalog remains the immutable execution compatibility snapshot.
    catalog = read_json(fixtures / "artifact-catalog.json")
    write_json(fixtures / "execution-artifact-catalog.json", catalog)
    replaced_roles = set(NEW_ROLES) | OBSOLETE_ORACLE_ROLES | {"terminal-state", "semantic-crash", "event-trace", "replay-manifest", "pattern-result", "observation-manifest"}
    catalog["entries"] = [entry for entry in catalog["entries"] if entry["role"] not in replaced_roles]
    catalog["entries"].extend([authority["reachSourceEntry"], *authority["predicateSourceEntries"], *output_entries, suite_entry])
    for observation_name in ("observation-manifest.json", "mutation-observation-manifest.json"):
        observation = read_json(fixtures / observation_name)
        catalog["entries"].append(structured_catalog_entry(root, "observation-manifest", observation["manifestId"], observation, f"bag12-{observation_name}"))
    catalog["entries"].append(structured_catalog_entry(root, "corpus-manifest", corpus["manifestId"], corpus, "bag12-corpus-manifest.json"))
    for role, identity, value, name in structured:
        catalog["entries"].append(structured_catalog_entry(root, role, identity, value, name))
    catalog["entries"] = sorted(catalog["entries"], key=lambda entry: (entry["role"], entry["digest"]))
    assert len({(entry["role"], entry["digest"]) for entry in catalog["entries"]}) == len(catalog["entries"])
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(catalog, "catalogId"))
    write_json(fixtures / "artifact-catalog.json", catalog)

    for test in manifest["tests"]:
        selected = sorted((spec for spec in case_specs if spec["testId"] == test["testId"]), key=lambda spec: spec["slot"])
        test.pop("oracleIds", None)
        test["oracleDeclarations"] = [key("oracle-declaration", spec["declaration"]["declarationId"]) for spec in selected]
    manifest.pop("oracles", None)
    manifest["artifactCatalogDigest"] = catalog["catalogId"]
    manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(manifest, "manifestId"))
    write_json(fixtures / "mutation-manifest.json", manifest)

    flattened = [item for test in manifest["tests"] for item in test["oracleDeclarations"]]
    policy = read_json(fixtures / "mutation-execution-policy.json")
    if "cacheKey" in policy:
        policy["cacheKey"].update({"oracleDeclarations": deepcopy(flattened),
                                   "patternQueries": [deepcopy(root_value) for test in manifest["tests"] for root_value in test["patternQueries"]],
                                   "testManifestDigest": digest("k-in-k/mutation-test-manifest/v1", manifest["tests"]),
                                   "oracleManifestDigest": digest("k-in-k/mutation-oracle-manifest/v1", flattened)})
        policy["cacheKey"]["keyDigest"] = digest("k-in-k/mutation-cache-key/v1", without(policy["cacheKey"], "domain", "keyDigest"))
        policy["policyId"] = digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId"))
        write_json(fixtures / "mutation-execution-policy.json", policy)

    campaign["manifestDigest"] = manifest["manifestId"]
    campaign["selectedTestIds"] = [test["testId"] for test in manifest["tests"]]
    campaign["baseline"].pop("oracleResults", None)
    campaign["baseline"].update({"status": "valid", "failures": [],
                                 "tests": [{"id": test["testId"], "status": "agree", "oracleDeclarations": deepcopy(test["oracleDeclarations"])} for test in manifest["tests"]],
                                 "oracleGateResults": [key("baseline-oracle-gate-result", next(gate["gateResultId"] for gate in gates.values() if gate["declaration"] == item)) for item in flattened]})
    for mutant_report in campaign["mutants"]:
        mutant_report["status"] = "killed"
        mutant_report["tests"] = [{"id": test["testId"], "status": "kill" if test["testId"] == "write-load" else "agree",
                                    "selected": True, "boundsDigest": test["boundsDigest"], "invocationDigest": test["invocationDigest"],
                                    "oracleDeclarations": deepcopy(test["oracleDeclarations"])} for test in manifest["tests"]]
        mutant_report["oracleResults"] = [deepcopy(outer_by_declaration[item["digest"]]) for item in flattened]
    campaign["campaignStatus"] = "complete"
    campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
    campaign["reportId"] = digest("k-in-k/mutation-report/v1", without(campaign, "reportId"))
    write_json(fixtures / "mutation-campaign.json", campaign)

    adversary_ids = [
        "catalog-corpus-removal", "catalog-declaration-removal", "catalog-operand-removal", "catalog-crash-removal",
        "cross-corpus-vocabulary", "stale-test-invocation", "stale-test-id", "replay-wrong-test",
        "pattern-query-plan-search-drift", "side-reversal", "normal-side-subject-swap", "crash-provenance-swap",
        "terminal-relabel", "reachability-cross-side", "predicate-binding-sort", "predicate-input-side",
        "output-other-subject", "gate-mutant-as-baseline", "gate-abort-retains-scoring", "failure-source-context",
        "failure-resource-disposition", "incomparable-missing-comparison", "incomparable-missing-side",
        "arbitrary-k-role", "missing-production-authority", "nonconformant-authority", "receipt-as-conformance",
        "expected-side-kind", "expected-side-value-integrity", "comparison-outcome-assertion", "manifest-slot-order", "execution-policy-isolation-root",
        "campaign-report-test-root", "global-oracle-join", "reachability-incomplete-absence", "utf8-byte-text-drift",
    ]
    inline_expectation_cases = []
    for case in evidence_cases:
        pair = (case["projectionId"], case["comparatorId"])
        if case["expectedOutcome"] != "agree" or pair not in REGISTRY[case["kind"]]:
            continue
        operand_key = case["baselineOperand"]
        assert operand_key is not None
        operand = operands[operand_key["digest"]]
        inline_expectation_cases.append({
            "id": case["id"],
            "kind": case["kind"],
            "projectionId": case["projectionId"],
            "comparatorId": case["comparatorId"],
            "declaration": deepcopy(case["declaration"]),
            "baselineOperand": deepcopy(operand_key),
            "expectedSide": {"kind": case["kind"], "normalizedValue": deepcopy(operand["normalizedValue"])},
        })
    vectors_value = {
        "schemaVersion": 1,
        "registry": [{"kind": kind, "projectionId": projection, "comparatorId": comparator} for kind, pairs in REGISTRY.items() for projection, comparator in pairs],
        "evidenceCases": evidence_cases,
        "inlineExpectationCases": inline_expectation_cases,
        "incompleteCases": [
            {"id": "reachability-bounded-unknown", "failure": taxonomy_failure("oracle", "evaluator-unavailable", "oracle-operand-production", "test"), "expected": "unknown"},
            {"id": "predicate-missing-row", "failure": taxonomy_failure("oracle", "evaluator-unavailable", "oracle-operand-production", "test"), "expected": "unknown"},
            {"id": "projection-invalid-utf8", "failure": taxonomy_failure("oracle", "projection-invalid", "oracle-operand-production", "test"), "expected": "error"},
            {"id": "missing-output-bytes", "failure": taxonomy_failure("input", "missing-artifact", "oracle-operand-production", "test"), "expected": "error"},
            {"id": "solver-indeterminate", "failure": taxonomy_failure("execution", "solver-unknown", "oracle-operand-production", "test"), "expected": "unknown"},
        ],
        "adversaries": [{"id": case_id, "probe": case_id} for case_id in adversary_ids],
    }
    write_json(vectors / "oracle-semantics-vectors.json", vectors_value)


def path_key(path: list[dict[str, Any]]) -> str:
    return canonical(path)


def path_prefix(left: list[dict[str, Any]], right: list[dict[str, Any]]) -> bool:
    return len(left) <= len(right) and left == right[:len(left)]


def term_at_path(term: dict[str, Any], path: list[dict[str, Any]]) -> dict[str, Any]:
    current = term
    for segment in path:
        node = current["node"]
        if segment["kind"] == "argument":
            assert node["kind"] == "application" and segment["index"] < len(node["args"]), "selected path misses an application argument"
            current = node["args"][segment["index"]]
        elif segment["kind"] == "sequence-item":
            assert node["kind"] == "sequence" and segment["index"] < len(node["items"]), "selected path misses a sequence item"
            current = node["items"][segment["index"]]
        elif segment["kind"] == "injection-term":
            assert node["kind"] == "injection", "selected path misses an injection"
            current = node["term"]
        else:
            raise AssertionError("non-term path segment used in a final-result projection")
    return current


def normalize_newlines(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")


class OracleVerifier:
    def __init__(self, root: Path, api: dict[str, Any]):
        self.root = root
        self.fixtures = root / "fixtures"
        self.api = api
        self.ok: Callable[[bool, str], None] = api["ok"]
        self.manifest = read_json(self.fixtures / "mutation-manifest.json")
        self.campaign = read_json(self.fixtures / "mutation-campaign.json")
        self.catalog = read_json(self.fixtures / "artifact-catalog.json")
        self.ok(self.catalog["catalogId"] == digest("k-in-k/artifact-catalog/v1", without(self.catalog, "catalogId")), "active BAG-08 catalog self ID drift")
        self.ok(self.manifest["artifactCatalogDigest"] == self.catalog["catalogId"], "mutation manifest does not select the active BAG-08 catalog")
        self.catalog_entries = {(item["role"], item["digest"]): item for item in self.catalog["entries"]}
        self.ok(len(self.catalog_entries) == len(self.catalog["entries"]), "active BAG-08 catalog has duplicate role/digest keys")
        self.role_specs = {item["role"]: item for item in read_json(self.root / "artifact-role-specs.json")["specs"]}
        self.corpus = self.resolve_json(key("corpus-manifest", self.manifest["corpusManifestDigest"]))
        self.observations = self.registry("observation-manifest", "manifestId")
        self.observation = self.observations.get(self.corpus["observationManifestDigest"])
        self.ok(self.observation is not None, "resolved corpus observation manifest is absent from the active catalog")
        self.declarations = self.registry("oracle-declaration", "declarationId")
        self.operands = self.registry("oracle-operand", "operandId")
        self.comparisons = self.registry("oracle-comparison-result", "comparisonId")
        self.gates = self.registry("baseline-oracle-gate-result", "gateResultId")
        self.conformances = self.registry("oracle-evaluator-conformance", "conformanceId")
        self.terminals = self.registry("terminal-state", "terminalStateDigest")
        self.crashes = self.registry("semantic-crash", "crashDigest")
        self.traces = {entry["digest"]: self.resolve_json(key("event-trace", entry["digest"])) for entry in self.catalog["entries"] if entry["role"] == "event-trace"}
        self.replays = self.registry("replay-manifest", "replayId")
        self.patterns = self.registry("pattern-result", "resultId")
        self.pattern_plans = self.registry("pattern-plan", "patternPlanDigest")
        self.pattern_queries = self.registry("pattern-query", "queryId")
        self.reach_plans = self.registry("reachability-plan", "planId")
        self.reach_queries = self.registry("reachability-query", "queryId")
        self.reach_witnesses = self.registry("reachability-witness", "witnessId")
        self.reach_tables = self.registry("reachability-conformance-table", "tableId")
        self.predicate_plans = self.registry("predicate-plan", "planId")
        self.predicate_queries = self.registry("predicate-query", "queryId")
        self.predicate_tables = self.registry("predicate-conformance-table", "tableId")
        self.output_tables = self.registry("semantic-output-finite-table", "tableId")
        taxonomy_values = self.registry("failure-taxonomy", "taxonomyId")
        self.ok(len(taxonomy_values) == 1, "active catalog must resolve one exact failure taxonomy")
        self.taxonomy = next(iter(taxonomy_values.values()))
        self.tests_by_invocation = {test["invocationDigest"]: test for test in self.manifest["tests"]}
        self.tests_by_id = {test["testId"]: test for test in self.manifest["tests"]}
        self.mutant_by_id = {item["mutantId"]: item for item in self.campaign["mutants"]}

    def entry_bytes(self, artifact: dict[str, str]) -> bytes:
        entry = self.catalog_entries.get((artifact["role"], artifact["digest"]))
        self.ok(entry is not None, f"active BAG-08 catalog omits {artifact['role']}:{artifact['digest']}")
        self.ok(entry["availability"] == "bundled" and entry["logicalPath"].startswith("repo://"), "live semantic artifact is not bundled active-catalog material")
        relative = entry["logicalPath"].removeprefix("repo://")
        data = self.root.parents[1].joinpath(relative).read_bytes()
        self.ok(raw_sha256(data) == entry["contentSha256"], "active-catalog material content hash drift")
        return data

    def resolve_json(self, artifact: dict[str, str]) -> dict[str, Any]:
        entry = self.catalog_entries.get((artifact["role"], artifact["digest"]))
        self.ok(entry is not None and entry["contentModel"] == "canonical-json" and entry["mediaType"] == "application/json", "structured live artifact has no exact active-catalog entry")
        data = self.entry_bytes(artifact)
        value = json.loads(data.decode("utf-8"))
        self.ok(data == canonical(value).encode("utf-8"), "structured active-catalog material is not canonical JSON")
        spec = self.role_specs[artifact["role"]]
        projection = spec["projection"]
        if projection["kind"] == "complete":
            payload = value
        elif projection["kind"] == "without-field":
            payload = without(value, spec["selfIdField"])
        elif projection["kind"] == "field":
            payload = value[projection["field"]]
        elif projection["kind"] == "select-fields":
            payload = {field: value[field] for field in projection["fields"]}
        else:
            raise AssertionError(f"unsupported BAG-12 structured projection {projection['kind']}")
        self.ok(digest(spec["digestDomain"], payload) == artifact["digest"], "structured active-catalog semantic digest drift")
        if spec["selfIdField"] is not None:
            self.ok(value[spec["selfIdField"]] == artifact["digest"], "structured active-catalog self ID differs from its key")
        return value

    def registry(self, role: str, identity_field: str) -> dict[str, dict[str, Any]]:
        result = {}
        for entry in self.catalog["entries"]:
            if entry["role"] != role:
                continue
            value = self.resolve_json(key(role, entry["digest"]))
            self.ok(value[identity_field] == entry["digest"] and entry["digest"] not in result, f"{role} active registry identity drift")
            result[entry["digest"]] = value
        return result

    def resolve_bytes(self, artifact: dict[str, str]) -> bytes:
        entry = self.catalog_entries.get((artifact["role"], artifact["digest"]))
        self.ok(entry is not None and entry["contentModel"] == "opaque-bytes", "oracle bytes artifact does not resolve as exact opaque BAG-08 material")
        return self.entry_bytes(artifact)

    def declaration_ids_for_manifest(self) -> list[str]:
        return [item["digest"] for test in self.manifest["tests"] for item in test["oracleDeclarations"]]

    def invocation_payload(self, test: dict[str, Any]) -> dict[str, Any]:
        return {
            "testId": test["testId"], "programDigest": test["programDigest"], "parserDigest": test["parserDigest"],
            "startSymbol": test["startSymbol"], "optionsDigest": test["optionsDigest"], "bounds": self.corpus["bounds"],
            "executionMode": self.corpus["executionMode"], "solverProfileDigest": self.corpus["solverProfileDigest"],
            "executionProfileDigest": self.corpus["executionProfileDigest"], "compatibilityProfileDigest": self.corpus["compatibilityProfileDigest"],
            "observationManifestDigest": self.corpus["observationManifestDigest"], "patternQueries": test["patternQueries"],
        }

    def validate_test(self, test: dict[str, Any]) -> None:
        corpus_matches = [row for row in self.corpus["tests"] if row["testId"] == test["testId"]]
        self.ok(len(corpus_matches) == 1, "mutation test ID does not resolve exactly once in the selected corpus")
        corpus_test = corpus_matches[0]
        self.ok(all(test[field] == corpus_test[field] for field in ("programDigest", "parserDigest", "startSymbol", "optionsDigest")), "mutation test roots differ from its exact corpus test")
        self.ok(test["boundsDigest"] == digest("k-in-k/bounds/v1", self.corpus["bounds"]), "mutation test bounds digest differs from selected corpus bounds")
        self.ok(test["invocationDigest"] == digest("k-in-k/test-invocation/v1", self.invocation_payload(test)), "mutation test invocation is stale or omitted a selected corpus root")

    def validate_declaration(self, declaration: dict[str, Any], *, expected_test: dict[str, Any] | None = None, expected_slot: int | None = None) -> None:
        self.ok(("oracle-declaration", declaration["declarationId"]) in self.catalog_entries, "oracle declaration is not active-catalog material")
        self.ok(declaration["declarationId"] == digest("k-in-k/oracle-declaration/v1", without(declaration, "declarationId")), "oracle declaration self identity drift")
        test = self.tests_by_invocation.get(declaration["testInvocationDigest"])
        self.ok(test is not None, "oracle declaration spans or names a nonselected test invocation")
        if expected_test is not None:
            self.ok(test == expected_test and declaration["testInvocationDigest"] == expected_test["invocationDigest"], "declaration test invocation drift")
        if expected_slot is not None:
            self.ok(declaration["slotOrdinal"] == expected_slot, "declaration slot ordinal differs from array position")
        self.ok(declaration["kind"] == declaration["kindConfig"]["kind"], "declaration kind/config mismatch")
        self.ok(declaration["compatibilityProfileDigest"] == self.corpus["compatibilityProfileDigest"] and declaration["executionProfileDigest"] == self.corpus["executionProfileDigest"] and declaration["solverProfileDigest"] == self.corpus["solverProfileDigest"] and declaration["boundsDigest"] == test["boundsDigest"], "declaration copied profile/bounds roots differ from invocation")
        projection = declaration["projectionSpec"]
        comparison = declaration["comparisonSpec"]
        if projection["mode"] == comparison["mode"] == "portable-built-in":
            self.ok((projection["projectionId"], comparison["comparatorId"]) in REGISTRY[declaration["kind"]], "unknown or kind-incompatible portable registry pair")
        else:
            self.ok(projection["mode"] == comparison["mode"] == "k-authored", "portable and K-authored operation modes were mixed")
            self.ok(projection["source"]["role"] == "oracle-projection-source" and projection["plan"]["role"] == "oracle-projection-plan" and projection["query"]["role"] == "oracle-projection-query" and comparison["comparisonArtifact"]["role"] == "oracle-comparison-spec", "K-authored declaration uses a legacy/arbitrary operation role")
            for artifact in (projection["source"], projection["plan"], projection["query"], comparison["comparisonArtifact"]):
                self.ok((artifact["role"], artifact["digest"]) in self.catalog_entries, "K-authored declaration operation root is absent from active catalog")
        gate = declaration["baselineGate"]
        if gate["mode"] == "assert" and isinstance(gate["expectedSide"], dict) and "kind" in gate["expectedSide"]:
            self.ok(gate["expectedSide"]["kind"] == declaration["kind"], "asserted expected normal side has another oracle kind")
            self.validate_expected_normal_value(declaration, gate["expectedSide"]["normalizedValue"])
        config = declaration["kindConfig"]
        if declaration["kind"] == "final-result":
            if projection.get("projectionId") == "selected-term-paths-v1":
                paths = config.get("paths", [])
                self.ok(bool(paths) and [path_key(item) for item in paths] == sorted(path_key(item) for item in paths), "selected final-result paths are empty or unsorted")
                self.ok(all(not path_prefix(left, right) for index, left in enumerate(paths) for right in paths[index + 1:]), "selected final-result paths overlap by prefix")
            else:
                self.ok("paths" not in config, "whole-term final-result retained selected paths")
        elif declaration["kind"] == "execution-pattern":
            query_key = config["patternQuery"]
            query = self.pattern_queries.get(query_key["digest"])
            self.ok(query is not None and query["patternSource"] == config["patternSource"] and query["patternPlan"] == config["patternPlan"], "execution-pattern declaration spliced its source/plan/query triple")
            plan = self.pattern_plans[config["patternPlan"]["digest"]]
            self.ok(self.observation["eventVocabularyDigest"] == digest("k-in-k/event-vocabulary/v1", self.observation["eventVocabulary"]), "resolved observation vocabulary self identity drift")
            self.ok(plan["eventVocabularyDigest"] == self.observation["eventVocabularyDigest"], "selected pattern plan vocabulary differs from exact catalog-resolved corpus observation")
            if projection.get("projectionId") == "pattern-outcome-bindings-v1":
                self.ok(config["searchPolicy"] == "exhaustive", "complete binding projection used existential-first search")
        elif declaration["kind"] == "reachability":
            self.ok(config["query"]["digest"] in self.reach_queries, "reachability declaration query is dangling")
        elif declaration["kind"] == "structured-predicate":
            self.ok(config["query"]["digest"] in self.predicate_queries, "predicate declaration query is dangling")

    def validate_expected_normal_value(self, declaration: dict[str, Any], normalized: dict[str, Any]) -> None:
        """Validate an inline assertion value without manufacturing an operand.

        Inline values are declaration-owned expectations, not produced sides,
        so they have no completion evidence or operand identity.  Every
        referenced artifact and every kind-specific derived field must still
        be valid before the comparator may project away provenance.
        """
        self.ok(
            declaration["projectionSpec"]["mode"] == declaration["comparisonSpec"]["mode"] == "portable-built-in",
            "inline expected normal value requires portable built-in validation",
        )
        kind = declaration["kind"]
        config = declaration["kindConfig"]
        projection = declaration["projectionSpec"]["projectionId"]
        if kind == "exit-stop":
            terminal_class = normalized["terminalClass"]
            exit_code = normalized["exitCode"]
            self.ok(
                exit_code is None if config["exitCodeMode"] == "none" or terminal_class == "stuck" else isinstance(exit_code, int),
                "inline expected exit-stop value violates declared object-program exit mode",
            )
            return
        if kind == "final-result":
            terminal_key = normalized["terminalState"]
            terminal = self.terminals.get(terminal_key["digest"])
            self.ok(
                terminal is not None
                and terminal["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", without(terminal, "terminalStateDigest")),
                "inline expected final-result terminal is absent or invalid",
            )
            self.ok(terminal["definitionDigest"] == self.manifest["definitionDigest"], "inline expected final-result terminal belongs to another definition")
            self.ok(normalized["projection"] == projection, "inline expected final-result projection differs from its declaration")
            if projection == "whole-portable-term-v1":
                self.ok(normalized["term"] == terminal["value"], "inline expected whole term differs from its cataloged terminal")
            else:
                paths = config["paths"]
                self.ok([row["path"] for row in normalized["paths"]] == paths, "inline expected final-result paths omit or reorder declaration paths")
                for row in normalized["paths"]:
                    resolved = term_at_path(terminal["value"], row["path"])
                    self.ok(row["sort"] == resolved["sort"] and row["value"] == resolved, "inline expected final-result path is self-asserted")
            return
        if kind == "concrete-output":
            self.validate_output_channels(declaration, normalized)
            return
        if kind == "reachability":
            witness_keys = normalized["witnesses"]
            self.ok(len(witness_keys) == len({item["digest"] for item in witness_keys}), "inline expected reachability witness is duplicated")
            self.ok(normalized["status"] == ("reached" if witness_keys else "not-reached"), "inline expected reachability status differs from its witness set")
            query_key = config["query"]
            query = self.reach_queries.get(query_key["digest"])
            self.ok(query is not None, "inline expected reachability query is dangling")
            plan = self.reach_plans[query["plan"]["digest"]]
            variables = {item["name"]: item["sort"] for item in plan["variables"]}
            for witness_key in witness_keys:
                witness = self.reach_witnesses.get(witness_key["digest"])
                self.ok(
                    witness is not None
                    and witness["witnessId"] == digest("k-in-k/reachability-witness/v1", without(witness, "witnessId"))
                    and witness["query"] == query_key,
                    "inline expected reachability witness is dangling, invalid, or belongs to another query",
                )
                terminal = self.terminals.get(witness["terminalState"]["digest"])
                self.ok(terminal is not None and terminal["definitionDigest"] == self.manifest["definitionDigest"], "inline expected reachability witness belongs to another definition")
                bound: dict[str, dict[str, Any]] = {}
                self.ok(self.match_term(plan["statePattern"], terminal["value"], variables, bound), "inline expected reachability witness does not match its proposition")
                self.ok(self.reachability_side_condition(plan, witness["terminalState"], bound), "inline expected reachability witness violates its side condition")
                expected_bindings = [{"name": item["name"], "term": bound[item["name"]]} for item in plan["variables"]]
                self.ok(witness["bindings"] == expected_bindings, "inline expected reachability witness bindings are self-asserted")
            return
        if kind == "execution-pattern":
            result = self.patterns.get(normalized["patternResult"]["digest"])
            self.ok(
                result is not None and result["resultId"] == digest("k-in-k/pattern-result/v1", without(result, "resultId")),
                "inline expected execution-pattern result is absent or invalid",
            )
            subject = {"side": "baseline", "definitionDigest": self.manifest["definitionDigest"]}
            self.validate_pattern_producer(result, declaration, subject)
            self.ok(result["outcome"] in {"match", "no-match"}, "inline expected execution-pattern result is incomplete")
            expected_tuples = [] if projection == "pattern-outcome-v1" else binding_tuple(result, self.pattern_plans[config["patternPlan"]["digest"]])
            self.ok(
                normalized == {"patternResult": key("pattern-result", result["resultId"]), "outcome": result["outcome"], "bindingTuples": expected_tuples},
                "inline expected execution-pattern value is self-asserted",
            )
            return
        self.ok(kind == "structured-predicate", "inline expected value has an unknown oracle kind")
        self.ok(normalized["query"] == config["query"], "inline expected predicate query differs from its declaration")
        query = self.predicate_queries.get(normalized["query"]["digest"])
        self.ok(query is not None, "inline expected predicate query is dangling")
        plan = self.predicate_plans[query["plan"]["digest"]]
        input_key = normalized["input"]
        self.ok(input_key["role"] == "terminal-state" and input_key["digest"] in self.terminals, "inline expected predicate input is not a cataloged terminal")
        terminal = self.terminals[input_key["digest"]]
        self.ok(terminal["definitionDigest"] == self.manifest["definitionDigest"], "inline expected predicate input belongs to another definition")
        self.ok(normalized["inputProjectionDigest"] == self.predicate_input_projection(plan, input_key), "inline expected predicate input projection drift")
        self.ok(normalized["bindingsDigest"] == digest("k-in-k/bindings/v1", normalized["bindings"]), "inline expected predicate binding digest drift")
        self.ok([item["name"] for item in normalized["bindings"]] == [item["name"] for item in plan["variables"]], "inline expected predicate binding order or coverage drift")
        self.ok(all(binding["term"]["sort"] == variable["sort"] for binding, variable in zip(normalized["bindings"], plan["variables"])), "inline expected predicate binding sort drift")
        rows = [
            row
            for table in self.predicate_tables.values()
            for row in table["rows"]
            if row["query"] == normalized["query"]
            and row["input"] == input_key
            and row["bindingsDigest"] == normalized["bindingsDigest"]
        ]
        self.ok(len(rows) == 1, "inline expected predicate value lacks one exact finite authority row")
        row = rows[0]
        self.ok(
            row["testInvocationDigest"] == declaration["testInvocationDigest"]
            and row["subject"] == {"side": "baseline", "definitionDigest": self.manifest["definitionDigest"]}
            and normalized == {field: row[field] for field in ("query", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result")},
            "inline expected predicate result or finite authority roots are self-asserted",
        )

    def validate_manifest(self, manifest: dict[str, Any] | None = None) -> None:
        value = self.manifest if manifest is None else manifest
        self.ok("oracles" not in value, "global oracle definition/join survived BAG-12")
        self.ok(value["manifestId"] == digest("k-in-k/mutation-manifest/v1", without(value, "manifestId")), "typed mutation manifest ID drift")
        self.ok(value["artifactCatalogDigest"] == self.catalog["catalogId"], "typed mutation manifest selects another active catalog")
        self.ok(value["corpusManifestDigest"] == self.corpus["manifestId"] and ("corpus-manifest", value["corpusManifestDigest"]) in self.catalog_entries, "typed mutation manifest corpus root is dangling or not selected")
        test_ids = [test["testId"] for test in value["tests"]]
        self.ok(len(test_ids) == len(set(test_ids)), "typed mutation manifest duplicates a test ID")
        seen_slots: set[tuple[str, str]] = set()
        flattened = []
        for test in value["tests"]:
            self.validate_test(test)
            slot_ids = []
            for ordinal, declaration_key in enumerate(test["oracleDeclarations"]):
                self.ok(declaration_key["role"] == "oracle-declaration" and (declaration_key["role"], declaration_key["digest"]) in self.catalog_entries and declaration_key["digest"] in self.declarations, "manifest oracle declaration key is dangling/wrong-role")
                declaration = self.declarations[declaration_key["digest"]]
                self.validate_declaration(declaration, expected_test=test, expected_slot=ordinal)
                slot_ids.append(declaration["slotId"])
                flattened.append(declaration_key)
                seen_slots.add((test["invocationDigest"], declaration["slotId"]))
            self.ok(len(slot_ids) == len(set(slot_ids)), "test-local oracle slot ID is duplicated")
            selected_queries = [deepcopy(declaration["kindConfig"]) for declaration in (self.declarations[item["digest"]] for item in test["oracleDeclarations"]) if declaration["kind"] == "execution-pattern"]
            selected_roots = [{name: config[name] for name in ("patternSource", "patternPlan", "patternQuery")} for config in selected_queries]
            self.ok(test["patternQueries"] == selected_roots, "mutation test query roots do not derive from ordered typed declarations")
        self.ok(len(seen_slots) == len(flattened), "one declaration spans multiple invocations or duplicate slots")

    def completion_class(self, operand: dict[str, Any]) -> str:
        evidence = operand["completionEvidence"]
        if evidence["kind"] in {"execution-terminal", "semantic-output-finite-row"}:
            if evidence["kind"] == "semantic-output-finite-row":
                table = self.output_tables[evidence["table"]["digest"]]
                row = next(row for row in table["rows"] if row["rowId"] == evidence["rowId"])
                return self.trace_terminal_class(row["producerTrace"], row["terminal"])
            return self.trace_terminal_class(evidence["producerTrace"], evidence["terminal"])
        return "normal"

    def trace_terminal_class(self, trace_key: dict[str, str], terminal_shell: dict[str, Any]) -> str:
        trace = self.traces.get(trace_key["digest"])
        self.ok(trace is not None and trace_digest(trace) == trace_key["digest"], "producer trace is dangling or has invalid identity")
        self.ok(trace["complete"] and trace["executionTerminal"] == terminal_shell, "inline terminal shell/class differs from its producer trace")
        derived = "stuck" if trace["stopReason"] == "stuck" and terminal_shell["kind"] == "stuck" else "normal" if trace["stopReason"] == "terminal" and terminal_shell["kind"] == "normal" else None
        self.ok(derived is not None, "producer trace does not prove a complete normal/stuck operand")
        return derived

    def validate_trace_subject(self, trace_key: dict[str, str], subject: dict[str, Any], declaration: dict[str, Any], terminal_shell: dict[str, Any] | None = None) -> dict[str, Any]:
        trace = self.traces.get(trace_key["digest"])
        self.ok(trace is not None and trace_digest(trace) == trace_key["digest"], "operand producer trace is absent from active catalog")
        test = self.tests_by_invocation[declaration["testInvocationDigest"]]
        self.ok(trace["testId"] == test["testId"] and trace["definitionDigest"] == subject_definition(subject), "producer trace belongs to another test/definition side")
        if terminal_shell is not None:
            self.trace_terminal_class(trace_key, terminal_shell)
        return trace

    def replay_invocation_payload(self, replay: dict[str, Any]) -> dict[str, Any]:
        payload = {name: deepcopy(value) for name, value in replay.items() if name not in {"replayId", "invocationDigest", "expectedResultDigest"}}
        payload["steps"] = [{name: deepcopy(value) for name, value in step.items() if name != "expectedArtifacts"} for step in replay["steps"]]
        return payload

    def validate_pattern_producer(self, result: dict[str, Any], declaration: dict[str, Any], subject: dict[str, Any]) -> None:
        self.validate_pattern_denotation(result)
        matches = [replay for replay in self.replays.values() if replay["invocationDigest"] == result["inputs"]["replayInvocationDigest"]]
        self.ok(len(matches) == 1, "pattern result does not resolve one active-catalog replay invocation")
        replay = matches[0]
        self.ok(replay["invocationDigest"] == digest("k-in-k/replay-invocation/v1", self.replay_invocation_payload(replay)) and replay["replayId"] == digest("k-in-k/replay-manifest/v1", without(replay, "replayId")), "pattern producer replay identity drift")
        test = self.tests_by_invocation[declaration["testInvocationDigest"]]
        self.ok(replay["testId"] == result["testId"] == test["testId"], "pattern replay/result belongs to another corpus test")
        self.ok(replay["definitionDigest"] == result["inputs"]["definitionDigest"] == subject_definition(subject), "pattern replay/result belongs to another definition side")
        self.ok(all(replay[field] == result["inputs"][field] == expected for field, expected in (
            ("programDigest", test["programDigest"]), ("parserDigest", test["parserDigest"]), ("startSymbol", test["startSymbol"]),
            ("optionsDigest", test["optionsDigest"]), ("compatibilityProfileDigest", declaration["compatibilityProfileDigest"]),
            ("executionProfileDigest", declaration["executionProfileDigest"]), ("solverProfileDigest", declaration["solverProfileDigest"]),
        )), "pattern replay/result invocation roots differ from declaration/corpus test")
        self.ok(replay["bounds"] == result["bounds"] == self.corpus["bounds"], "pattern replay/result bounds differ from exact corpus invocation")
        config = declaration["kindConfig"]
        self.ok(all(replay[name] == result["inputs"][name] == config[name] for name in ("patternSource", "patternPlan", "patternQuery")) and replay["searchPolicy"] == result["inputs"]["searchPolicy"] == config["searchPolicy"], "pattern replay/result query/plan/search-policy drift")
        observation = self.observations.get(replay["observationManifestDigest"])
        self.ok(observation is not None and result["inputs"]["observationManifestDigest"] == observation["manifestId"] and observation["eventVocabularyDigest"] == self.observation["eventVocabularyDigest"], "pattern producer uses an unselected or cross-vocabulary observation manifest")
        self.ok(replay["expectedResultDigest"] == result["resultId"], "pattern replay expected result differs from resolved operand result")
        trace_keys = result["inputs"]["artifacts"]
        self.ok(trace_keys and all(item["role"] == "event-trace" and item["digest"] in self.traces for item in trace_keys), "pattern result trace closure is absent from active catalog")
        for trace_key in trace_keys:
            self.validate_trace_subject(trace_key, subject, declaration)

    def validate_pattern_denotation(self, result: dict[str, Any]) -> None:
        checker = self.api.get("validate_pattern_result_semantics")
        self.ok(callable(checker), "BAG-11 complete-denotation validator is unavailable")
        checker(result, self.traces, self.taxonomy)

    def validate_pattern_operand(self, operand: dict[str, Any], declaration: dict[str, Any], result: dict[str, Any]) -> None:
        config = declaration["kindConfig"]
        test = self.tests_by_invocation[declaration["testInvocationDigest"]]
        subject = operand["subject"]
        expected_definition = subject["definitionDigest"] if subject["side"] == "baseline" else subject["mutantDefinitionDigest"]
        self.ok(result["testId"] == test["testId"], "pattern operand result is not a member of the selected test")
        self.ok(result["inputs"]["definitionDigest"] == expected_definition, "pattern operand result belongs to another definition side")
        self.ok(result["queryId"] == config["patternQuery"]["digest"] and all(result["inputs"][field] == config[field] for field in ("patternSource", "patternPlan", "patternQuery")), "pattern operand differs from declaration source/plan/query")
        self.ok(result["inputs"]["searchPolicy"] == config["searchPolicy"], "pattern operand search-policy drift")
        self.validate_pattern_producer(result, declaration, subject)
        self.ok(result["outcome"] in {"match", "no-match"}, "unknown/error pattern result was used as an operand")
        if result["outcome"] == "no-match":
            self.ok(result["completeCoverage"] and config["searchPolicy"] == "exhaustive", "nonexhaustive no-match was used as an operand")
        projection = declaration["projectionSpec"]["projectionId"]
        expected_tuples = [] if projection == "pattern-outcome-v1" else binding_tuple(result, self.pattern_plans[config["patternPlan"]["digest"]])
        self.ok(operand["normalizedValue"] == {"patternResult": key("pattern-result", result["resultId"]), "outcome": result["outcome"], "bindingTuples": expected_tuples}, "pattern operand normalized projection is self-asserted or witness-ordered")

    def validate_operand(self, operand: dict[str, Any]) -> None:
        self.ok(("oracle-operand", operand["operandId"]) in self.catalog_entries, "oracle operand is not active-catalog material")
        self.ok(operand["operandId"] == digest("k-in-k/oracle-operand/v1", without(operand, "operandId")), "oracle operand self identity drift")
        declaration = self.declarations.get(operand["declaration"]["digest"])
        self.ok(declaration is not None, "oracle operand declaration is dangling")
        self.validate_declaration(declaration)
        self.ok(all(operand[field] == declaration[field] for field in ("testInvocationDigest", "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest")), "operand invocation/profile roots differ from declaration")
        subject = operand["subject"]
        if subject["side"] == "baseline":
            self.ok(subject["definitionDigest"] == self.manifest["definitionDigest"], "baseline operand references another definition")
        else:
            mutant = self.mutant_by_id.get(subject["mutantId"])
            self.ok(mutant is not None and subject["baselineDefinitionDigest"] == self.manifest["definitionDigest"] and subject["mutantDefinitionDigest"] == mutant["outputDefinitionDigest"], "mutant operand subject drift")
        kind, evidence, normalized = declaration["kind"], operand["completionEvidence"], operand["normalizedValue"]
        if declaration["projectionSpec"]["mode"] == "k-authored" or declaration["comparisonSpec"]["mode"] == "k-authored":
            raise AssertionError("K-authored decision lacks mandatory BAG-15 production authority")
        if kind in {"exit-stop", "final-result"}:
            self.ok(evidence["kind"] == "execution-terminal", "terminal kind used nonterminal completion evidence")
            terminal_key = evidence["terminal"]["artifact"]
            terminal = self.terminals.get(terminal_key["digest"])
            self.ok(terminal is not None, "terminal completion evidence is dangling")
            expected_definition = subject["definitionDigest"] if subject["side"] == "baseline" else subject["mutantDefinitionDigest"]
            self.ok(terminal["definitionDigest"] == expected_definition, "terminal completion evidence belongs to another side")
            derived_terminal_class = self.trace_terminal_class(evidence["producerTrace"], evidence["terminal"])
            self.validate_trace_subject(evidence["producerTrace"], subject, declaration, evidence["terminal"])
            if kind == "exit-stop":
                self.ok(normalized["terminalClass"] == derived_terminal_class, "exit-stop terminal class is not derived from producer trace")
                mode = declaration["kindConfig"]["exitCodeMode"]
                self.ok(normalized["exitCode"] is None if mode == "none" or normalized["terminalClass"] == "stuck" else isinstance(normalized["exitCode"], int), "exit-stop code violates declared object-program exit mode")
            elif kind == "final-result":
                self.ok(normalized["terminalState"] == terminal_key, "final-result source terminal key drift")
                if derived_terminal_class == "stuck":
                    self.ok(declaration["kindConfig"]["stuckResultPolicy"] == "comparable", "stuck final result used without comparable policy")
                projection = declaration["projectionSpec"]["projectionId"]
                self.ok(normalized["projection"] == projection, "final-result projection drift")
                if projection == "whole-portable-term-v1":
                    self.ok(normalized["term"] == terminal["value"], "whole final term differs from resolved terminal")
                else:
                    paths = declaration["kindConfig"]["paths"]
                    self.ok([row["path"] for row in normalized["paths"]] == paths, "selected final paths omit/reorder declaration paths")
                    for row in normalized["paths"]:
                        resolved = term_at_path(terminal["value"], row["path"])
                        self.ok(row["sort"] == resolved["sort"] and row["value"] == resolved, "selected final path has missing/wrong-sort/self-asserted value")
        elif kind == "concrete-output":
            self.validate_output_value(operand, declaration, evidence, normalized)
        elif kind == "execution-pattern":
            self.ok(evidence["kind"] == "pattern-result" and evidence["patternResult"] == normalized["patternResult"], "pattern completion evidence/result key drift")
            result = self.patterns.get(evidence["patternResult"]["digest"])
            self.ok(result is not None, "pattern completion evidence is dangling")
            self.validate_pattern_operand(operand, declaration, result)
        elif kind == "reachability":
            self.validate_reachability_value(operand, declaration, evidence, normalized)
        else:
            self.validate_predicate_value(operand, declaration, evidence, normalized)

    def validate_output_value(
        self,
        operand: dict[str, Any],
        declaration: dict[str, Any],
        evidence: dict[str, Any],
        normalized: dict[str, Any],
    ) -> None:
        self.ok(evidence["kind"] == "semantic-output-finite-row", "concrete output lacks a finite reviewed production row")
        table = self.output_tables.get(evidence["table"]["digest"])
        self.ok(table is not None, "semantic output finite table is absent from the active catalog")
        rows = [row for row in table["rows"] if row["rowId"] == evidence["rowId"]]
        self.ok(len(rows) == 1, "semantic output row is missing or ambiguous")
        row = rows[0]
        self.ok(row["rowId"] == digest("k-in-k/semantic-output-finite-row/v1", without(row, "rowId")), "semantic output row identity drift")
        self.ok(row["declaration"] == operand["declaration"] and row["testInvocationDigest"] == operand["testInvocationDigest"], "semantic output row belongs to another declaration/test")
        self.ok(row["subject"] == operand["subject"], "semantic output row belongs to another subject")
        terminal_key = row["terminal"]["artifact"]
        terminal = self.terminals.get(terminal_key["digest"])
        self.ok(terminal is not None and terminal["definitionDigest"] == subject_definition(operand["subject"]), "semantic output terminal belongs to another subject")
        self.validate_trace_subject(row["producerTrace"], operand["subject"], declaration, row["terminal"])
        self.ok(normalized == {"channels": row["channels"]}, "semantic output bytes were not derived from the exact finite production row")
        self.validate_output_channels(declaration, normalized)

    def validate_output_channels(self, declaration: dict[str, Any], normalized: dict[str, Any]) -> None:
        channels = normalized["channels"]
        self.ok([item["name"] for item in channels] == declaration["kindConfig"]["channels"], "semantic output channel coverage/order drift")
        self.ok(len({item["name"] for item in channels}) == len(channels), "duplicate semantic output channel")
        projection = declaration["projectionSpec"]["projectionId"]
        for channel in channels:
            entry = self.catalog_entries.get((channel["bytesArtifact"]["role"], channel["bytesArtifact"]["digest"]))
            self.ok(entry is not None and channel["mediaType"] == entry["mediaType"], "semantic output mediaType differs from its exact catalog entry")
            data = self.resolve_bytes(channel["bytesArtifact"])
            self.ok(channel["contentSha256"] == raw_sha256(data), "semantic output byte hash mismatch")
            try:
                decoded = data.decode("utf-8")
            except UnicodeDecodeError:
                decoded = None
            self.ok(channel["text"] == decoded, "semantic output text is null/wrong despite exact strict UTF-8 decode")
            if projection == "ordered-output-utf8-lines-v1":
                self.ok(decoded is not None, "invalid UTF-8 was produced for UTF-8-lines projection")

    def validate_evaluator_conformance(self, record: dict[str, Any]) -> None:
        self.ok(("oracle-evaluator-conformance", record["conformanceId"]) in self.catalog_entries, "evaluator conformance is not active-catalog material")
        self.ok(record["conformanceId"] == digest("k-in-k/oracle-evaluator-conformance/v1", without(record, "conformanceId")), "evaluator conformance self ID drift")
        self.ok(record["compatibilityProfileDigest"] == self.corpus["compatibilityProfileDigest"] and record["executionProfileDigest"] == self.corpus["executionProfileDigest"] and record["solverProfileDigest"] == self.corpus["solverProfileDigest"], "evaluator conformance profile roots drift")
        self.ok(record["conformanceSuite"]["role"] == "oracle-conformance-suite", "evaluator conformance used an arbitrary suite role")
        self.resolve_bytes(record["conformanceSuite"])
        operation = record["operationKind"]
        if operation == "predicate-query":
            query = self.predicate_queries.get(record["query"]["digest"])
            self.ok(record["source"]["role"] == "predicate-source" and record["plan"]["role"] == "predicate-plan" and record["query"]["role"] == "predicate-query", "predicate conformance uses arbitrary K roles")
            self.ok(query is not None and query["source"] == record["source"] and query["plan"] == record["plan"], "predicate evaluator conformance source/plan/query drift")
        elif operation == "reachability-query":
            query = self.reach_queries.get(record["query"]["digest"])
            self.ok(record["source"]["role"] == "reachability-source" and record["plan"]["role"] == "reachability-plan" and record["query"]["role"] == "reachability-query", "reachability conformance uses arbitrary K roles")
            self.ok(query is not None and query["source"] == record["source"] and query["plan"] == record["plan"], "reachability evaluator conformance source/plan/query drift")
        else:
            fields = ("comparisonArtifact",) if operation == "comparison" else ("source", "plan", "query")
            expected_roles = ("oracle-comparison-spec",) if operation == "comparison" else ("oracle-projection-source", "oracle-projection-plan", "oracle-projection-query")
            self.ok(tuple(record[field]["role"] for field in fields) == expected_roles, "K-authored conformance uses legacy/arbitrary operation roles")
            self.ok(all((record[field]["role"], record[field]["digest"]) in self.catalog_entries for field in fields), "evaluator conformance operation root is dangling")

    def authorize_evaluator(self, record: dict[str, Any], expected: dict[str, Any], production_receipt: dict[str, Any] | None = None) -> None:
        self.validate_evaluator_conformance(record)
        self.ok(record["result"] == "conformant", "nonconformant evaluator record was used as decision authority")
        self.ok(all(record.get(field) == value for field, value in expected.items()), "evaluator conformance was reused for different operation roots")
        self.ok(production_receipt is not None and production_receipt.get("role") == "oracle-production-receipt", "K-authored decision lacks mandatory BAG-15 production authority")
        raise AssertionError("BAG-15 production receipt role is not registered in the zero-backend BAG-12 package")

    def comparator(self, declaration: dict[str, Any], left: dict[str, Any], right: dict[str, Any]) -> str:
        projection = declaration["projectionSpec"]["projectionId"]
        if projection == "terminal-class-and-declared-exit-v1":
            equal = left == right
        elif projection == "whole-portable-term-v1":
            equal = left["term"] == right["term"]
        elif projection == "selected-term-paths-v1":
            equal = left["paths"] == right["paths"]
        elif projection == "ordered-output-bytes-v1":
            def byte_projection(value: dict[str, Any]) -> list[tuple[str, str, bytes]]:
                return [(item["name"], item["mediaType"], self.resolve_bytes(item["bytesArtifact"])) for item in value["channels"]]
            equal = byte_projection(left) == byte_projection(right)
        elif projection == "ordered-output-utf8-lines-v1":
            def text_projection(value: dict[str, Any]) -> list[tuple[str, str, str]]:
                return [(item["name"], item["mediaType"], normalize_newlines(item["text"])) for item in value["channels"]]
            equal = text_projection(left) == text_projection(right)
        elif projection == "reachability-truth-v1":
            equal = left["status"] == right["status"]
        elif projection == "pattern-outcome-v1":
            equal = left["outcome"] == right["outcome"]
        elif projection == "pattern-outcome-bindings-v1":
            equal = (left["outcome"], left["bindingTuples"]) == (right["outcome"], right["bindingTuples"])
        elif projection == "predicate-bool-v1":
            equal = left["result"] == right["result"]
        else:
            raise AssertionError("zero-backend comparator used an unregistered/K-authored operation")
        return "agree" if equal else "distinguish"

    def match_term(self, pattern: dict[str, Any], actual: dict[str, Any], variables: dict[str, str], bindings: dict[str, dict[str, Any]]) -> bool:
        node = pattern["node"]
        if node["kind"] == "variable":
            name = node["name"]
            if name not in variables or variables[name] != pattern["sort"] or actual["sort"] != pattern["sort"]:
                return False
            if name in bindings:
                return bindings[name] == actual
            bindings[name] = actual
            return True
        if pattern["sort"] != actual["sort"] or node["kind"] != actual["node"]["kind"]:
            return False
        other = actual["node"]
        if node["kind"] == "token":
            return node["text"] == other["text"]
        if node["kind"] == "application":
            return node["symbolId"] == other["symbolId"] and len(node["args"]) == len(other["args"]) and all(self.match_term(left, right, variables, bindings) for left, right in zip(node["args"], other["args"]))
        if node["kind"] == "rewrite":
            return self.match_term(node["left"], other["left"], variables, bindings) and self.match_term(node["right"], other["right"], variables, bindings)
        if node["kind"] == "sequence":
            return len(node["items"]) == len(other["items"]) and all(self.match_term(left, right, variables, bindings) for left, right in zip(node["items"], other["items"]))
        if node["kind"] == "injection":
            return node["fromSort"] == other["fromSort"] and node["toSort"] == other["toSort"] and self.match_term(node["term"], other["term"], variables, bindings)
        return False

    def reachability_side_condition(self, plan: dict[str, Any], terminal_key: dict[str, str], bindings: dict[str, dict[str, Any]]) -> bool:
        condition = plan["sideCondition"]
        if condition is None:
            return True
        query = self.predicate_queries.get(condition["digest"])
        self.ok(query is not None, "reachability sideCondition predicate query is dangling")
        predicate_plan = self.predicate_plans[query["plan"]["digest"]]
        declared = {item["name"]: item["sort"] for item in plan["variables"]}
        expected_bindings = []
        for variable in predicate_plan["variables"]:
            self.ok(variable["name"] in bindings and declared.get(variable["name"]) == variable["sort"] and bindings[variable["name"]]["sort"] == variable["sort"], "reachability sideCondition variable/sort interface drift")
            expected_bindings.append({"name": variable["name"], "term": bindings[variable["name"]]})
        binding_digest = digest("k-in-k/bindings/v1", expected_bindings)
        matches = [row for table in self.predicate_tables.values() for row in table["rows"] if row["query"] == condition and row["input"] == terminal_key and row["bindings"] == expected_bindings and row["bindingsDigest"] == binding_digest]
        self.ok(len(matches) == 1, "reachability sideCondition lacks one exact finite predicate row")
        return matches[0]["result"]

    def validate_reachability_assets(self) -> None:
        for plan in self.reach_plans.values():
            self.ok(plan["planId"] == digest("k-in-k/reachability-plan/v1", without(plan, "planId")), "reachability plan self ID drift")
            variables = [(item["name"], item["sort"]) for item in plan["variables"]]
            self.ok(len(variables) == len({name for name, _ in variables}), "reachability plan variable duplicated")
            if plan["sideCondition"] is not None:
                self.ok(plan["sideCondition"]["digest"] in self.predicate_queries, "reachability plan sideCondition is not an exact predicate query")
        for query in self.reach_queries.values():
            self.ok(query["queryId"] == digest("k-in-k/reachability-query/v1", without(query, "queryId")) and query["plan"]["digest"] in self.reach_plans, "reachability query identity/plan drift")
        for witness in self.reach_witnesses.values():
            self.ok(witness["witnessId"] == digest("k-in-k/reachability-witness/v1", without(witness, "witnessId")), "reachability witness self ID drift")
            query = self.reach_queries[witness["query"]["digest"]]
            plan = self.reach_plans[query["plan"]["digest"]]
            terminal = self.terminals[witness["terminalState"]["digest"]]
            self.ok(terminal["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", without(terminal, "terminalStateDigest")), "reachability witness terminal identity drift")
            bound: dict[str, dict[str, Any]] = {}
            variables = {item["name"]: item["sort"] for item in plan["variables"]}
            self.ok(self.match_term(plan["statePattern"], terminal["value"], variables, bound) and self.reachability_side_condition(plan, witness["terminalState"], bound), "reachability witness terminal does not satisfy proposition and sideCondition")
            expected_bindings = [{"name": item["name"], "term": bound[item["name"]]} for item in plan["variables"]]
            self.ok(witness["bindings"] == expected_bindings, "reachability witness bindings are missing/reordered/self-asserted")
        for table in self.reach_tables.values():
            self.ok(table["tableId"] == digest("k-in-k/reachability-conformance-table/v1", without(table, "tableId")), "reachability table self ID drift")
            keys = [(row["query"]["digest"], row["inputVectorDigest"]) for row in table["rows"]]
            self.ok(keys == sorted(set(keys)), "reachability rows are duplicate or noncanonical")
            for row in table["rows"]:
                self.ok(row["testInvocationDigest"] in self.tests_by_invocation, "reachability finite row test invocation is not selected")
                test = self.tests_by_invocation[row["testInvocationDigest"]]
                self.ok(row["subject"]["side"] in {"baseline", "mutant"}, "reachability row subject is malformed")
                expected_definition = subject_definition(row["subject"])
                if row["subject"]["side"] == "baseline":
                    self.ok(expected_definition == self.manifest["definitionDigest"], "reachability finite row baseline definition drift")
                else:
                    mutant = self.mutant_by_id.get(row["subject"]["mutantId"])
                    self.ok(mutant is not None and row["subject"]["baselineDefinitionDigest"] == self.manifest["definitionDigest"] and expected_definition == mutant["outputDefinitionDigest"], "reachability finite row mutant subject drift")
                expected_input = digest("k-in-k/reachability-finite-input/v1", {"terminalStates": row["terminalStates"], "finiteComplete": row["finiteComplete"]})
                self.ok(row["inputVectorDigest"] == expected_input, "reachability finite input digest drift")
                self.ok(len(row["producerTraces"]) == len(row["terminalStates"]), "reachability finite row trace/input cardinality drift")
                for terminal_key, trace_key in zip(row["terminalStates"], row["producerTraces"]):
                    terminal = self.terminals.get(terminal_key["digest"])
                    self.ok(terminal is not None and terminal["definitionDigest"] == expected_definition, "reachability finite input was swapped across subjects")
                    # Finite rows bind the producing attempt even though their
                    # collection semantics may retain stuck/crash paths.
                    self.validate_trace_subject(trace_key, row["subject"], {"testInvocationDigest": test["invocationDigest"]})
                query = self.reach_queries[row["query"]["digest"]]
                plan = self.reach_plans[query["plan"]["digest"]]
                derived = []
                for ordinal, terminal_key in enumerate(row["terminalStates"]):
                    terminal = self.terminals[terminal_key["digest"]]
                    bound: dict[str, dict[str, Any]] = {}
                    variables = {item["name"]: item["sort"] for item in plan["variables"]}
                    if self.match_term(plan["statePattern"], terminal["value"], variables, bound) and self.reachability_side_condition(plan, terminal_key, bound):
                        matches = [witness for witness in self.reach_witnesses.values() if witness["query"] == row["query"] and witness["terminalState"] == terminal_key]
                        self.ok(len(matches) == 1, "reachability finite row omitted/duplicated a derived witness")
                        derived.append((ordinal, matches[0]))
                ordered = [key("reachability-witness", item["witnessId"]) for _, item in sorted(derived, key=lambda pair: (pair[0], digest("k-in-k/bindings/v1", pair[1]["bindings"]), canonical(pair[1]["bindings"]))) ]
                self.ok(row["witnesses"] == ordered, "reachability finite row witness set/order drift")
                if not row["witnesses"]:
                    self.ok(row["finiteComplete"], "incomplete finite absence was called not-reached")

    def validate_reachability_value(self, operand: dict[str, Any], declaration: dict[str, Any], evidence: dict[str, Any], normalized: dict[str, Any]) -> None:
        self.ok(evidence["kind"] == "reachability-finite-row" and evidence["query"] == declaration["kindConfig"]["query"], "reachability operand completion/query drift")
        table = self.reach_tables.get(evidence["table"]["digest"])
        self.ok(table is not None, "reachability operand table is dangling")
        rows = [row for row in table["rows"] if row["query"] == evidence["query"] and row["inputVectorDigest"] == evidence["inputVectorDigest"]]
        self.ok(len(rows) == 1, "reachability operand has missing/ambiguous finite row")
        row = rows[0]
        self.ok(row["testInvocationDigest"] == operand["testInvocationDigest"] and row["subject"] == operand["subject"], "reachability operand selected another test/subject finite row")
        self.ok(row["producerTraces"] == evidence["producerTraces"], "reachability operand producer traces differ from its finite row")
        for terminal_key, trace_key in zip(row["terminalStates"], row["producerTraces"]):
            terminal = self.terminals.get(terminal_key["digest"])
            self.ok(terminal is not None and terminal["definitionDigest"] == subject_definition(operand["subject"]), "reachability operand retained another subject's terminal")
            self.validate_trace_subject(trace_key, operand["subject"], declaration)
        expected_status = "reached" if row["witnesses"] else "not-reached"
        self.ok(normalized == {"status": expected_status, "witnesses": row["witnesses"]}, "reachability truth/witness projection is self-asserted")

    def predicate_input_projection(self, plan: dict[str, Any], input_key: dict[str, str]) -> str:
        self.ok(input_key["role"] == plan["inputRole"], "predicate row input role differs from plan")
        if input_key["role"] == "terminal-state":
            value = self.terminals[input_key["digest"]]
        else:
            raise AssertionError("finite predicate row uses an unregistered input role")
        return digest("k-in-k/predicate-input-projection/v1", {
            "inputRole": plan["inputRole"], "inputSchemaDigest": plan["inputSchemaDigest"], "inputArtifact": input_key, "inputValue": value,
        })

    def validate_predicate_assets(self) -> None:
        for plan in self.predicate_plans.values():
            self.ok(plan["planId"] == digest("k-in-k/predicate-plan/v1", without(plan, "planId")), "predicate plan self ID drift")
            self.ok(plan["inputProjectionDigest"] == digest("k-in-k/predicate-input-projection-spec/v1", {"inputRole": plan["inputRole"], "inputSchemaDigest": plan["inputSchemaDigest"]}), "predicate plan input projection identity drift")
            self.ok(plan["resultSort"] == "Bool", "predicate plan result is not Bool")
        for query in self.predicate_queries.values():
            self.ok(query["queryId"] == digest("k-in-k/predicate-query/v1", without(query, "queryId")) and query["plan"]["digest"] in self.predicate_plans, "predicate query identity/plan drift")
        for table in self.predicate_tables.values():
            self.ok(table["tableId"] == digest("k-in-k/predicate-conformance-table/v1", without(table, "tableId")), "predicate table self ID drift")
            keys = [(row["query"]["digest"], row["input"]["role"], row["input"]["digest"], row["bindingsDigest"]) for row in table["rows"]]
            self.ok(keys == sorted(set(keys)), "predicate rows are duplicate or noncanonical")
            for row in table["rows"]:
                query = self.predicate_queries[row["query"]["digest"]]
                plan = self.predicate_plans[query["plan"]["digest"]]
                self.ok(row["testInvocationDigest"] in self.tests_by_invocation, "predicate finite row test invocation is not selected")
                self.ok(row["input"]["role"] == "terminal-state" and row["input"]["digest"] in self.terminals, "predicate finite row input is not a cataloged terminal")
                terminal = self.terminals[row["input"]["digest"]]
                self.ok(terminal["definitionDigest"] == subject_definition(row["subject"]), "predicate finite input was swapped across subjects")
                self.validate_trace_subject(row["producerTrace"], row["subject"], {"testInvocationDigest": row["testInvocationDigest"]})
                self.ok(row["inputProjectionDigest"] == self.predicate_input_projection(plan, row["input"]), "predicate row input projection drift")
                self.ok(row["bindingsDigest"] == digest("k-in-k/bindings/v1", row["bindings"]), "predicate row binding digest drift")
                self.ok([item["name"] for item in row["bindings"]] == [item["name"] for item in plan["variables"]], "predicate row binding order/coverage drift")
                self.ok(all(binding["term"]["sort"] == variable["sort"] for binding, variable in zip(row["bindings"], plan["variables"])), "predicate binding term sort differs from the plan variable sort")

    def validate_predicate_value(self, operand: dict[str, Any], declaration: dict[str, Any], evidence: dict[str, Any], normalized: dict[str, Any]) -> None:
        self.ok(evidence["kind"] == "predicate-finite-row" and evidence["query"] == declaration["kindConfig"]["query"], "predicate operand completion/query drift")
        table = self.predicate_tables.get(evidence["table"]["digest"])
        self.ok(table is not None, "predicate operand table is dangling")
        rows = [row for row in table["rows"] if row["query"] == evidence["query"] and row["input"] == evidence["input"] and row["bindingsDigest"] == evidence["bindingsDigest"]]
        self.ok(len(rows) == 1, "predicate operand has missing/ambiguous finite row")
        row = rows[0]
        self.ok(row["testInvocationDigest"] == operand["testInvocationDigest"] and row["subject"] == operand["subject"], "predicate operand selected another test/subject finite row")
        self.ok(row["producerTrace"] == evidence["producerTrace"], "predicate operand producer attempt differs from its finite row")
        self.validate_trace_subject(row["producerTrace"], operand["subject"], declaration)
        self.ok(normalized == {field: row[field] for field in ("query", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result")}, "predicate Bool/input/bindings projection is self-asserted")

    def crash_value(self, crash_key: dict[str, str]) -> tuple[Any, ...]:
        crash = self.crashes[crash_key["digest"]]
        terminal = self.terminals[crash["terminalState"]["digest"]]
        return crash["executionProfileDigest"], crash["classification"], terminal["value"]

    def expected_subject(self, side_name: str, expected_mutant: dict[str, Any] | None = None) -> dict[str, Any]:
        if side_name == "baseline":
            return {"side": "baseline", "definitionDigest": self.manifest["definitionDigest"]}
        mutant = expected_mutant
        self.ok(mutant is not None, "mutant side has no enclosing mutant")
        return {
            "side": "mutant",
            "baselineDefinitionDigest": self.manifest["definitionDigest"],
            "mutantId": mutant["mutantId"],
            "mutantDefinitionDigest": mutant["outputDefinitionDigest"],
        }

    def infer_mutant(self, side_value: dict[str, Any]) -> dict[str, Any]:
        if side_value["normalOperand"] is not None:
            operand = self.operands.get(side_value["normalOperand"]["digest"])
            self.ok(operand is not None and operand["subject"]["side"] == "mutant", "mutant normal side is dangling or relabeled")
            mutant = self.mutant_by_id.get(operand["subject"]["mutantId"])
            self.ok(mutant is not None, "mutant normal side names an unselected mutant")
            return mutant
        crash = self.crashes.get(side_value["semanticCrash"]["digest"])
        self.ok(crash is not None and crash["terminalState"]["digest"] in self.terminals, "mutant crash side is dangling")
        definition = self.terminals[crash["terminalState"]["digest"]]["definitionDigest"]
        matches = [mutant for mutant in self.campaign["mutants"] if mutant["outputDefinitionDigest"] == definition]
        self.ok(len(matches) == 1, "mutant crash side does not identify exactly one campaign mutant")
        return matches[0]

    def validate_side(
        self,
        side_value: dict[str, Any],
        declaration: dict[str, Any],
        expected_side: str,
        expected_mutant: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        self.ok(side_value["side"] == expected_side, "semantic side tag differs from its enclosing position")
        if expected_side == "mutant" and expected_mutant is None:
            expected_mutant = self.infer_mutant(side_value)
        subject = self.expected_subject(expected_side, expected_mutant)
        normal_key, crash_key = side_value["normalOperand"], side_value["semanticCrash"]
        self.ok((normal_key is None) != (crash_key is None), "semantic side does not contain exactly one normal/crash arm")
        if normal_key is not None:
            self.ok(normal_key["role"] == "oracle-operand", "normal side uses another artifact role")
            operand = self.operands.get(normal_key["digest"])
            self.ok(operand is not None, "normal semantic side is absent from the active catalog")
            self.ok(operand["declaration"] == key("oracle-declaration", declaration["declarationId"]), "normal semantic side belongs to another declaration")
            self.ok(operand["subject"] == subject, "normal semantic side belongs to another baseline/mutant subject")
            self.ok(all(operand[field] == declaration[field] for field in ("testInvocationDigest", "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest")), "normal semantic side invocation/profile roots drift")
            self.validate_operand(operand)
            return {"arm": "normal", "operand": operand, "side": side_value}
        self.ok(crash_key["role"] == "semantic-crash", "crash side uses another artifact role")
        crash = self.crashes.get(crash_key["digest"])
        self.ok(crash is not None, "semantic crash side is absent from the active catalog")
        self.ok(crash["crashDigest"] == digest("k-in-k/semantic-crash/v1", without(crash, "crashDigest")), "semantic crash side self identity drift")
        self.ok(crash["executionProfileDigest"] == declaration["executionProfileDigest"], "semantic crash side execution profile drift")
        terminal = self.terminals.get(crash["terminalState"]["digest"])
        self.ok(terminal is not None and terminal["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", without(terminal, "terminalStateDigest")), "semantic crash terminal is dangling or invalid")
        self.ok(terminal["definitionDigest"] == subject_definition(subject), "semantic crash terminal belongs to another definition side")
        test = self.tests_by_invocation[declaration["testInvocationDigest"]]
        producers = [
            trace for trace in self.traces.values()
            if trace.get("testId") == test["testId"]
            and trace.get("definitionDigest") == subject_definition(subject)
            and trace.get("complete") is True
            and trace.get("stopReason") == "terminal"
            and trace.get("executionTerminal") == {"kind": "semantic-crash", "artifact": crash_key}
        ]
        self.ok(len(producers) == 1, "semantic crash side lacks one exact cataloged producer attempt")
        return {"arm": "crash", "crash": crash, "terminal": terminal, "producerTrace": producers[0], "side": side_value}

    def derive_sides(self, declaration: dict[str, Any], left: dict[str, Any], right: dict[str, Any]) -> str:
        if left["arm"] == "crash" or right["arm"] == "crash":
            if left["arm"] == right["arm"] == "crash" and self.crash_value(left["side"]["semanticCrash"]) == self.crash_value(right["side"]["semanticCrash"]):
                return "agree"
            return "distinguish" if declaration["crashPolicy"] == "semantic-crash-distinguishes" else "incomparable"
        return self.comparator(declaration, left["operand"]["normalizedValue"], right["operand"]["normalizedValue"])

    def validate_comparison(self, comparison: dict[str, Any]) -> None:
        self.ok(comparison["comparisonId"] == digest("k-in-k/oracle-comparison-result/v1", without(comparison, "comparisonId")), "oracle comparison self ID drift")
        declaration = self.declarations.get(comparison["declaration"]["digest"])
        self.ok(declaration is not None, "comparison declaration dangling")
        mutant = self.infer_mutant(comparison["sides"][1])
        resolved = [
            self.validate_side(comparison["sides"][0], declaration, "baseline"),
            self.validate_side(comparison["sides"][1], declaration, "mutant", mutant),
        ]
        projection = declaration["projectionSpec"]["projectionId"]
        comparator = declaration["comparisonSpec"]["comparatorId"]
        self.ok(comparison["projectionId"] == projection and comparison["comparatorId"] == comparator, "comparison copied projection/comparator drift")
        expected_digests = []
        for side_value in resolved:
            if side_value["arm"] == "crash":
                expected_digests.append(None)
            else:
                operand = side_value["operand"]
                expected_digests.append(normalized_digest(declaration, operand["normalizedValue"]))
        self.ok(comparison["normalizedValueDigests"] == expected_digests, "comparison normalized-value digest is self-asserted or present on crash")
        self.ok(comparison["outcome"] == self.derive_sides(declaration, *resolved), "comparison outcome is not derived by crash truth table/kind comparator")

    def policy_admits(self, declaration: dict[str, Any], actual: dict[str, Any]) -> bool:
        actual_class = "crash" if actual["arm"] == "crash" else self.completion_class(actual["operand"])
        admitted = {
            "normal-only": {"normal"}, "normal-or-stuck": {"normal", "stuck"},
            "normal-or-crash": {"normal", "crash"}, "normal-stuck-or-crash": {"normal", "stuck", "crash"},
        }
        return actual_class in admitted[declaration["baselineTerminalPolicy"]]

    def validate_gate(self, gate: dict[str, Any]) -> None:
        self.ok(gate["gateResultId"] == digest("k-in-k/baseline-oracle-gate-result/v1", without(gate, "gateResultId")), "baseline gate self ID drift")
        declaration = self.declarations[gate["declaration"]["digest"]]
        actual = self.validate_side(gate["actualSide"], declaration, "baseline")
        admitted = self.policy_admits(declaration, actual)
        mode = declaration["baselineGate"]["mode"]
        assertion = None
        if mode == "assert":
            expected = declaration["baselineGate"]["expectedSide"]
            if expected.get("role") == "semantic-crash":
                expected_side = self.validate_side(side("baseline", crash=expected), declaration, "baseline")
            else:
                # Inline expected values deliberately have no operand identity.
                if actual["arm"] == "crash":
                    assertion = "distinguish" if declaration["crashPolicy"] == "semantic-crash-distinguishes" else "incomparable"
                else:
                    actual_value = actual["operand"]["normalizedValue"]
                    assertion = self.comparator(declaration, expected["normalizedValue"], actual_value)
                expected_side = None
            if expected_side is not None:
                assertion = self.derive_sides(declaration, expected_side, actual)
        self.ok(gate["assertionOutcome"] == assertion, "baseline assertion outcome drift/recopied expectation")
        accepted = admitted and (mode == "reference-only" or assertion == "agree")
        self.ok(gate["status"] == ("accepted" if accepted else "error"), "baseline gate status is not derived")
        if accepted:
            self.ok(gate["failure"] is None, "accepted baseline gate retained failure")
        else:
            failure_value = gate["failure"]
            self.ok(failure_value is not None and (failure_value["stage"], failure_value["classification"], failure_value["context"], failure_value["scope"]) == ("oracle", "baseline-mismatch", "baseline-oracle-gate", "campaign"), "rejected baseline gate lacks exact baseline-mismatch placement")

    def failure_outcome(self, wrapper: dict[str, Any]) -> str:
        source = wrapper["sourceSide"]
        failure_value = wrapper["failure"]
        expected_context = {
            "baseline-execution": ("baseline-execution", "campaign"),
            "baseline-operand-production": ("oracle-operand-production", "test"),
            "mutant-execution": ("mutant-execution", "mutant"),
            "mutant-operand-production": ("oracle-operand-production", "test"),
            "comparison": ("oracle-comparison", "mutant"),
        }
        self.ok((failure_value["context"], failure_value["scope"]) == expected_context[source], "oracle failure source/context/scope cross-product drift")
        matches = [
            (entry, placement)
            for entry in self.taxonomy["entries"]
            if (entry["stage"], entry["classification"]) == (failure_value["stage"], failure_value["classification"])
            for placement in entry["placements"]
            if (placement["context"], placement["scope"]) == (failure_value["context"], failure_value["scope"])
        ]
        self.ok(len(matches) == 1, "oracle failure has no exact active-taxonomy placement")
        entry, placement = matches[0]
        self.ok(failure_value["retryability"] == entry["retryability"], "oracle failure retryability differs from active taxonomy")
        disposition = placement["consequence"]["disposition"]
        if failure_value["classification"] == "incomparable-result" and disposition == "error":
            return "incomparable"
        return "error" if disposition in {"baseline-invalid", "baseline-oracle-failed", "invalid", "rejected"} else disposition

    def validate_outer_result(self, result: dict[str, Any], expected_mutant: dict[str, Any] | None = None) -> None:
        declaration = self.declarations.get(result["declaration"]["digest"])
        self.ok(declaration is not None, "outer oracle result declaration dangling")
        left, right, comparison_key, wrapper, outcome = result["baselineSide"], result["mutantSide"], result["comparison"], result["failure"], result["outcome"]
        if outcome == "skipped":
            self.ok(left is None and right is None and comparison_key is None and wrapper is None, "skipped oracle retained side/comparison/failure")
            return
        if wrapper is not None:
            source = wrapper["sourceSide"]
            failure_value = wrapper["failure"]
            if source in {"baseline-execution", "baseline-operand-production"}:
                self.ok(left is None and right is None, "baseline-side failure retained an operand")
            elif source in {"mutant-execution", "mutant-operand-production"}:
                self.ok(left is not None and right is None, "mutant-side failure omitted baseline or retained mutant operand")
                self.validate_side(left, declaration, "baseline")
            else:
                self.ok(left is not None and right is not None, "comparison failure lacks both complete sides")
                mutant = expected_mutant or self.infer_mutant(right)
                self.validate_side(left, declaration, "baseline")
                self.validate_side(right, declaration, "mutant", mutant)
            if failure_value["classification"] == "incomparable-result":
                self.ok(source == "comparison" and comparison_key is not None, "incomparable result omitted its exact comparison artifact")
                comparison = self.comparisons.get(comparison_key["digest"])
                self.ok(comparison is not None and comparison["declaration"] == result["declaration"] and comparison["sides"] == [left, right], "incomparable result comparison does not retain the exact sides/declaration")
                self.validate_comparison(comparison)
                self.ok(comparison["outcome"] == "incomparable", "incomparable wrapper retained another comparison outcome")
            else:
                self.ok(comparison_key is None, "failed outer oracle retained comparison artifact")
            self.ok(outcome == self.failure_outcome(wrapper), "outer failure disposition differs from active taxonomy")
            return
        self.ok(left is not None and right is not None and comparison_key is not None, "conclusive outer oracle lacks two sides/comparison")
        mutant = expected_mutant or self.infer_mutant(right)
        self.validate_side(left, declaration, "baseline")
        self.validate_side(right, declaration, "mutant", mutant)
        comparison = self.comparisons.get(comparison_key["digest"])
        self.ok(comparison is not None and comparison["declaration"] == result["declaration"] and comparison["sides"] == [left, right], "outer result comparison does not bind exact sides/declaration")
        self.validate_comparison(comparison)
        self.ok(outcome == comparison["outcome"], "outer result outcome differs from comparison")
        self.ok(outcome in {"agree", "distinguish"}, "incomparable comparison omitted its BAG-10 failure")

    def validate_campaign(self) -> None:
        self.ok(self.campaign["manifestDigest"] == self.manifest["manifestId"], "campaign references another typed manifest")
        self.ok(self.campaign["campaignId"] == digest("k-in-k/mutation-campaign/v1", {"manifestDigest": self.campaign["manifestDigest"], "operator": self.campaign["operator"], "scheduleMode": self.campaign["scheduleMode"]}), "campaign ID did not propagate typed manifest")
        self.ok(self.campaign["reportId"] == digest("k-in-k/mutation-report/v1", without(self.campaign, "reportId")), "report ID did not propagate typed oracle results")
        manifest_flat = [item for test in self.manifest["tests"] for item in test["oracleDeclarations"]]
        self.ok(self.campaign["selectedTestIds"] == [test["testId"] for test in self.manifest["tests"]], "campaign selected test IDs differ from manifest order")
        self.ok(self.campaign["baseline"]["definitionDigest"] == self.manifest["definitionDigest"], "campaign baseline definition differs from manifest")
        baseline_tests = self.campaign["baseline"]["tests"]
        self.ok(len(baseline_tests) == len(self.manifest["tests"]), "baseline report test coverage drift")
        for reported, selected in zip(baseline_tests, self.manifest["tests"]):
            self.ok(reported["id"] == selected["testId"] and reported["oracleDeclarations"] == selected["oracleDeclarations"], "baseline report test ID/declaration roots drift")
        reported_test_flat = [item for test in baseline_tests for item in test["oracleDeclarations"]]
        self.ok(reported_test_flat == manifest_flat, "baseline report omitted/duplicated/reordered oracle slots")
        gates = [self.gates[item["digest"]] for item in self.campaign["baseline"]["oracleGateResults"]]
        self.ok([item["declaration"] for item in gates] == manifest_flat, "baseline gates do not exactly cover declaration slot order")
        for gate in gates:
            self.validate_gate(gate)
        rejected = [gate for gate in gates if gate["status"] == "error"]
        if rejected:
            self.ok(self.campaign["baseline"]["status"] == "baseline-oracle-failed", "rejected baseline gate did not abort baseline validity")
            self.ok(self.campaign["campaignStatus"] == "baseline-oracle-failed" and not self.campaign["mutants"] and "score" not in self.campaign, "rejected baseline gate retained mutant scoring")
            expected_failures = [gate["failure"] for gate in rejected]
            self.ok(self.campaign["baseline"]["failures"] == expected_failures, "baseline gate abort failure set drift")
            return
        self.ok(self.campaign["baseline"]["status"] == "valid" and not self.campaign["baseline"]["failures"], "accepted baseline gates did not derive a valid baseline")
        self.ok(self.campaign["campaignStatus"] == "complete", "fully scored typed campaign is not complete")
        for mutant in self.campaign["mutants"]:
            manifest_tests = {test["testId"]: test for test in self.manifest["tests"]}
            self.ok([test["id"] for test in mutant["tests"]] == [test["testId"] for test in self.manifest["tests"]], "mutant report test IDs omit/reorder the manifest")
            for report_test in mutant["tests"]:
                selected_test = manifest_tests[report_test["id"]]
                self.ok(report_test["boundsDigest"] == selected_test["boundsDigest"] and report_test["invocationDigest"] == selected_test["invocationDigest"] and report_test["oracleDeclarations"] == selected_test["oracleDeclarations"], "mutant report test invocation/declaration roots drift")
            selected = [item for test in mutant["tests"] if test["selected"] for item in test["oracleDeclarations"]]
            self.ok([item["declaration"] for item in mutant["oracleResults"]] == selected, "mutant oracle results do not preserve selected test/slot order")
            for result in mutant["oracleResults"]:
                self.validate_outer_result(result, mutant)
            statuses = [item["outcome"] for item in mutant["oracleResults"]]
            expected = "killed" if "distinguish" in statuses else "survived" if statuses and all(item == "agree" for item in statuses) else next((item for item in ("timeout", "unknown", "error") if item in statuses), "error")
            self.ok(mutant["status"] == expected, "mutant status/kill is not folded from every selected typed oracle")
            offset = 0
            for report_test in mutant["tests"]:
                count = len(report_test["oracleDeclarations"]) if report_test["selected"] else 0
                test_outcomes = statuses[offset:offset + count]
                offset += count
                expected_test = "skipped" if not report_test["selected"] else "kill" if "distinguish" in test_outcomes else "agree" if test_outcomes and all(item == "agree" for item in test_outcomes) else next((item for item in ("timeout", "unknown", "error") if item in test_outcomes), "error")
                self.ok(report_test["status"] == expected_test, "mutant test status is not folded from its typed oracle slots")
        statuses = [mutant["status"] for mutant in self.campaign["mutants"]]
        killed, survived = statuses.count("killed"), statuses.count("survived")
        denominator = killed + survived
        excluded = {name: statuses.count(name) for name in ("invalid", "timeout", "unknown", "error")}
        excluded.update({name: sum(item["status"] == name for item in self.campaign["candidateRejections"]) for name in ("duplicate", "no-change")})
        ratio = None if denominator == 0 else {"numerator": killed // math.gcd(killed, denominator), "denominator": denominator // math.gcd(killed, denominator)}
        expected_score = {"killed": killed, "survived": survived, "denominator": denominator, "ratio": ratio, "excluded": excluded}
        self.ok(self.campaign.get("score") == expected_score, "campaign mutation score/counts/exclusions are not derived")

    def validate_cache(self, policy: dict[str, Any] | None = None) -> None:
        policy = read_json(self.fixtures / "mutation-execution-policy.json") if policy is None else policy
        isolation = policy["isolationPolicy"]
        self.ok(isolation == {
            "schemaVersion": 1,
            "isolationPolicyDigest": digest("k-in-k/isolation-policy/v1", without(isolation, "isolationPolicyDigest")),
            "baselineState": "immutable",
            "mutantState": "fresh-per-mutant",
            "sharedWritableState": False,
            "observerState": "fresh-per-test-path",
        }, "mutation execution policy does not embed the exact BAG-14 isolation policy")
        self.ok(policy["policyId"] == digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId")), "mutation execution policy ID derivation drift")

    def validate_vectors(self) -> None:
        vectors = read_json(self.root / "vectors" / "oracle-semantics-vectors.json")
        registered = {(item["kind"], item["projectionId"], item["comparatorId"]) for item in vectors["registry"]}
        expected = {(kind, projection, comparator) for kind, pairs in REGISTRY.items() for projection, comparator in pairs}
        self.ok(registered == expected, "portable oracle registry vector is incomplete/open")
        cases = vectors["evidenceCases"]
        self.ok(len(cases) == len({item["id"] for item in cases}), "end-to-end evidence case IDs are duplicate")
        seen = []
        nonordinary_gate = False
        asserted_gate = False
        mutant = next(iter(self.campaign["mutants"]))
        for case in cases:
            declaration = self.declarations.get(case["declaration"]["digest"])
            self.ok(declaration is not None, f"{case['id']} declaration is absent from active catalog")
            self.validate_declaration(declaration)
            self.ok((case["kind"], case["projectionId"], case["comparatorId"]) == (declaration["kind"], declaration["projectionSpec"].get("projectionId"), declaration["comparisonSpec"].get("comparatorId")), f"{case['id']} vector metadata differs from its declaration")
            gate = self.gates.get(case["baselineGate"]["digest"])
            self.ok(gate is not None and gate["declaration"] == case["declaration"], f"{case['id']} gate is dangling or cross-declaration")
            self.validate_gate(gate)
            self.ok(gate["status"] == "accepted", f"{case['id']} positive baseline gate was not accepted")
            asserted_gate |= declaration["baselineGate"]["mode"] == "assert"
            resolved_baseline = self.validate_side(gate["actualSide"], declaration, "baseline")
            nonordinary_gate |= resolved_baseline["arm"] == "crash" or resolved_baseline["arm"] == "normal" and self.completion_class(resolved_baseline["operand"]) == "stuck"
            if case["baselineOperand"] is not None:
                self.ok(gate["actualSide"]["normalOperand"] == case["baselineOperand"], f"{case['id']} baseline evidence key drift")
            if case["mutantOperand"] is not None:
                self.ok(case["mutantOperand"]["digest"] in self.operands, f"{case['id']} mutant operand is absent from active catalog")
            if case["comparison"] is None:
                self.ok(case["expectedOutcome"] == "unknown", f"{case['id']} omitted comparison outside an incomplete case")
            else:
                comparison = self.comparisons.get(case["comparison"]["digest"])
                self.ok(comparison is not None and comparison["declaration"] == case["declaration"], f"{case['id']} comparison is dangling/cross-declaration")
                self.validate_comparison(comparison)
                self.ok(comparison["outcome"] == case["expectedOutcome"], f"{case['id']} expected comparison outcome drift")
            self.ok(case["outerResult"]["declaration"] == case["declaration"] and case["outerResult"]["outcome"] == case["expectedOutcome"], f"{case['id']} outer result metadata drift")
            self.validate_outer_result(case["outerResult"], mutant)
            seen.append((case["kind"], case["projectionId"], case["comparatorId"], case["expectedOutcome"]))
        expected_pairs = {(kind, projection, comparator, outcome) for kind, pairs in REGISTRY.items() for projection, comparator in pairs for outcome in ("agree", "distinguish")}
        self.ok(expected_pairs <= set(seen), "not every built-in pair has end-to-end agree and distinguish evidence")
        incomparable = [case for case in cases if case["expectedOutcome"] == "incomparable"]
        orientations = {
            "baseline-crash" if case["outerResult"]["baselineSide"]["semanticCrash"] is not None else "baseline-normal"
            for case in incomparable
        }
        self.ok(orientations == {"baseline-normal", "baseline-crash"}, "two-orientation incomparable end-to-end evidence is missing")
        self.ok({case["kind"] for case in cases if case["expectedOutcome"] == "unknown"} == {"reachability", "structured-predicate"}, "reachability/predicate incomplete evidence is missing")
        self.ok({case["kind"] for case in cases} == set(KINDS), "not all six oracle kinds have end-to-end evidence")
        self.ok(nonordinary_gate, "no non-ordinary baseline side is accepted end to end")
        self.ok(asserted_gate, "no kind-correct asserted normal baseline gate is accepted end to end")
        inline_cases = vectors["inlineExpectationCases"]
        inline_pairs = {(case["kind"], case["projectionId"], case["comparatorId"]) for case in inline_cases}
        self.ok(inline_pairs == expected and len(inline_cases) == len(expected), "inline expectation positives do not cover every portable built-in pair exactly once")
        for case in inline_cases:
            declaration = self.declarations.get(case["declaration"]["digest"])
            operand = self.operands.get(case["baselineOperand"]["digest"])
            self.ok(declaration is not None and operand is not None, f"{case['id']} inline expectation roots are dangling")
            expected_side = case["expectedSide"]
            self.ok(expected_side["kind"] == declaration["kind"] and operand["declaration"] == case["declaration"] and operand["subject"]["side"] == "baseline", f"{case['id']} inline expectation belongs to another kind/declaration/side")
            self.validate_expected_normal_value(declaration, expected_side["normalizedValue"])
            self.ok(self.comparator(declaration, expected_side["normalizedValue"], operand["normalizedValue"]) == "agree", f"{case['id']} valid inline expectation did not agree")
        incomplete = {(item["failure"]["stage"], item["failure"]["classification"], item["failure"]["context"], item["expected"]) for item in vectors["incompleteCases"]}
        self.ok({("oracle", "evaluator-unavailable", "oracle-operand-production", "unknown"), ("oracle", "projection-invalid", "oracle-operand-production", "error"), ("input", "missing-artifact", "oracle-operand-production", "error"), ("execution", "solver-unknown", "oracle-operand-production", "unknown")} <= incomplete, "BAG-10 operand-production incomplete placements missing")
        advertised = [(item["id"], item["probe"]) for item in vectors["adversaries"]]
        self.ok(len(advertised) == len(set(advertised)) and len({item[0] for item in advertised}) == len(advertised), "advertised adversary IDs/probes are duplicate")
        self.ok(set(advertised) == {(name, name) for name in self.adversary_probes()}, "advertised adversary registry differs from executable probes")

    def expect_rejection(self, checker: Callable[[Any], None], value: Any, message: str) -> None:
        try:
            checker(value)
        except (AssertionError, KeyError, TypeError, ValueError, UnicodeDecodeError):
            self.ok(True, message)
        else:
            raise AssertionError(message)

    def expect_registered_rejection(
        self,
        registry: dict[str, dict[str, Any]],
        role: str,
        identity_field: str,
        domain: str,
        value: dict[str, Any],
        checker: Callable[[dict[str, Any]], None],
        message: str,
    ) -> None:
        value[identity_field] = digest(domain, without(value, identity_field))
        identity = value[identity_field]
        registry[identity] = value
        self.catalog_entries[(role, identity)] = {"role": role, "digest": identity}
        try:
            self.expect_rejection(checker, value, message)
        finally:
            registry.pop(identity, None)
            self.catalog_entries.pop((role, identity), None)

    def adversary_probes(self) -> dict[str, Callable[[], None]]:
        mutant = next(iter(self.campaign["mutants"]))
        normal_comparison = next(item for item in self.comparisons.values() if all(side_value["normalOperand"] is not None for side_value in item["sides"]))
        crash_comparison = next(item for item in self.comparisons.values() if any(side_value["semanticCrash"] is not None for side_value in item["sides"]))
        pattern_operand = next(item for item in self.operands.values() if self.declarations[item["declaration"]["digest"]]["kind"] == "execution-pattern")
        output_operand = next(item for item in self.operands.values() if self.declarations[item["declaration"]["digest"]]["kind"] == "concrete-output")
        reach_operand = next(item for item in self.operands.values() if self.declarations[item["declaration"]["digest"]]["kind"] == "reachability" and item["subject"]["side"] == "baseline")
        predicate_operand = next(item for item in self.operands.values() if self.declarations[item["declaration"]["digest"]]["kind"] == "structured-predicate" and item["subject"]["side"] == "baseline")

        def catalog_removal(role: str, identity: str, registry: dict[str, dict[str, Any]] | None, checker: Callable[[], None], label: str) -> None:
            entry = self.catalog_entries.pop((role, identity))
            value = None if registry is None else registry.pop(identity)
            try:
                self.expect_rejection(lambda _: checker(), None, label)
            finally:
                self.catalog_entries[(role, identity)] = entry
                if registry is not None and value is not None:
                    registry[identity] = value

        def registered_declaration(bad: dict[str, Any], message: str) -> None:
            self.expect_registered_rejection(self.declarations, "oracle-declaration", "declarationId", "k-in-k/oracle-declaration/v1", bad, self.validate_declaration, message)

        def registered_operand(bad: dict[str, Any], message: str) -> None:
            self.expect_registered_rejection(self.operands, "oracle-operand", "operandId", "k-in-k/oracle-operand/v1", bad, self.validate_operand, message)

        def catalog_corpus() -> None:
            catalog_removal("corpus-manifest", self.corpus["manifestId"], None, self.validate_manifest, "catalog corpus removal survived")

        def catalog_declaration() -> None:
            identity = normal_comparison["declaration"]["digest"]
            catalog_removal("oracle-declaration", identity, self.declarations, self.validate_manifest, "catalog declaration removal survived")

        def catalog_operand() -> None:
            identity = normal_comparison["sides"][0]["normalOperand"]["digest"]
            catalog_removal("oracle-operand", identity, self.operands, lambda: self.validate_comparison(normal_comparison), "catalog operand removal survived")

        def catalog_crash() -> None:
            crash_key = next(side_value["semanticCrash"] for side_value in crash_comparison["sides"] if side_value["semanticCrash"] is not None)
            catalog_removal("semantic-crash", crash_key["digest"], self.crashes, lambda: self.validate_comparison(crash_comparison), "catalog crash removal survived")

        def cross_vocabulary() -> None:
            declaration = self.declarations[pattern_operand["declaration"]["digest"]]
            original = self.observation
            changed = deepcopy(original)
            changed["eventVocabulary"].append("bag12-different-vocabulary-event")
            changed["eventVocabularyDigest"] = digest("k-in-k/event-vocabulary/v1", changed["eventVocabulary"])
            self.observation = changed
            try:
                self.expect_rejection(self.validate_declaration, declaration, "cross-corpus vocabulary survived")
            finally:
                self.observation = original

        def stale_invocation() -> None:
            bad = deepcopy(self.manifest)
            bad["tests"][0]["programDigest"] = "f" * 64
            bad["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(bad, "manifestId"))
            self.expect_rejection(self.validate_manifest, bad, "stale invocation survived changed test roots")

        def stale_test_id() -> None:
            bad = deepcopy(self.manifest)
            bad["tests"][0]["testId"] += "-drift"
            bad["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(bad, "manifestId"))
            self.expect_rejection(self.validate_manifest, bad, "changed test ID survived stale invocation")

        def replay_wrong_test() -> None:
            declaration = self.declarations[pattern_operand["declaration"]["digest"]]
            result = deepcopy(self.patterns[pattern_operand["completionEvidence"]["patternResult"]["digest"]])
            replay = deepcopy(next(item for item in self.replays.values() if item["invocationDigest"] == result["inputs"]["replayInvocationDigest"]))
            other_test = next(test for test in self.manifest["tests"] if test["testId"] != replay["testId"])
            replay["testId"] = other_test["testId"]
            replay["invocationDigest"] = digest("k-in-k/replay-invocation/v1", self.replay_invocation_payload(replay))
            result["inputs"]["replayInvocationDigest"] = replay["invocationDigest"]
            result["resultId"] = digest("k-in-k/pattern-result/v1", without(result, "resultId"))
            replay["expectedResultDigest"] = result["resultId"]
            replay["replayId"] = digest("k-in-k/replay-manifest/v1", without(replay, "replayId"))
            self.replays[replay["replayId"]] = replay
            try:
                self.expect_rejection(lambda value: self.validate_pattern_producer(value, declaration, pattern_operand["subject"]), result, "replay wrong-test drift survived")
            finally:
                self.replays.pop(replay["replayId"], None)

        def pattern_drift() -> None:
            declaration = self.declarations[pattern_operand["declaration"]["digest"]]
            result = deepcopy(self.patterns[pattern_operand["completionEvidence"]["patternResult"]["digest"]])
            result["inputs"]["searchPolicy"] = "existential-first" if result["inputs"]["searchPolicy"] == "exhaustive" else "exhaustive"
            self.expect_rejection(lambda value: self.validate_pattern_operand(pattern_operand, declaration, value), result, "pattern query/plan/search drift survived")

        def side_reversal() -> None:
            bad = deepcopy(normal_comparison)
            bad["sides"].reverse()
            bad["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(bad, "comparisonId"))
            self.expect_rejection(self.validate_comparison, bad, "side reversal survived")

        def normal_subject_swap() -> None:
            bad = deepcopy(normal_comparison)
            bad["sides"][0]["normalOperand"] = deepcopy(bad["sides"][1]["normalOperand"])
            bad["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(bad, "comparisonId"))
            self.expect_rejection(self.validate_comparison, bad, "normal subject swap survived")

        def crash_swap() -> None:
            bad = deepcopy(crash_comparison)
            index = next(index for index, item in enumerate(bad["sides"]) if item["semanticCrash"] is not None)
            opposite = "mutant" if index == 0 else "baseline"
            bad["sides"][index]["semanticCrash"] = key("semantic-crash", next(crash["crashDigest"] for crash in self.crashes.values() if self.terminals[crash["terminalState"]["digest"]]["definitionDigest"] == subject_definition(self.expected_subject(opposite, mutant if opposite == "mutant" else None))))
            bad["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(bad, "comparisonId"))
            self.expect_rejection(self.validate_comparison, bad, "cross-definition crash provenance swap survived")

        def terminal_relabel() -> None:
            operand = next(item for item in self.operands.values() if item["completionEvidence"]["kind"] == "execution-terminal" and item["completionEvidence"]["terminal"]["kind"] == "normal")
            bad = deepcopy(operand)
            bad["completionEvidence"]["terminal"]["kind"] = "stuck"
            registered_operand(bad, "inline terminal relabel survived producer trace")

        def reach_cross_side() -> None:
            declaration = self.declarations[reach_operand["declaration"]["digest"]]
            table = self.reach_tables[reach_operand["completionEvidence"]["table"]["digest"]]
            row = next(row for row in table["rows"] if row["query"] == reach_operand["completionEvidence"]["query"] and row["subject"]["side"] == "mutant")
            bad = deepcopy(reach_operand)
            bad["completionEvidence"].update({"inputVectorDigest": row["inputVectorDigest"], "producerTraces": deepcopy(row["producerTraces"])})
            bad["normalizedValue"] = {"status": "reached" if row["witnesses"] else "not-reached", "witnesses": deepcopy(row["witnesses"])}
            registered_operand(bad, "reachability cross-side finite row survived")

        def predicate_sort() -> None:
            table = deepcopy(next(iter(self.predicate_tables.values())))
            table["rows"][0]["bindings"][0]["term"]["sort"] += "Drift"
            table["rows"][0]["bindingsDigest"] = digest("k-in-k/bindings/v1", table["rows"][0]["bindings"])
            table["tableId"] = digest("k-in-k/predicate-conformance-table/v1", without(table, "tableId"))
            original = self.predicate_tables
            self.predicate_tables = {table["tableId"]: table}
            try:
                self.expect_rejection(lambda _: self.validate_predicate_assets(), None, "predicate binding sort drift survived")
            finally:
                self.predicate_tables = original

        def predicate_input_side() -> None:
            table = self.predicate_tables[predicate_operand["completionEvidence"]["table"]["digest"]]
            row = next(row for row in table["rows"] if row["query"] == predicate_operand["completionEvidence"]["query"] and row["subject"]["side"] == "mutant")
            bad = deepcopy(predicate_operand)
            bad["completionEvidence"].update({"input": deepcopy(row["input"]), "bindingsDigest": row["bindingsDigest"], "producerTrace": deepcopy(row["producerTrace"])})
            bad["normalizedValue"] = {field: deepcopy(row[field]) for field in ("query", "input", "inputProjectionDigest", "bindings", "bindingsDigest", "result")}
            registered_operand(bad, "predicate cross-side input survived")

        def output_other_subject() -> None:
            table = self.output_tables[output_operand["completionEvidence"]["table"]["digest"]]
            declaration_key = output_operand["declaration"]
            row = next(row for row in table["rows"] if row["declaration"] == declaration_key and row["subject"]["side"] != output_operand["subject"]["side"])
            bad = deepcopy(output_operand)
            bad["completionEvidence"]["rowId"] = row["rowId"]
            bad["normalizedValue"] = {"channels": deepcopy(row["channels"])}
            registered_operand(bad, "semantic output from another subject survived")

        def gate_mutant() -> None:
            declaration = self.declarations[normal_comparison["declaration"]["digest"]]
            gate = next(item for item in self.gates.values() if item["declaration"] == normal_comparison["declaration"])
            bad = deepcopy(gate)
            bad["actualSide"] = deepcopy(normal_comparison["sides"][1])
            bad["gateResultId"] = digest("k-in-k/baseline-oracle-gate-result/v1", without(bad, "gateResultId"))
            self.expect_rejection(self.validate_gate, bad, "mutant operand tagged as baseline gate side survived")

        def gate_abort_scoring() -> None:
            gate_key = self.campaign["baseline"]["oracleGateResults"][0]
            original_gate = self.gates[gate_key["digest"]]
            bad_gate = deepcopy(original_gate)
            baseline_crash = next(
                crash for crash in self.crashes.values()
                if self.terminals[crash["terminalState"]["digest"]]["definitionDigest"] == self.manifest["definitionDigest"]
            )
            bad_gate.update({
                "actualSide": side("baseline", crash=key("semantic-crash", baseline_crash["crashDigest"])),
                "assertionOutcome": "distinguish",
                "status": "error",
                "failure": {"stage": "oracle", "classification": "baseline-mismatch", "context": "baseline-oracle-gate", "scope": "campaign", "retryability": "never", "semanticEvidence": [], "details": {}},
            })
            bad_gate["gateResultId"] = digest("k-in-k/baseline-oracle-gate-result/v1", without(bad_gate, "gateResultId"))
            self.validate_gate(bad_gate)
            bad_campaign = deepcopy(self.campaign)
            bad_campaign["baseline"]["oracleGateResults"][0] = key("baseline-oracle-gate-result", bad_gate["gateResultId"])
            bad_campaign["reportId"] = digest("k-in-k/mutation-report/v1", without(bad_campaign, "reportId"))
            original_campaign = self.campaign
            self.campaign = bad_campaign
            self.gates[bad_gate["gateResultId"]] = bad_gate
            try:
                self.expect_rejection(lambda _: self.validate_campaign(), None, "gate error retained valid/scored mutants")
            finally:
                self.campaign = original_campaign
                self.gates.pop(bad_gate["gateResultId"], None)

        def failure_source_context() -> None:
            outer = deepcopy(next(item for item in mutant["oracleResults"] if item["failure"] is not None and item["failure"]["sourceSide"] == "mutant-operand-production"))
            outer["failure"]["sourceSide"] = "baseline-operand-production"
            self.expect_rejection(lambda value: self.validate_outer_result(value, mutant), outer, "failure source/context cross-product survived")

        def resource_disposition() -> None:
            outer = deepcopy(next(item for item in mutant["oracleResults"] if item["failure"] is not None and item["failure"]["sourceSide"] == "mutant-operand-production"))
            outer.update({"outcome": "error", "failure": {"sourceSide": "mutant-execution", "failure": {"stage": "execution", "classification": "resource-limit", "context": "mutant-execution", "scope": "mutant", "retryability": "same-input-after-resource-change", "semanticEvidence": [], "details": {}}}})
            self.expect_rejection(lambda value: self.validate_outer_result(value, mutant), outer, "resource-limit was not taxonomy-derived unknown")

        def incomparable_missing(field: str) -> None:
            outer = deepcopy(next(item for item in mutant["oracleResults"] if item["outcome"] == "incomparable"))
            outer[field] = None
            self.expect_rejection(lambda value: self.validate_outer_result(value, mutant), outer, f"incomparable missing {field} survived")

        def arbitrary_k_role() -> None:
            declaration = deepcopy(next(iter(self.declarations.values())))
            declaration["projectionSpec"] = {"mode": "k-authored", "source": key("pattern-source", "a" * 64), "plan": key("pattern-plan", "b" * 64), "query": key("pattern-query", "c" * 64), "conformanceRequirement": "rust-proof-required"}
            declaration["comparisonSpec"] = {"mode": "k-authored", "comparisonArtifact": key("oracle-comparison", "d" * 64), "conformanceRequirement": "rust-proof-required"}
            registered_declaration(declaration, "arbitrary K operation roles survived")

        def missing_production() -> None:
            record = deepcopy(next(iter(self.conformances.values())))
            record["result"] = "conformant"
            expected = {field: deepcopy(record[field]) for field in ("operationKind", "source", "plan", "query", "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest")}
            self.expect_registered_rejection(self.conformances, "oracle-evaluator-conformance", "conformanceId", "k-in-k/oracle-evaluator-conformance/v1", record, lambda value: self.authorize_evaluator(value, expected), "conformant record without BAG-15 production receipt survived")

        def nonconformant() -> None:
            record = next(iter(self.conformances.values()))
            expected = {field: deepcopy(record[field]) for field in ("operationKind", "source", "plan", "query", "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest")}
            self.expect_rejection(lambda value: self.authorize_evaluator(value, expected), record, "nonconformant evaluator authorized a decision")

        def receipt_as_conformance() -> None:
            self.api["expect_schema_rejection"](read_json(self.fixtures / "mutant-cycle-lowering-proof-check-receipt.json"), "oracle-semantics.schema.json", "BAG-15-like receipt was accepted as evaluator conformance")

        def expected_kind() -> None:
            declaration = deepcopy(next(item for item in self.declarations.values() if item["baselineGate"]["mode"] == "assert"))
            declaration["baselineGate"]["expectedSide"]["kind"] = "final-result"
            registered_declaration(declaration, "wrong expected normal oracle kind survived")

        def expected_value_integrity() -> None:
            baseline_operands = {
                kind: next(
                    operand for operand in self.operands.values()
                    if operand["subject"]["side"] == "baseline"
                    and self.declarations[operand["declaration"]["digest"]]["kind"] == kind
                )
                for kind in KINDS
            }
            for kind, operand in baseline_operands.items():
                declaration = deepcopy(self.declarations[operand["declaration"]["digest"]])
                expected = deepcopy(operand["normalizedValue"])
                declaration["baselineGate"] = {"mode": "assert", "expectedSide": {"kind": kind, "normalizedValue": expected}}
                if kind == "exit-stop":
                    expected["exitCode"] = 0 if declaration["kindConfig"]["exitCodeMode"] == "none" else None
                elif kind == "final-result":
                    expected["terminalState"]["digest"] = "f" * 64
                elif kind == "concrete-output":
                    expected["channels"][0]["contentSha256"] = "f" * 64
                elif kind == "reachability":
                    if expected["witnesses"]:
                        expected["witnesses"][0]["digest"] = "f" * 64
                    else:
                        expected["witnesses"].append(key("reachability-witness", "f" * 64))
                elif kind == "execution-pattern":
                    expected["patternResult"]["digest"] = "f" * 64
                else:
                    expected["inputProjectionDigest"] = "f" * 64
                if kind != "exit-stop":
                    self.ok(self.comparator(declaration, expected, operand["normalizedValue"]) == "agree", f"{kind} integrity adversary did not preserve the compared projection")
                registered_declaration(declaration, f"invalid inline expected {kind} value survived kind-specific validation")
                if kind == "structured-predicate":
                    result_declaration = deepcopy(self.declarations[operand["declaration"]["digest"]])
                    result_expected = deepcopy(operand["normalizedValue"])
                    result_expected["result"] = not result_expected["result"]
                    result_declaration["baselineGate"] = {
                        "mode": "assert",
                        "expectedSide": {"kind": kind, "normalizedValue": result_expected},
                    }
                    registered_declaration(result_declaration, "self-asserted inline expected predicate result survived finite authority validation")

        def comparison_assertion() -> None:
            bad = deepcopy(normal_comparison)
            bad["outcome"] = "distinguish" if bad["outcome"] == "agree" else "agree"
            bad["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(bad, "comparisonId"))
            self.expect_rejection(self.validate_comparison, bad, "self-asserted comparison outcome survived")

        def manifest_slot_order() -> None:
            bad = deepcopy(self.manifest)
            target = next(test for test in bad["tests"] if len(test["oracleDeclarations"]) > 1)
            target["oracleDeclarations"].reverse()
            bad["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(bad, "manifestId"))
            self.expect_rejection(self.validate_manifest, bad, "manifest slot order drift survived")

        def execution_policy_isolation_root() -> None:
            policy = read_json(self.fixtures / "mutation-execution-policy.json")
            policy["isolationPolicy"]["observerState"] = "fresh-per-mutant"
            policy["isolationPolicy"]["isolationPolicyDigest"] = digest("k-in-k/isolation-policy/v1", without(policy["isolationPolicy"], "isolationPolicyDigest"))
            policy["policyId"] = digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId"))
            self.expect_rejection(self.validate_cache, policy, "execution policy isolation drift survived")

        def campaign_test_root() -> None:
            bad = deepcopy(self.campaign)
            bad["mutants"][0]["tests"][0]["invocationDigest"] = "f" * 64
            bad["reportId"] = digest("k-in-k/mutation-report/v1", without(bad, "reportId"))
            original = self.campaign
            self.campaign = bad
            try:
                self.expect_rejection(lambda _: self.validate_campaign(), None, "campaign report test invocation drift survived")
            finally:
                self.campaign = original

        def global_join() -> None:
            bad = deepcopy(self.manifest)
            bad["oracles"] = []
            self.api["expect_schema_rejection"](bad, "mutation-manifest.schema.json", "global oracle join schema survived")

        def incomplete_absence() -> None:
            table = deepcopy(next(iter(self.reach_tables.values())))
            row = next(item for item in table["rows"] if not item["witnesses"])
            row["finiteComplete"] = False
            row["inputVectorDigest"] = digest("k-in-k/reachability-finite-input/v1", {"terminalStates": row["terminalStates"], "finiteComplete": False})
            table["tableId"] = digest("k-in-k/reachability-conformance-table/v1", without(table, "tableId"))
            original = self.reach_tables
            self.reach_tables = {table["tableId"]: table}
            try:
                self.expect_rejection(lambda _: self.validate_reachability_assets(), None, "incomplete reachability absence survived")
            finally:
                self.reach_tables = original

        def utf8_drift() -> None:
            operand = output_operand
            declaration = self.declarations[operand["declaration"]["digest"]]
            table = deepcopy(self.output_tables[operand["completionEvidence"]["table"]["digest"]])
            row = next(item for item in table["rows"] if item["rowId"] == operand["completionEvidence"]["rowId"])
            row["channels"][0]["text"] += "drift"
            row["rowId"] = digest("k-in-k/semantic-output-finite-row/v1", without(row, "rowId"))
            table["tableId"] = digest("k-in-k/semantic-output-finite-table/v1", without(table, "tableId"))
            bad = deepcopy(operand)
            bad["completionEvidence"].update({"table": key("semantic-output-finite-table", table["tableId"]), "rowId": row["rowId"]})
            bad["normalizedValue"] = {"channels": deepcopy(row["channels"])}
            self.output_tables[table["tableId"]] = table
            try:
                self.expect_rejection(lambda _: self.validate_output_value(bad, declaration, bad["completionEvidence"], bad["normalizedValue"]), None, "UTF-8 text/byte drift survived")
            finally:
                self.output_tables.pop(table["tableId"], None)

        return {
            "catalog-corpus-removal": catalog_corpus,
            "catalog-declaration-removal": catalog_declaration,
            "catalog-operand-removal": catalog_operand,
            "catalog-crash-removal": catalog_crash,
            "cross-corpus-vocabulary": cross_vocabulary,
            "stale-test-invocation": stale_invocation,
            "stale-test-id": stale_test_id,
            "replay-wrong-test": replay_wrong_test,
            "pattern-query-plan-search-drift": pattern_drift,
            "side-reversal": side_reversal,
            "normal-side-subject-swap": normal_subject_swap,
            "crash-provenance-swap": crash_swap,
            "terminal-relabel": terminal_relabel,
            "reachability-cross-side": reach_cross_side,
            "predicate-binding-sort": predicate_sort,
            "predicate-input-side": predicate_input_side,
            "output-other-subject": output_other_subject,
            "gate-mutant-as-baseline": gate_mutant,
            "gate-abort-retains-scoring": gate_abort_scoring,
            "failure-source-context": failure_source_context,
            "failure-resource-disposition": resource_disposition,
            "incomparable-missing-comparison": lambda: incomparable_missing("comparison"),
            "incomparable-missing-side": lambda: incomparable_missing("mutantSide"),
            "arbitrary-k-role": arbitrary_k_role,
            "missing-production-authority": missing_production,
            "nonconformant-authority": nonconformant,
            "receipt-as-conformance": receipt_as_conformance,
            "expected-side-kind": expected_kind,
            "expected-side-value-integrity": expected_value_integrity,
            "comparison-outcome-assertion": comparison_assertion,
            "manifest-slot-order": manifest_slot_order,
            "execution-policy-isolation-root": execution_policy_isolation_root,
            "campaign-report-test-root": campaign_test_root,
            "global-oracle-join": global_join,
            "reachability-incomplete-absence": incomplete_absence,
            "utf8-byte-text-drift": utf8_drift,
        }

    def adversaries(self) -> None:
        vectors = read_json(self.root / "vectors" / "oracle-semantics-vectors.json")
        advertised = [item["probe"] for item in vectors["adversaries"]]
        probes = self.adversary_probes()
        self.ok(len(advertised) == len(set(advertised)) and set(advertised) == set(probes), "adversary registry is not one-to-one with executable probes")
        executed = []
        for name in advertised:
            probes[name]()
            executed.append(name)
        self.ok(executed == advertised and len(executed) == len(probes), "an advertised adversary did not execute exactly once")

    def run(self) -> None:
        self.validate_manifest()
        validated_pattern_ids = set()
        for result_id, result in self.patterns.items():
            self.validate_pattern_denotation(result)
            validated_pattern_ids.add(result_id)
        self.ok(validated_pattern_ids == set(self.patterns), "active-catalog pattern-result denotation coverage is incomplete")
        self.validate_reachability_assets()
        self.validate_predicate_assets()
        for operand in self.operands.values():
            self.validate_operand(operand)
        for comparison in self.comparisons.values():
            self.validate_comparison(comparison)
        for gate in self.gates.values():
            self.validate_gate(gate)
        for record in self.conformances.values():
            self.validate_evaluator_conformance(record)
        self.validate_cache()
        self.validate_campaign()
        self.validate_vectors()
        self.adversaries()


def new_official_fixtures(root: Path) -> dict[str, str]:
    fixtures = root / "fixtures"
    result = {"execution-artifact-catalog.json": "artifact-catalog.schema.json"}
    for path in fixtures.glob("oracle-declaration-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("oracle-operand-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("oracle-comparison-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("baseline-oracle-gate-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    result["oracle-evaluator-conformance-nonconformant.json"] = "oracle-semantics.schema.json"
    result["semantic-output-finite-table.json"] = "oracle-semantics.schema.json"
    for path in fixtures.glob("reachability-plan-*.json"):
        result[path.name] = "reachability-semantics.schema.json"
    for path in fixtures.glob("reachability-query-*.json"):
        result[path.name] = "reachability-semantics.schema.json"
    for path in fixtures.glob("reachability-witness-*.json"):
        result[path.name] = "reachability-semantics.schema.json"
    result["reachability-conformance-table.json"] = "reachability-semantics.schema.json"
    for path in fixtures.glob("predicate-query-*.json"):
        result[path.name] = "predicate-semantics.schema.json"
    for name in ("predicate-plan.json", "predicate-conformance-table.json"):
        result[name] = "predicate-semantics.schema.json"
    for path in fixtures.glob("bag12-*-event-trace.json"):
        result[path.name] = "event-trace.schema.json"
    for name in ("terminal-state-mutant-distinct.json", "terminal-state-baseline-live.json", "terminal-state-mutant-live.json"):
        result[name] = "terminal-state.schema.json"
    for path in fixtures.glob("semantic-crash-*-live.json"):
        result[path.name] = "semantic-crash.schema.json"
    for path in list(fixtures.glob("bag12-*-pattern-result.json")) + list(fixtures.glob("pattern-result-write-only-*-no-match.json")):
        result[path.name] = "pattern-result.schema.json"
    for path in list(fixtures.glob("bag12-*-pattern-replay.json")) + list(fixtures.glob("replay-write-only-*-no-match.json")):
        result[path.name] = "replay-manifest.schema.json"
    return result


def verify_package(root: Path, api: dict[str, Any]) -> None:
    OracleVerifier(root, api).run()
