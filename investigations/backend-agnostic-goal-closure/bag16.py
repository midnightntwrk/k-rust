#!/usr/bin/env python3
"""Portable BAG-16 branch-collection, corpus-fold, and replay closure evidence.

This module constructs and checks deterministic canonical JSON only.  It never
invokes K, a compiler, an executor, a backend, a solver, or a native adapter.
The accepted BAG-11/12/14/15 artifacts are immutable inputs; every BAG-16
identity is published through a successor schema/version arm.
"""

from __future__ import annotations

import hashlib
import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Callable, Iterable

from bag14 import canonical, digest, key, without
from bag15 import artifact_keys, unique_artifacts
from bag16_schemas import (
    BAG16_OPERATIONS,
    BAG16_ROLE_SPECS,
    BAG16_SCHEMA_FILES,
    build_replay_registry,
    build_role_spec_registry,
    schema_for_artifact,
    select_structured_version,
)


DOMAINS = {
    "execution-test": "k-in-k/execution-test-invocation/v2",
    "execution-key": "k-in-k/execution-attempt-key/v2",
    "invocation": "k-in-k/operation-invocation/v2",
    "receipt": "k-in-k/operation-receipt/v2",
    "trace": "k-in-k/event-trace/v2",
    "scope": "k-in-k/branch-collection-scope/v1",
    "branch": "k-in-k/branch-occurrence/v1",
    "occurrence": "k-in-k/trace-occurrence/v1",
    "empty": "k-in-k/empty-search-decision/v1",
    "collection": "k-in-k/branch-trace-collection/v1",
    "pattern": "k-in-k/pattern-result/v2",
    "witness": "k-in-k/pattern-witness-occurrence/v2",
    "execution-result": "k-in-k/execution-attempt-result/v2",
    "pattern-evaluation-result": "k-in-k/pattern-evaluation-result/v1",
    "component-invocation": "k-in-k/corpus-component-invocation/v1",
    "component-result": "k-in-k/corpus-component-result/v1",
    "slot": "k-in-k/corpus-slot/v1",
    "corpus-manifest": "k-in-k/corpus-manifest/v2",
    "corpus-result": "k-in-k/corpus-result/v2",
    "corpus-derivation-result": "k-in-k/corpus-derivation-result/v1",
    "cache": "k-in-k/cache-record/v2",
    "closure": "k-in-k/portable-closure-root/v1",
}

RESULT_DOMAINS = {
    "execution-attempt-result": DOMAINS["execution-result"],
    "pattern-evaluation-result": DOMAINS["pattern-evaluation-result"],
    "corpus-derivation-result": DOMAINS["corpus-derivation-result"],
    "oracle-operand-production-result": "k-in-k/oracle-operand-production-result/v1",
}

OUTPUT_ROLES = {
    "execution-attempt": "execution-attempt-result",
    "pattern-evaluation": "pattern-evaluation-result",
    "corpus-derivation": "corpus-derivation-result",
    "oracle-operand-production": "oracle-operand-production-result",
}

ADVERSARIES = (
    "trace-v1-on-v2-edge",
    "branch-ordinal-gap",
    "branch-key-without-scope",
    "trace-occurrence-without-disposition",
    "duplicate-trace-denotation-omitted",
    "witness-digest-order",
    "pending-work-proves-coverage",
    "empty-without-produced-decision",
    "empty-marker-on-nonempty",
    "exhaustive-match-found",
    "existential-without-final-query-satisfied",
    "match-found-claimed-complete",
    "path-collection-drift",
    "execution-output-reordered",
    "execution-wrapper-terminal-drift",
    "cache-not-proven-promoted",
    "completed-receipt-without-wrapper",
    "failed-receipt-with-output",
    "completed-receipt-native-conformance",
    "failed-receipt-finite-conformance",
    "receipt-producer-identity-drift",
    "pattern-wrapper-self-receipt-cycle",
    "component-slot-drift",
    "skipped-component-with-receipt",
    "corpus-component-reorder",
    "corpus-top-level-skipped",
    "corpus-failure-taxonomy-disposition-drift",
    "registry-v1-substitution",
    "registry-missing-schema",
    "registry-surplus-operation",
    "catalog-same-key-version-alias",
    "catalog-opaque-content-hash-drift",
    "role-registry-authority-drift",
    "projected-artifact-identity-drift",
    "successor-taxonomy-placement-omitted",
    "legacy-schema-version-dispatch",
    "schema-version-legacy-dispatch",
    "closure-catalog-registry-drift",
    "finite-row-wrong-occurrence-terminal",
    "reachability-row-pair-reorder",
    "predicate-input-occurrence-drift",
    "concrete-row-content-hash-drift",
    "reachability-row-witness-unresolved",
    "predicate-row-query-unresolved",
    "finite-row-occurrence-omitted",
    "finite-row-occurrence-surplus",
    "finite-row-incomplete-collection",
    "finite-row-bounded-collection",
    "finite-row-existential-collection",
    "finite-row-input-reordered",
    "finite-row-input-missing",
    "finite-row-child-missing",
    "false-coverage-bindings-projection",
    "bindings-operand-tuples-omitted",
    "oracle-receipt-terminal-operand-drift",
    "oracle-operation-subject-drift",
    "execution-key-wrong-test",
    "execution-key-wrong-subject",
    "exhaustive-key-query-pollution",
    "existential-key-query-omitted",
    "exhaustive-slot-query-coupled",
    "existential-collection-query-neutral",
    "pattern-operation-wrong-execution-result",
    "pattern-operation-wrong-query",
    "pattern-operation-wrong-policy",
    "corpus-operation-child-reordered",
    "cache-projection-omitted",
    "cache-projection-reordered",
    "cache-projection-surplus",
    "semantic-crash-terminal-omitted",
    "semantic-crash-output-reordered",
    "semantic-crash-output-surplus",
    "existential-earlier-match",
    "existential-witness-under-exhaustion",
    "false-coverage-bindings-inline-expectation",
    "pattern-query-plan-source-drift",
    "manifest-slot-declaration-test-drift",
    "collection-trace-vocabulary-drift",
    "collection-terminal-definition-drift",
    "collection-crash-profile-drift",
    "failed-pattern-operation-wrong-query",
    "manifest-slot-query-plan-drift",
    "test-invocation-program-unresolved",
    "manifest-slot-side-condition-unresolved",
    "pattern-plan-unknown-constructor",
    "pattern-source-unresolved",
    "trace-event-unknown-constructor",
    "trace-emitting-provenance-drift",
    "trace-path-predicate-sort-drift",
    "terminal-term-sort-drift",
    "side-condition-table-duplicate-key",
    "execution-key-observation-subject-drift",
    "execution-key-observation-output-drift",
    "execution-key-subject-catalog-unresolved",
    "execution-key-lowering-profile-drift",
    "execution-key-execution-profile-drift",
    "execution-key-solver-profile-drift",
    "execution-key-isolation-policy-drift",
    "collection-query-satisfied-without-match-found",
)


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def raw_sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identify(value: dict[str, Any], field: str, domain: str) -> dict[str, Any]:
    value[field] = digest(domain, without(value, field))
    return value


def typed(role: str, identity: str) -> dict[str, str]:
    return {"role": role, "digest": identity}


def artifact_edge(edge_role: str, artifact: dict[str, str]) -> dict[str, Any]:
    return {"edgeRole": edge_role, "artifact": deepcopy(artifact)}


def receipt_edge(edge_role: str, receipt_key: dict[str, str]) -> dict[str, Any]:
    return {"edgeRole": edge_role, "receipt": deepcopy(receipt_key)}


def bag10_failure(classification: str, *, scope: str, consequence: str | None = None) -> dict[str, Any]:
    retryability = "same-input-after-resource-change" if classification != "backend-error" else "never"
    return {
        "stage": "execution", "classification": classification,
        "context": "pattern-path" if scope == "path" else "pattern-test", "scope": scope,
        "retryability": retryability, "semanticEvidence": [], "details": {},
    }


def infrastructure_failure(classification: str = "worker-lost") -> dict[str, Any]:
    return {
        "stage": "infrastructure", "classification": classification,
        "context": "pattern-test", "scope": "test",
        "retryability": "after-external-repair" if classification in {"process-launch", "io", "worker-lost"} else "never",
        "semanticEvidence": [], "details": {},
    }


def successor_failure_taxonomy(root: Path) -> dict[str, Any]:
    """Derive BAG-16's placement extension without rewriting historical v1 bytes."""
    value = read_json(root / "failure-taxonomy.json")
    context_order = {
        name: index for index, name in enumerate(
            read_json(root / "schemas" / "common.schema.json")["$defs"]["failure"]
            ["properties"]["context"]["enum"]
        )
    }
    scope_order = {name: index for index, name in enumerate(["candidate", "mutant", "path", "test", "campaign"])}
    expected = {
        "context": "pattern-test", "scope": "test",
        "consequence": {"disposition": "error"},
    }
    classifications = {"process-launch", "io", "artifact-corruption", "worker-lost", "internal"}
    for entry in value["entries"]:
        if entry["stage"] != "infrastructure" or entry["classification"] not in classifications:
            continue
        if expected not in entry["placements"]:
            entry["placements"].append(deepcopy(expected))
        entry["placements"].sort(
            key=lambda item: (context_order[item["context"]], scope_order[item["scope"]])
        )
    return identify(value, "taxonomyId", "k-in-k/failure-taxonomy/v1")


def execution_test_invocation(
    test: dict[str, Any], manifest: dict[str, Any], *, bounds: dict[str, Any] | None = None,
) -> dict[str, Any]:
    value = {
        "schemaVersion": 2, "testInvocationDigest": "0" * 64,
        "testId": test["testId"],
        "program": typed("program", test["programDigest"]),
        "parser": typed("parser", test["parserDigest"]),
        "startSymbol": test["startSymbol"],
        "options": typed("options", test["optionsDigest"]),
        "bounds": deepcopy(manifest["bounds"] if bounds is None else bounds),
    }
    return identify(value, "testInvocationDigest", DOMAINS["execution-test"])


def execution_key(
    test_invocation: dict[str, Any], manifest: dict[str, Any], subject: dict[str, Any],
    observation_key: dict[str, str], *, query: dict[str, dict[str, str]] | None = None,
    side_condition_table: dict[str, str] | None = None, search_policy: str = "exhaustive",
) -> dict[str, Any]:
    attempt: dict[str, Any] = {
        "kind": "observed-exhaustive", "observationInputs": [deepcopy(observation_key)],
    }
    if query is not None:
        attempt = {
            "kind": "query-coupled", "observationInputs": [deepcopy(observation_key)],
            "patternSource": deepcopy(query["patternSource"]),
            "patternPlan": deepcopy(query["patternPlan"]),
            "patternQuery": deepcopy(query["patternQuery"]),
            "sideConditionTable": deepcopy(side_condition_table),
            "searchPolicy": search_policy,
        }
    value = {
        "schemaVersion": 2, "keyDigest": "0" * 64,
        "operation": {
            "operationId": "portable-finite-execution", "operationVersion": 4,
            "adapterId": "bag16-vector-adapter", "adapterVersion": 1,
        },
        "subject": deepcopy(subject),
        "testInvocationDigest": test_invocation["testInvocationDigest"],
        "compatibilityProfileDigest": manifest["compatibilityProfileDigest"],
        "loweringProfileDigest": "6d07d5437a05b5bda922083438b7d4c5ee448bbbea5955ee4a49e97582eafefd",
        "executionProfileDigest": manifest["executionProfileDigest"],
        "solverProfileDigest": manifest["solverProfileDigest"],
        "isolationPolicy": {
            "schemaVersion": 1,
            "isolationPolicyDigest": digest("k-in-k/isolation-policy/v1", {
                "schemaVersion": 1, "baselineState": "immutable", "mutantState": "fresh-per-mutant",
                "sharedWritableState": False, "observerState": "fresh-per-test-path",
            }),
            "baselineState": "immutable", "mutantState": "fresh-per-mutant",
            "sharedWritableState": False, "observerState": "fresh-per-test-path",
        },
        "attemptKind": attempt,
    }
    return identify(value, "keyDigest", DOMAINS["execution-key"])


def invocation(
    operation: str, operation_version: int, parameters: dict[str, Any],
    inputs: Iterable[tuple[str, dict[str, str]]],
    children: Iterable[tuple[str, dict[str, str]]] = (),
) -> dict[str, Any]:
    value = {
        "schemaVersion": 2, "invocationDigest": "0" * 64,
        "operationKind": operation, "operationVersion": operation_version,
        "adapterContract": {"adapterId": "bag16-portable-finite", "adapterVersion": 1},
        "parameters": deepcopy(parameters),
        "inputs": [artifact_edge(edge, item) for edge, item in inputs],
        "childReceipts": [receipt_edge(edge, item) for edge, item in children],
        "outputRoles": [OUTPUT_ROLES[operation]],
    }
    return identify(value, "invocationDigest", DOMAINS["invocation"])


def complete_receipt(
    inv: dict[str, Any], result_key: dict[str, str], terminal: Any,
    failure: dict[str, Any] | None = None, *, conformance: str = "finite-vector-proven",
) -> dict[str, Any]:
    value = {
        "schemaVersion": 2, "receiptId": "0" * 64,
        "invocationDigest": inv["invocationDigest"], "invocation": deepcopy(inv),
        "producer": {"producerId": "bag16-deterministic-python", "producerVersion": 1, "executionConformance": conformance},
        "producerStatus": "complete",
        "outputs": [{"edgeRole": inv["outputRoles"][0], "artifact": deepcopy(result_key)}],
        "semanticTerminal": deepcopy(terminal), "failure": deepcopy(failure),
    }
    return identify(value, "receiptId", DOMAINS["receipt"])


def failed_receipt(inv: dict[str, Any], failure: dict[str, Any]) -> dict[str, Any]:
    value = {
        "schemaVersion": 2, "receiptId": "0" * 64,
        "invocationDigest": inv["invocationDigest"], "invocation": deepcopy(inv),
        "producer": {"producerId": "bag16-unavailable-producer", "producerVersion": 1, "executionConformance": "not-proven"},
        "producerStatus": "failed", "outputs": [], "semanticTerminal": None,
        "failure": deepcopy(failure),
    }
    return identify(value, "receiptId", DOMAINS["receipt"])


def event_trace_v2(old_trace: dict[str, Any], event_vocabulary_digest: str, *, events: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    value = {
        "schemaVersion": 2, "traceId": "0" * 64,
        "definitionDigest": old_trace["definitionDigest"],
        "eventVocabularyDigest": event_vocabulary_digest,
        "pathPredicate": deepcopy(old_trace["pathPredicate"]),
        "events": deepcopy(old_trace["events"] if events is None else events),
    }
    return identify(value, "traceId", DOMAINS["trace"])


def collection_scope(attempt_key_digest: str, invocation_digest: str) -> str:
    return digest(DOMAINS["scope"], {
        "attemptKeyDigest": attempt_key_digest, "invocationDigest": invocation_digest, "outputOrdinal": 0,
    })


def visit_record(
    scope: str, invocation_digest: str, ordinal: int, trace_key: dict[str, str], disposition: dict[str, Any],
) -> dict[str, Any]:
    branch = digest(DOMAINS["branch"], {
        "collectionScopeId": scope, "invocationDigest": invocation_digest, "visitOrdinal": ordinal,
    })
    occurrence = digest(DOMAINS["occurrence"], {
        "collectionScopeId": scope, "invocationDigest": invocation_digest,
        "branchKey": branch, "visitOrdinal": ordinal, "trace": trace_key,
        "disposition": disposition,
    })
    return {
        "branchKey": branch, "visitOrdinal": ordinal, "trace": deepcopy(trace_key),
        "traceOccurrence": occurrence, "disposition": deepcopy(disposition),
    }


def branch_collection(
    attempt_key_digest: str, invocation_digest: str, visits: list[dict[str, Any]],
    *, coupling: str = "query-independent", pending: int = 0,
    stop: dict[str, Any] | None = None, empty_decision_key: dict[str, str] | None = None,
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "collectionId": "0" * 64,
        "collectionScopeId": collection_scope(attempt_key_digest, invocation_digest),
        "attemptKeyDigest": attempt_key_digest, "invocationDigest": invocation_digest,
        "queryCoupling": {"kind": coupling}, "visited": deepcopy(visits),
        "pendingWork": {"discoveredCount": pending},
        "stopReason": deepcopy(stop or {"kind": "search-exhausted"}),
        "emptySearchDecision": deepcopy(empty_decision_key),
    }
    return identify(value, "collectionId", DOMAINS["collection"])


def empty_search_decision(attempt_key_digest: str, invocation_digest: str) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "decisionId": "0" * 64,
        "attemptKeyDigest": attempt_key_digest, "invocationDigest": invocation_digest,
        "collectionScopeId": collection_scope(attempt_key_digest, invocation_digest),
        "reason": "finite-frontier-empty",
    }
    return identify(value, "decisionId", DOMAINS["empty"])


def produced_artifacts(
    visits: list[dict[str, Any]], collection_key: dict[str, str],
    empty_key: dict[str, str] | None = None,
    assets: dict[tuple[str, str], Any] | None = None,
) -> list[dict[str, str]]:
    values: list[dict[str, str]] = []
    for visit in visits:
        disposition = visit["disposition"]
        if disposition["kind"] in {"normal", "stuck"}:
            values.append(deepcopy(disposition["terminal"]))
        elif disposition["kind"] == "semantic-crash":
            crash_key = disposition["crash"]
            if assets is None or (crash_key["role"], crash_key["digest"]) not in assets:
                raise AssertionError("semantic-crash output derivation lacks its resolved crash")
            crash = assets[(crash_key["role"], crash_key["digest"])]
            values.extend([deepcopy(crash["terminalState"]), deepcopy(crash_key)])
        values.append(deepcopy(visit["trace"]))
    result = unique_artifacts(values)
    if empty_key is not None:
        result.append(deepcopy(empty_key))
    result.append(deepcopy(collection_key))
    return result


def _match_atom(atom: dict[str, Any], event: dict[str, Any], bindings: dict[str, Any]) -> dict[str, Any] | None:
    if atom["constructor"] != event["constructor"]:
        return None
    resolved = deepcopy(bindings)
    for clause in atom["payload"]:
        if clause["position"] >= len(event["payload"]):
            return None
        term = event["payload"][clause["position"]]
        variable = clause["variable"]
        if clause["mode"] == "bind":
            if variable in resolved:
                return None
            resolved[variable] = deepcopy(term)
        elif variable not in resolved or canonical(resolved[variable]) != canonical(term):
            return None
    return resolved


def finite_denotation(
    plan: dict[str, Any], trace: dict[str, Any], table: dict[str, Any],
) -> tuple[list[dict[str, Any]], int, int]:
    """Derive BAG-11 candidates in within-trace semantic order."""
    witnesses: list[dict[str, Any]] = []
    candidates = 0
    indeterminate = 0
    table_rows = {
        (row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]): row["result"]
        for row in table["rows"]
    }

    def extend(arm: dict[str, Any], arm_ordinal: int, atom_ordinal: int, indices: list[int], bindings: dict[str, Any]) -> None:
        nonlocal candidates, indeterminate
        if atom_ordinal == len(arm["atoms"]):
            candidates += 1
            ordered = [{"name": variable["name"], "term": deepcopy(bindings[variable["name"]])} for variable in plan["variables"]]
            side = plan["sideCondition"]
            if side is not None:
                by_name = {binding["name"]: binding for binding in ordered}
                condition_bindings = [deepcopy(by_name[name]) for name in side["inputVariables"]]
                lookup = (
                    side["artifact"]["digest"], digest("k-in-k/bindings/v1", condition_bindings),
                    digest("k-in-k/path-predicate/v1", trace["pathPredicate"]),
                )
                answer = table_rows.get(lookup, "unknown")
                if answer == "false":
                    return
                if answer == "unknown":
                    indeterminate += 1
                    return
            witnesses.append({
                "armOrdinal": arm_ordinal, "eventIndices": deepcopy(indices),
                "bindings": ordered, "pathPredicate": deepcopy(trace["pathPredicate"]),
                "events": [deepcopy(trace["events"][index]) for index in indices],
            })
            return
        if not indices:
            possible = range(len(trace["events"]))
        elif arm["relations"][atom_ordinal - 1] == "next-event":
            possible = [indices[-1] + 1]
        else:
            possible = range(indices[-1] + 1, len(trace["events"]))
        for index in possible:
            if index >= len(trace["events"]):
                continue
            next_bindings = _match_atom(arm["atoms"][atom_ordinal], trace["events"][index], bindings)
            if next_bindings is not None:
                extend(arm, arm_ordinal, atom_ordinal + 1, [*indices, index], next_bindings)

    for arm_ordinal, arm in enumerate(plan["arms"]):
        extend(arm, arm_ordinal, 0, [], {})
    witnesses.sort(key=lambda item: (
        tuple(item["eventIndices"]), digest("k-in-k/bindings/v1", item["bindings"]), item["armOrdinal"],
    ))
    return witnesses, candidates, indeterminate


def occurrence_witness(
    partial: dict[str, Any], collection_key: dict[str, str], visit: dict[str, Any], query_key: dict[str, str],
) -> dict[str, Any]:
    value = {
        "witnessOccurrence": "0" * 64,
        "collection": deepcopy(collection_key), "visitOrdinal": visit["visitOrdinal"],
        "branchKey": visit["branchKey"], "trace": deepcopy(visit["trace"]),
        "traceOccurrence": visit["traceOccurrence"], "patternQuery": deepcopy(query_key),
        **deepcopy(partial),
    }
    return identify(value, "witnessOccurrence", DOMAINS["witness"])


def pattern_result(
    collection: dict[str, Any], traces: dict[str, dict[str, Any]], plan: dict[str, Any],
    query_roots: dict[str, dict[str, str]], table_key: dict[str, str], table: dict[str, Any],
    *, search_policy: str,
) -> dict[str, Any]:
    collection_key = typed("branch-trace-collection", collection["collectionId"])
    paths: list[dict[str, Any]] = []
    all_witnesses: list[dict[str, Any]] = []
    first_indeterminate: dict[str, Any] | None = None
    first_error: dict[str, Any] | None = None
    first_unknown_failure: dict[str, Any] | None = None
    for visit in collection["visited"]:
        disposition = visit["disposition"]
        trace = traces[visit["trace"]["digest"]]
        if disposition["kind"] in {"normal", "stuck", "semantic-crash", "query-satisfied"}:
            partial, candidate_count, indeterminate_count = finite_denotation(plan, trace, table)
            derived = [occurrence_witness(item, collection_key, visit, query_roots["patternQuery"]) for item in partial]
            status = "match" if derived else "unknown" if indeterminate_count else "no-match"
            if disposition["kind"] == "query-satisfied" and status != "match":
                raise AssertionError("BAG-16 query-satisfied occurrence lacks its validated witness")
            evaluation = {
                "kind": "trustworthy", "status": status,
                "denotation": {"candidateCount": candidate_count, "indeterminateCandidateCount": indeterminate_count},
                "witnesses": deepcopy(derived),
            }
            if status == "unknown" and first_indeterminate is None:
                first_indeterminate = {
                    "collection": deepcopy(collection_key), "visitOrdinal": visit["visitOrdinal"],
                    "branchKey": visit["branchKey"], "traceOccurrence": visit["traceOccurrence"],
                }
            all_witnesses.extend(derived)
        else:
            failure = disposition["failure"]
            evaluation = {"kind": "untrustworthy", "failure": deepcopy(failure)}
            if failure["classification"] == "backend-error" and first_error is None:
                first_error = deepcopy(failure)
            elif first_unknown_failure is None:
                first_unknown_failure = deepcopy(failure)
        paths.append({
            "visitOrdinal": visit["visitOrdinal"], "branchKey": visit["branchKey"],
            "trace": deepcopy(visit["trace"]), "traceOccurrence": visit["traceOccurrence"],
            "disposition": deepcopy(disposition), "evaluation": evaluation,
        })
    all_witnesses.sort(key=lambda item: (
        item["visitOrdinal"], tuple(item["eventIndices"]),
        digest("k-in-k/bindings/v1", item["bindings"]), item["armOrdinal"],
    ))
    stop = collection["stopReason"]
    global_failure = stop.get("failure")
    clean_exhaustion = stop["kind"] == "search-exhausted" and collection["pendingWork"]["discoveredCount"] == 0
    conclusive = all(path["evaluation"]["kind"] == "trustworthy" and path["evaluation"]["status"] in {"match", "no-match"} for path in paths)
    coverage = clean_exhaustion and conclusive and (bool(paths) or collection["emptySearchDecision"] is not None)
    if search_policy == "exhaustive":
        if collection["queryCoupling"] != {"kind": "query-independent"}:
            raise AssertionError("BAG-16 exhaustive evaluation consumed query-coupled execution")
        if stop["kind"] == "match-found" or any(
            path["disposition"]["kind"] == "query-satisfied" for path in paths
        ):
            raise AssertionError("BAG-16 exhaustive evaluation used existential stop evidence")
    elif search_policy == "existential-first":
        if collection["queryCoupling"] != {"kind": "pattern-query"}:
            raise AssertionError("BAG-16 existential evaluation consumed query-neutral execution")
        if stop["kind"] == "match-found":
            if (
                not paths
                or paths[-1]["disposition"]["kind"] != "query-satisfied"
                or paths[-1]["evaluation"]["status"] != "match"
                or any(
                    path["evaluation"]["kind"] != "trustworthy"
                    or path["evaluation"]["status"] != "no-match"
                    for path in paths[:-1]
                )
            ):
                raise AssertionError("BAG-16 existential match-found prefix is not first-witness exact")
            decision = {
                "kind": "match", "completeCoverage": False,
                "primaryWitness": deepcopy(all_witnesses[0]),
            }
        elif all_witnesses:
            raise AssertionError("BAG-16 existential non-match stop retained a witness")
    else:
        raise AssertionError("BAG-16 open pattern search policy")
    if search_policy == "existential-first" and stop["kind"] == "match-found":
        pass
    elif all_witnesses:
        decision = {"kind": "match", "completeCoverage": coverage, "primaryWitness": deepcopy(all_witnesses[0])}
    elif first_error is not None or (global_failure is not None and global_failure["classification"] == "backend-error"):
        decision = {"kind": "error", "completeCoverage": False, "failure": deepcopy(first_error or global_failure)}
    elif global_failure is not None or first_unknown_failure is not None:
        decision = {"kind": "unknown", "completeCoverage": False, "reason": {"kind": "execution-stop", "failure": deepcopy(global_failure or first_unknown_failure)}}
    elif first_indeterminate is not None:
        decision = {"kind": "unknown", "completeCoverage": False, "reason": {"kind": "indeterminate-denotation", "firstIndeterminate": first_indeterminate}}
    elif coverage:
        decision = {"kind": "no-match", "completeCoverage": True}
        if not paths:
            decision["emptySearchDecision"] = deepcopy(collection["emptySearchDecision"])
    else:
        raise AssertionError("BAG-16 pattern decision is not total for supplied collection")
    value = {
        "schemaVersion": 2, "resultId": "0" * 64,
        "collection": collection_key,
        "patternSource": deepcopy(query_roots["patternSource"]),
        "patternPlan": deepcopy(query_roots["patternPlan"]),
        "patternQuery": deepcopy(query_roots["patternQuery"]),
        "sideConditionTable": deepcopy(table_key), "searchPolicy": search_policy,
        "pathResults": paths, "witnesses": all_witnesses, "decision": decision,
    }
    return identify(value, "resultId", DOMAINS["pattern"])


def execution_wrapper(
    execution_key_value: dict[str, Any], inv: dict[str, Any], collection: dict[str, Any],
    outputs: list[dict[str, str]],
) -> dict[str, Any]:
    collection_key = typed("branch-trace-collection", collection["collectionId"])
    terminal = {"kind": "branch-collection", "collection": collection_key, "stopReason": deepcopy(collection["stopReason"])}
    value = {
        "schemaVersion": 2, "resultId": "0" * 64,
        "attemptKeyDigest": execution_key_value["keyDigest"],
        "invocationDigest": inv["invocationDigest"], "terminalRecord": terminal,
        "producedArtifacts": deepcopy(outputs), "branchCollection": collection_key,
    }
    return identify(value, "resultId", DOMAINS["execution-result"])


def result_wrapper(role: str, invocation_digest: str, field: str, artifact: dict[str, str]) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "resultId": "0" * 64,
        "invocationDigest": invocation_digest, field: deepcopy(artifact),
    }
    return identify(value, "resultId", RESULT_DOMAINS[role])


def oracle_operand(
    declaration: dict[str, str], subject: dict[str, Any], test_invocation_digest: str,
    manifest: dict[str, Any], completion_evidence: dict[str, Any], normalized_value: dict[str, Any],
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "operandId": "0" * 64,
        "declaration": deepcopy(declaration), "subject": deepcopy(subject),
        "testInvocationDigest": test_invocation_digest,
        "compatibilityProfileDigest": manifest["compatibilityProfileDigest"],
        "executionProfileDigest": manifest["executionProfileDigest"],
        "solverProfileDigest": manifest["solverProfileDigest"],
        "completionEvidence": deepcopy(completion_evidence),
        "normalizedValue": deepcopy(normalized_value),
    }
    return identify(value, "operandId", "k-in-k/oracle-operand/v1")


def oracle_operand_result(
    invocation_digest: str, operand_key: dict[str, str],
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "resultId": "0" * 64,
        "invocationDigest": invocation_digest,
        "outcome": {"kind": "operand", "operand": deepcopy(operand_key)},
        "failure": None,
    }
    return identify(value, "resultId", RESULT_DOMAINS["oracle-operand-production-result"])


def cache_record_v2(
    execution_key_value: dict[str, Any], wrapper: dict[str, Any], receipt_key: dict[str, str],
    collection: dict[str, Any], *, conformance: str = "finite-vector-proven",
) -> dict[str, Any]:
    stop = wrapper["terminalRecord"]["stopReason"]
    nested_incomplete = any(
        visit["disposition"]["kind"] in {"depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown"}
        for visit in collection["visited"]
    )
    if conformance == "not-proven" or stop["kind"] == "backend-failure":
        evidence, reuse = "diagnostic-only", "not-reusable"
    elif stop["kind"] in {"depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown"} or nested_incomplete:
        evidence = reuse = "exact-bounded-attempt"
    else:
        evidence = reuse = "semantic-result"
    value = {
        "schemaVersion": 2, "recordId": "0" * 64, "kind": "execution-attempt",
        "keyDigest": execution_key_value["keyDigest"], "key": deepcopy(execution_key_value),
        "terminalRecord": deepcopy(wrapper["terminalRecord"]),
        "producedArtifacts": deepcopy(wrapper["producedArtifacts"]),
        "completion": {
            "producerStatus": "complete", "evidenceClass": evidence,
            "materialClosure": "repo-complete", "executionConformance": conformance,
        },
        "reuseClass": reuse,
        "productionEvidence": {
            "mode": "operation-receipt", "receipt": deepcopy(receipt_key),
            "result": typed("execution-attempt-result", wrapper["resultId"]),
        },
    }
    return identify(value, "recordId", DOMAINS["cache"])


def corpus_slot(
    test_ordinal: int, slot_ordinal: int, test_invocation_digest: str,
    declaration: dict[str, str], roots: dict[str, dict[str, str]], table: dict[str, str], policy: str,
) -> dict[str, Any]:
    value = {
        "testOrdinal": test_ordinal, "slotOrdinal": slot_ordinal, "slotId": "0" * 64,
        "testInvocationDigest": test_invocation_digest, "declaration": deepcopy(declaration),
        "patternSource": deepcopy(roots["patternSource"]), "patternPlan": deepcopy(roots["patternPlan"]),
        "patternQuery": deepcopy(roots["patternQuery"]), "sideConditionTable": deepcopy(table),
        "searchPolicy": policy,
    }
    return identify(value, "slotId", DOMAINS["slot"])


def corpus_manifest_v2(
    old: dict[str, Any], test_invocations: list[dict[str, Any]], slots: list[list[dict[str, Any]]],
    *, scheduling: str = "full",
) -> dict[str, Any]:
    tests = [{
        "testOrdinal": ordinal, "testInvocationDigest": invocation_value["testInvocationDigest"],
        "slots": deepcopy(slots[ordinal]),
    } for ordinal, invocation_value in enumerate(test_invocations)]
    value = {
        "schemaVersion": 2, "manifestId": "0" * 64,
        "definition": typed("definition", old["definitionDigest"]),
        "compatibilityProfileDigest": old["compatibilityProfileDigest"],
        "observationManifestDigest": old["observationManifestDigest"],
        "executionMode": old["executionMode"], "solverProfileDigest": old["solverProfileDigest"],
        "executionProfileDigest": old["executionProfileDigest"], "bounds": deepcopy(old["bounds"]),
        "aggregation": {"question": "corpus-exists", "schedulingPolicy": scheduling, "failurePolicy": "preserve-unknown-error"},
        "tests": tests,
    }
    return identify(value, "manifestId", DOMAINS["corpus-manifest"])


def component_invocation(manifest: dict[str, Any], slot: dict[str, Any], attempt_key: dict[str, Any]) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "componentInvocationId": "0" * 64,
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "slotId": slot["slotId"], "testOrdinal": slot["testOrdinal"], "slotOrdinal": slot["slotOrdinal"],
        "executionAttemptKey": deepcopy(attempt_key),
        "patternEvaluationRequest": {
            "operationKind": "pattern-evaluation", "operationVersion": 1,
            **{field: deepcopy(slot[field]) for field in ("patternSource", "patternPlan", "patternQuery", "sideConditionTable", "searchPolicy")},
        },
    }
    return identify(value, "componentInvocationId", DOMAINS["component-invocation"])


def evaluated_component(
    manifest: dict[str, Any], slot: dict[str, Any], component_inv: dict[str, Any],
    attempt_key: dict[str, Any], execution_result_key: dict[str, str], execution_receipt_key: dict[str, str],
    collection_key: dict[str, str], pattern_inv: dict[str, Any], pattern_key: dict[str, str],
    pattern_wrapper_key: dict[str, str], pattern_receipt_key: dict[str, str],
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "componentResultId": "0" * 64, "kind": "evaluated",
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "slotId": slot["slotId"], "testOrdinal": slot["testOrdinal"], "slotOrdinal": slot["slotOrdinal"],
        "componentInvocationId": component_inv["componentInvocationId"],
        "executionAttemptKey": deepcopy(attempt_key), "executionResult": deepcopy(execution_result_key),
        "executionReceipt": deepcopy(execution_receipt_key), "collection": deepcopy(collection_key),
        "patternEvaluationInvocation": deepcopy(pattern_inv), "patternResult": deepcopy(pattern_key),
        "patternEvaluationResult": deepcopy(pattern_wrapper_key), "patternEvaluationReceipt": deepcopy(pattern_receipt_key),
    }
    return identify(value, "componentResultId", DOMAINS["component-result"])


def skipped_component(manifest: dict[str, Any], slot: dict[str, Any], stopped_after: int) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "componentResultId": "0" * 64, "kind": "skipped",
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "slotId": slot["slotId"], "testOrdinal": slot["testOrdinal"], "slotOrdinal": slot["slotOrdinal"],
        "schedulingReason": {"kind": "stop-after-test-match", "stoppedAfterTestOrdinal": stopped_after},
    }
    return identify(value, "componentResultId", DOMAINS["component-result"])


def execution_failure_component(
    manifest: dict[str, Any], slot: dict[str, Any], component_inv: dict[str, Any],
    attempt_key: dict[str, Any], execution_receipt_key: dict[str, str],
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "componentResultId": "0" * 64,
        "kind": "execution-failure",
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "slotId": slot["slotId"], "testOrdinal": slot["testOrdinal"],
        "slotOrdinal": slot["slotOrdinal"],
        "componentInvocationId": component_inv["componentInvocationId"],
        "executionAttemptKey": deepcopy(attempt_key),
        "executionReceipt": deepcopy(execution_receipt_key),
    }
    return identify(value, "componentResultId", DOMAINS["component-result"])


def pattern_failure_component(
    manifest: dict[str, Any], slot: dict[str, Any], component_inv: dict[str, Any],
    attempt_key: dict[str, Any], execution_result_key: dict[str, str],
    execution_receipt_key: dict[str, str], collection_key: dict[str, str],
    pattern_invocation: dict[str, Any], pattern_receipt_key: dict[str, str],
) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "componentResultId": "0" * 64,
        "kind": "pattern-failure",
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "slotId": slot["slotId"], "testOrdinal": slot["testOrdinal"],
        "slotOrdinal": slot["slotOrdinal"],
        "componentInvocationId": component_inv["componentInvocationId"],
        "executionAttemptKey": deepcopy(attempt_key),
        "executionResult": deepcopy(execution_result_key),
        "executionReceipt": deepcopy(execution_receipt_key),
        "collection": deepcopy(collection_key),
        "patternEvaluationInvocation": deepcopy(pattern_invocation),
        "patternEvaluationReceipt": deepcopy(pattern_receipt_key),
    }
    return identify(value, "componentResultId", DOMAINS["component-result"])


def _component_decision(component: dict[str, Any], assets: dict[tuple[str, str], Any]) -> tuple[dict[str, Any], bool]:
    if component["kind"] == "evaluated":
        result = assets[("pattern-result", component["patternResult"]["digest"])]
        decision = result["decision"]
        if decision["kind"] in {"match", "no-match"}:
            return {"kind": decision["kind"]}, bool(decision["completeCoverage"])
        cause = decision.get("failure") or decision.get("reason")
        return {"kind": decision["kind"], "cause": deepcopy(cause)}, False
    if component["kind"] == "skipped":
        return {"kind": "skipped", "schedulingReason": deepcopy(component["schedulingReason"])}, False
    receipt_key = component["executionReceipt"] if component["kind"] == "execution-failure" else component["patternEvaluationReceipt"]
    failure = assets[("operation-receipt", receipt_key["digest"])]["failure"]
    taxonomies = [
        value for (role, _), value in assets.items()
        if role == "failure-taxonomy"
    ]
    if len(taxonomies) != 1:
        raise AssertionError("BAG-16 component fold lacks one successor taxonomy")
    entries = [
        entry for entry in taxonomies[0]["entries"]
        if (entry["stage"], entry["classification"])
        == (failure["stage"], failure["classification"])
    ]
    placements = [
        placement for entry in entries for placement in entry["placements"]
        if (placement["context"], placement["scope"])
        == (failure["context"], failure["scope"])
    ]
    if len(placements) != 1:
        raise AssertionError("BAG-16 component failure lacks one taxonomy placement")
    disposition = placements[0]["consequence"].get("disposition")
    if disposition not in {"error", "unknown"}:
        raise AssertionError("BAG-16 failed component has no corpus failure disposition")
    kind = disposition
    return {"kind": kind, "cause": deepcopy(failure)}, False


def corpus_result_v2(
    manifest: dict[str, Any], components: list[dict[str, Any]], assets: dict[tuple[str, str], Any],
) -> dict[str, Any]:
    component_keys = [typed("corpus-component-result", item["componentResultId"]) for item in components]
    test_results: list[dict[str, Any]] = []
    complete = True
    for test in manifest["tests"]:
        selected = [(component, component_keys[index]) for index, component in enumerate(components) if component["testOrdinal"] == test["testOrdinal"]]
        if len(selected) != len(test["slots"]):
            raise AssertionError("BAG-16 corpus component/test cardinality drift")
        decisions = [(_component_decision(component, assets), component_key) for component, component_key in selected]
        complete &= all(item[0][1] for item in decisions)
        matches = [(decision, component_key) for (decision, _), component_key in decisions if decision["kind"] == "match"]
        errors = [(decision, component_key) for (decision, _), component_key in decisions if decision["kind"] == "error"]
        unknowns = [(decision, component_key) for (decision, _), component_key in decisions if decision["kind"] == "unknown"]
        skipped = [(decision, component_key) for (decision, _), component_key in decisions if decision["kind"] == "skipped"]
        if matches:
            selected_decision = {"kind": "match"}
        elif errors:
            selected_decision = {"kind": "error", "causeComponent": errors[0][1], "cause": errors[0][0]["cause"]}
        elif unknowns:
            selected_decision = {"kind": "unknown", "causeComponent": unknowns[0][1], "cause": unknowns[0][0]["cause"]}
        elif skipped:
            selected_decision = {"kind": "skipped", "schedulingReason": skipped[0][0]["schedulingReason"]}
        else:
            selected_decision = {"kind": "no-match"}
        test_results.append({"testOrdinal": test["testOrdinal"], "slots": [item[1] for item in selected], "decision": selected_decision})
    matches = [item for item in test_results if item["decision"]["kind"] == "match"]
    errors = [item for item in test_results if item["decision"]["kind"] == "error"]
    unknowns = [item for item in test_results if item["decision"]["kind"] == "unknown"]
    if matches:
        decision: dict[str, Any] = {"kind": "match", "completeCoverage": complete}
    elif errors:
        decision = {"kind": "error", "completeCoverage": False, **{field: deepcopy(errors[0]["decision"][field]) for field in ("causeComponent", "cause")}}
    elif unknowns:
        decision = {"kind": "unknown", "completeCoverage": False, **{field: deepcopy(unknowns[0]["decision"][field]) for field in ("causeComponent", "cause")}}
    else:
        if not complete:
            raise AssertionError("BAG-16 incomplete corpus cannot prove no-match")
        decision = {"kind": "no-match", "completeCoverage": True}
    value = {
        "schemaVersion": 2, "corpusResultId": "0" * 64,
        "corpusManifest": typed("corpus-manifest", manifest["manifestId"]),
        "schedulingPolicy": manifest["aggregation"]["schedulingPolicy"],
        "components": component_keys, "testResults": test_results, "decision": decision,
    }
    return identify(value, "corpusResultId", DOMAINS["corpus-result"])


def structured_entry(root: Path, role: str, identity: str, value: Any, name: str) -> dict[str, Any]:
    data = canonical(value).encode("utf-8")
    (root / "material" / name).write_bytes(data)
    return {
        "role": role, "digest": identity, "contentModel": "canonical-json", "mediaType": "application/json",
        "contentSha256": raw_sha256(data), "availability": "bundled",
        "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{name}", "resolverId": "repo-v1",
    }


def _schema_reference_closure(root: Path, initial: Iterable[str]) -> list[str]:
    documents = {path.name: read_json(path) for path in (root / "schemas").glob("*.schema.json")}
    pending = [item.partition("#")[0] for item in initial]
    reached: set[str] = set()
    while pending:
        name = pending.pop()
        if not name or name in reached:
            continue
        if name not in documents:
            raise AssertionError(f"BAG-16 registry references missing schema {name}")
        reached.add(name)

        def walk(value: Any) -> None:
            if isinstance(value, dict):
                reference = value.get("$ref")
                if isinstance(reference, str):
                    target = reference.partition("#")[0]
                    if "://" in target:
                        target = target.rsplit("/", 1)[-1]
                    if target:
                        pending.append(target)
                for child in value.values():
                    walk(child)
            elif isinstance(value, list):
                for child in value:
                    walk(child)
        walk(documents[name])
    return sorted(reached)


def _reachable(
    assets: dict[tuple[str, str], Any], result_key: dict[str, str] | None, receipt_key: dict[str, str],
) -> tuple[list[tuple[str, str]], set[tuple[str, int]], list[str]]:
    # Stack entries are reversed at each expansion so first reach follows the
    # declared receipt/input/child traversal order rather than set/hash order.
    pending = ([] if result_key is None else [result_key]) + [receipt_key]
    reached: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    operations: set[tuple[str, int]] = set()
    while pending:
        artifact = pending.pop()
        identity = (artifact["role"], artifact["digest"])
        if identity in seen:
            continue
        seen.add(identity)
        reached.append(identity)
        value = assets.get(identity)
        if value is None:
            continue
        pending.extend(reversed(artifact_keys(value)))
        # Execution-attempt keys deliberately carry this identity as a bare
        # digest so that they remain compatible with the accepted BAG-14 key
        # shape.  Replay reachability must nevertheless include the exact v2
        # invocation artifact selected by that digest.
        def add_test_invocations(node: Any) -> None:
            if isinstance(node, dict):
                test_digest = node.get("testInvocationDigest")
                if isinstance(test_digest, str):
                    pending.insert(0, typed("execution-test-invocation", test_digest))
                for child in node.values():
                    add_test_invocations(child)
            elif isinstance(node, list):
                for child in node:
                    add_test_invocations(child)

        add_test_invocations(value)
        if artifact["role"] == "operation-receipt":
            inv = value["invocation"]
            operations.add((inv["operationKind"], inv["operationVersion"]))
    schemas = {"portable-closure-root.schema.json", "replay-version-registry-v2.schema.json"}
    return reached, operations, sorted(schemas)


def _schema_names_for_assets(
    root: Path, registry: dict[str, Any], assets: dict[tuple[str, str], Any], reached: set[tuple[str, str]], seed: Iterable[str],
) -> list[str]:
    names = set(seed)
    by_role = {item["role"]: item for item in registry["specs"]}
    for identity in reached:
        value = assets.get(identity)
        if value is None or identity[0] not in by_role:
            continue
        arm = select_structured_version(by_role[identity[0]], value)
        schema_name = arm["schemaId"].partition("#")[0]
        names.add(schema_name)
    return _schema_reference_closure(root, names)


class AssetBuilder:
    def __init__(self, root: Path):
        self.root = root
        self.fixtures = root / "fixtures"
        self.assets: dict[tuple[str, str], Any] = {}
        self.names: dict[tuple[str, str], str] = {}

    def add(self, role: str, value: dict[str, Any], name: str, identity: str | None = None) -> dict[str, str]:
        if identity is None:
            fields = {
                "execution-test-invocation": "testInvocationDigest", "event-trace": "traceId",
                "branch-trace-collection": "collectionId", "empty-search-decision": "decisionId",
                "execution-attempt-result": "resultId", "pattern-result": "resultId",
                "pattern-evaluation-result": "resultId", "corpus-manifest": "manifestId",
                "corpus-component-invocation": "componentInvocationId", "corpus-component-result": "componentResultId",
                "corpus-result": "corpusResultId", "corpus-derivation-result": "resultId",
                "operation-receipt": "receiptId", "cache-record": "recordId", "oracle-operand": "operandId",
                "oracle-operand-production-result": "resultId", "replay-version-registry": "registryId",
            }
            identity = value[fields[role]]
        self.assets[(role, identity)] = deepcopy(value)
        self.names[(role, identity)] = name
        return typed(role, identity)

    def publish(self) -> list[dict[str, Any]]:
        entries = []
        for (role, identity), value in sorted(self.assets.items()):
            name = self.names[(role, identity)]
            write_json(self.fixtures / name, value)
            entries.append(structured_entry(self.root, role, identity, value, name))
        return entries


def _query_roots(declaration: dict[str, Any]) -> dict[str, dict[str, str]]:
    return {name: deepcopy(declaration["kindConfig"][name]) for name in ("patternSource", "patternPlan", "patternQuery")}


def _execution_inputs(value: dict[str, Any]) -> list[tuple[str, dict[str, str]]]:
    return [("key-artifact", item) for item in unique_artifacts(artifact_keys(value))]


def finalize_refresh(root: Path) -> None:
    """Publish the deterministic BAG-16 derivative graph and evidence vector."""
    fixtures = root / "fixtures"
    old_catalog = read_json(fixtures / "bag15-replay-artifact-catalog.json")
    old_entries = {
        (item["role"], item["digest"]): deepcopy(item)
        for item in old_catalog["entries"] if item["role"] != "failure-taxonomy"
    }
    # BAG-15's replay-focused catalog intentionally contains only its reachable
    # subset.  BAG-16 replays every accepted BAG-12 finite authority and inline
    # expectation through the successor resolver, so import the complete
    # frozen base catalog before adding derivative BAG-16 material.
    base_catalog = read_json(fixtures / "artifact-catalog.json")
    for item in base_catalog["entries"]:
        if item["role"] == "failure-taxonomy":
            continue
        old_entries[(item["role"], item["digest"])] = deepcopy(item)
    old_assets: dict[tuple[str, str], Any] = {}
    for identity, entry in old_entries.items():
        if entry["contentModel"] == "canonical-json" and entry["availability"] == "bundled":
            path = root.parents[1] / entry["logicalPath"].removeprefix("repo://")
            old_assets[identity] = json.loads(path.read_text(encoding="utf-8"))

    builder = AssetBuilder(root)
    taxonomy = successor_failure_taxonomy(root)
    builder.add(
        "failure-taxonomy", taxonomy, "bag16-failure-taxonomy.json",
        taxonomy["taxonomyId"],
    )
    old_corpus = read_json(fixtures / "corpus-manifest.json")
    old_test = old_corpus["tests"][0]
    test_inv = execution_test_invocation(old_test, old_corpus)
    test_inv_key = builder.add("execution-test-invocation", test_inv, "bag16-execution-test-invocation.json")
    observation = read_json(fixtures / "observation-manifest.json")
    observation_key = typed("observation-manifest", observation["manifestId"])
    definition_key = typed("definition", old_corpus["definitionDigest"])
    subject = {"kind": "baseline", "definition": definition_key}

    declaration = deepcopy(read_json(
        fixtures / "oracle-declaration-execution-pattern-pattern-outcome-distinguish.json"
    ))
    declaration["testInvocationDigest"] = test_inv["testInvocationDigest"]
    identify(declaration, "declarationId", "k-in-k/oracle-declaration/v1")
    declaration_key = builder.add(
        "oracle-declaration", declaration,
        "bag16-oracle-declaration-execution-pattern.json",
        declaration["declarationId"],
    )
    roots = _query_roots(declaration)
    plan = old_assets.get(("pattern-plan", roots["patternPlan"]["digest"])) or read_json(root / "material" / "pattern-plan-write-eventually-load.json")
    table = read_json(fixtures / "side-condition-conformance-table.json")
    table_key = typed("side-condition-conformance-table", table["tableDigest"])
    old_trace = read_json(fixtures / "bag12-baseline-event-trace.json")
    trace = event_trace_v2(old_trace, observation["eventVocabularyDigest"])
    trace_key = builder.add("event-trace", trace, "bag16-event-trace-shared.json")

    exhaustive_key = execution_key(test_inv, old_corpus, subject, observation_key)
    execution_inv = invocation("execution-attempt", 2, {
        "executionKey": exhaustive_key, "keyDigest": exhaustive_key["keyDigest"],
    }, _execution_inputs(exhaustive_key))
    scope = collection_scope(exhaustive_key["keyDigest"], execution_inv["invocationDigest"])
    terminal_key = deepcopy(old_trace["executionTerminal"]["artifact"])
    visits = [
        visit_record(scope, execution_inv["invocationDigest"], ordinal, trace_key, {"kind": "normal", "terminal": terminal_key})
        for ordinal in range(2)
    ]
    collection = branch_collection(exhaustive_key["keyDigest"], execution_inv["invocationDigest"], visits)
    collection_key = builder.add("branch-trace-collection", collection, "bag16-collection-two-branch.json")
    outputs = produced_artifacts(visits, collection_key)
    execution_result = execution_wrapper(exhaustive_key, execution_inv, collection, outputs)
    execution_result_key = builder.add("execution-attempt-result", execution_result, "bag16-execution-result-two-branch.json")
    execution_receipt = complete_receipt(execution_inv, execution_result_key, execution_result["terminalRecord"])
    execution_receipt_key = builder.add("operation-receipt", execution_receipt, "bag16-receipt-execution-two-branch.json")
    cache = cache_record_v2(exhaustive_key, execution_result, execution_receipt_key, collection)
    cache_key = builder.add("cache-record", cache, "bag16-cache-two-branch.json")

    pattern = pattern_result(collection, {trace["traceId"]: trace}, plan, roots, table_key, table, search_policy="exhaustive")
    pattern_key = builder.add("pattern-result", pattern, "bag16-pattern-result-two-branch.json")
    pattern_inv = invocation("pattern-evaluation", 1, {
        "collection": collection_key, "executionResult": execution_result_key,
        **{name: deepcopy(roots[name]) for name in roots}, "sideConditionTable": table_key,
        "searchPolicy": "exhaustive",
    }, [
        ("execution-result", execution_result_key), ("branch-collection", collection_key),
        ("pattern-source", roots["patternSource"]), ("pattern-plan", roots["patternPlan"]),
        ("pattern-query", roots["patternQuery"]), ("side-condition-conformance-table", table_key),
    ], [("execution-production", execution_receipt_key)])
    pattern_wrapper = result_wrapper("pattern-evaluation-result", pattern_inv["invocationDigest"], "patternResult", pattern_key)
    pattern_wrapper_key = builder.add("pattern-evaluation-result", pattern_wrapper, "bag16-pattern-evaluation-result-two-branch.json")
    pattern_receipt = complete_receipt(pattern_inv, pattern_wrapper_key, pattern["decision"])
    pattern_receipt_key = builder.add("operation-receipt", pattern_receipt, "bag16-receipt-pattern-two-branch.json")

    slots = [[
        corpus_slot(0, ordinal, test_inv["testInvocationDigest"], declaration_key, roots, table_key, "exhaustive")
        for ordinal in range(2)
    ]]
    corpus = corpus_manifest_v2(old_corpus, [test_inv], slots)
    corpus_key = builder.add("corpus-manifest", corpus, "bag16-corpus-manifest-full.json")
    components = []
    for slot in slots[0]:
        component_inv = component_invocation(corpus, slot, exhaustive_key)
        builder.add("corpus-component-invocation", component_inv, f"bag16-component-invocation-{slot['slotOrdinal']}.json")
        component = evaluated_component(
            corpus, slot, component_inv, exhaustive_key, execution_result_key, execution_receipt_key,
            collection_key, pattern_inv, pattern_key, pattern_wrapper_key, pattern_receipt_key,
        )
        builder.add("corpus-component-result", component, f"bag16-component-result-{slot['slotOrdinal']}.json")
        components.append(component)
    fold_assets = {**old_assets, **builder.assets}
    corpus_result = corpus_result_v2(corpus, components, fold_assets)
    corpus_result_key = builder.add("corpus-result", corpus_result, "bag16-corpus-result-full.json")
    component_keys = [typed("corpus-component-result", item["componentResultId"]) for item in components]
    corpus_children = [
        edge
        for _component in components
        for edge in (
            ("execution-production", execution_receipt_key),
            ("pattern-evaluation-production", pattern_receipt_key),
        )
    ]
    corpus_inv = invocation("corpus-derivation", 1, {
        "corpusManifest": corpus_key, "schedulingPolicy": "full", "components": component_keys,
    }, [("corpus-manifest", corpus_key), *[("component-result", item) for item in component_keys]], corpus_children)
    corpus_wrapper = result_wrapper("corpus-derivation-result", corpus_inv["invocationDigest"], "corpusResult", corpus_result_key)
    corpus_wrapper_key = builder.add("corpus-derivation-result", corpus_wrapper, "bag16-corpus-derivation-result-full.json")
    corpus_receipt = complete_receipt(corpus_inv, corpus_wrapper_key, corpus_result["decision"])
    corpus_receipt_key = builder.add("operation-receipt", corpus_receipt, "bag16-receipt-corpus-full.json")

    # Empty exhaustive evidence retains an execution-produced empty-space authority.
    empty_test_inv = execution_test_invocation(old_corpus["tests"][1], old_corpus)
    builder.add("execution-test-invocation", empty_test_inv, "bag16-execution-test-invocation-empty.json")
    empty_declaration = deepcopy(declaration)
    empty_declaration["testInvocationDigest"] = empty_test_inv["testInvocationDigest"]
    identify(empty_declaration, "declarationId", "k-in-k/oracle-declaration/v1")
    empty_declaration_key = builder.add(
        "oracle-declaration", empty_declaration,
        "bag16-oracle-declaration-execution-pattern-empty-test.json",
        empty_declaration["declarationId"],
    )
    empty_execution_key = execution_key(empty_test_inv, old_corpus, subject, observation_key)
    empty_inv = invocation(
        "execution-attempt", 2,
        {"executionKey": empty_execution_key, "keyDigest": empty_execution_key["keyDigest"]},
        _execution_inputs(empty_execution_key),
    )
    empty_value = empty_search_decision(empty_execution_key["keyDigest"], empty_inv["invocationDigest"])
    empty_key = builder.add("empty-search-decision", empty_value, "bag16-empty-search-decision.json")
    empty_collection = branch_collection(empty_execution_key["keyDigest"], empty_inv["invocationDigest"], [], empty_decision_key=empty_key)
    empty_collection_key = builder.add("branch-trace-collection", empty_collection, "bag16-collection-empty.json")
    empty_outputs = produced_artifacts([], empty_collection_key, empty_key)
    empty_result = execution_wrapper(empty_execution_key, empty_inv, empty_collection, empty_outputs)
    empty_result_key = builder.add("execution-attempt-result", empty_result, "bag16-execution-result-empty.json")
    empty_receipt = complete_receipt(empty_inv, empty_result_key, empty_result["terminalRecord"])
    empty_receipt_key = builder.add("operation-receipt", empty_receipt, "bag16-receipt-execution-empty.json")
    empty_cache = cache_record_v2(empty_execution_key, empty_result, empty_receipt_key, empty_collection)
    empty_cache_key = builder.add("cache-record", empty_cache, "bag16-cache-empty.json")
    empty_pattern = pattern_result(empty_collection, {}, plan, roots, table_key, table, search_policy="exhaustive")
    empty_pattern_key = builder.add("pattern-result", empty_pattern, "bag16-pattern-result-empty.json")
    empty_pattern_inv = invocation("pattern-evaluation", 1, {
        "collection": empty_collection_key, "executionResult": empty_result_key,
        **{name: deepcopy(roots[name]) for name in roots},
        "sideConditionTable": table_key, "searchPolicy": "exhaustive",
    }, [
        ("execution-result", empty_result_key),
        ("branch-collection", empty_collection_key),
        ("pattern-source", roots["patternSource"]),
        ("pattern-plan", roots["patternPlan"]),
        ("pattern-query", roots["patternQuery"]),
        ("side-condition-conformance-table", table_key),
    ], [("execution-production", empty_receipt_key)])
    empty_pattern_wrapper = result_wrapper(
        "pattern-evaluation-result", empty_pattern_inv["invocationDigest"],
        "patternResult", empty_pattern_key,
    )
    empty_pattern_wrapper_key = builder.add(
        "pattern-evaluation-result", empty_pattern_wrapper,
        "bag16-pattern-evaluation-result-empty.json",
    )
    empty_pattern_receipt = complete_receipt(
        empty_pattern_inv, empty_pattern_wrapper_key, empty_pattern["decision"],
    )
    empty_pattern_receipt_key = builder.add(
        "operation-receipt", empty_pattern_receipt,
        "bag16-receipt-pattern-empty.json",
    )

    # Two distinct execution children establish cache projection traversal
    # order independently of set/hash iteration.
    multi_slots = [
        [corpus_slot(
            0, 0, test_inv["testInvocationDigest"], declaration_key,
            roots, table_key, "exhaustive",
        )],
        [corpus_slot(
            1, 0, empty_test_inv["testInvocationDigest"], empty_declaration_key,
            roots, table_key, "exhaustive",
        )],
    ]
    multi_manifest = corpus_manifest_v2(
        old_corpus, [test_inv, empty_test_inv], multi_slots,
    )
    multi_manifest_key = builder.add(
        "corpus-manifest", multi_manifest, "bag16-corpus-manifest-two-execution.json",
    )
    multi_component_invocations = [
        component_invocation(multi_manifest, multi_slots[0][0], exhaustive_key),
        component_invocation(multi_manifest, multi_slots[1][0], empty_execution_key),
    ]
    for ordinal, component_invocation_value in enumerate(multi_component_invocations):
        builder.add(
            "corpus-component-invocation", component_invocation_value,
            f"bag16-component-invocation-two-execution-{ordinal}.json",
        )
    multi_components = [
        evaluated_component(
            multi_manifest, multi_slots[0][0], multi_component_invocations[0],
            exhaustive_key, execution_result_key, execution_receipt_key,
            collection_key, pattern_inv, pattern_key, pattern_wrapper_key,
            pattern_receipt_key,
        ),
        evaluated_component(
            multi_manifest, multi_slots[1][0], multi_component_invocations[1],
            empty_execution_key, empty_result_key, empty_receipt_key,
            empty_collection_key, empty_pattern_inv, empty_pattern_key,
            empty_pattern_wrapper_key, empty_pattern_receipt_key,
        ),
    ]
    for ordinal, component in enumerate(multi_components):
        builder.add(
            "corpus-component-result", component,
            f"bag16-component-result-two-execution-{ordinal}.json",
        )
    multi_corpus_result = corpus_result_v2(
        multi_manifest, multi_components, {**old_assets, **builder.assets},
    )
    multi_corpus_result_key = builder.add(
        "corpus-result", multi_corpus_result,
        "bag16-corpus-result-two-execution.json",
    )
    multi_component_keys = [
        typed("corpus-component-result", component["componentResultId"])
        for component in multi_components
    ]
    multi_corpus_inv = invocation("corpus-derivation", 1, {
        "corpusManifest": multi_manifest_key, "schedulingPolicy": "full",
        "components": multi_component_keys,
    }, [
        ("corpus-manifest", multi_manifest_key),
        *[("component-result", item) for item in multi_component_keys],
    ], [
        ("execution-production", execution_receipt_key),
        ("pattern-evaluation-production", pattern_receipt_key),
        ("execution-production", empty_receipt_key),
        ("pattern-evaluation-production", empty_pattern_receipt_key),
    ])
    multi_corpus_wrapper = result_wrapper(
        "corpus-derivation-result", multi_corpus_inv["invocationDigest"],
        "corpusResult", multi_corpus_result_key,
    )
    multi_corpus_wrapper_key = builder.add(
        "corpus-derivation-result", multi_corpus_wrapper,
        "bag16-corpus-derivation-result-two-execution.json",
    )
    multi_corpus_receipt = complete_receipt(
        multi_corpus_inv, multi_corpus_wrapper_key, multi_corpus_result["decision"],
    )
    multi_corpus_receipt_key = builder.add(
        "operation-receipt", multi_corpus_receipt,
        "bag16-receipt-corpus-two-execution.json",
    )

    # Query-coupled existential-first produces a terminal-free final occurrence.
    existential_key = execution_key(test_inv, old_corpus, subject, observation_key, query=roots, side_condition_table=table_key, search_policy="existential-first")
    existential_inv = invocation("execution-attempt", 2, {"executionKey": existential_key, "keyDigest": existential_key["keyDigest"]}, _execution_inputs(existential_key))
    existential_scope = collection_scope(existential_key["keyDigest"], existential_inv["invocationDigest"])
    existential_visits = [visit_record(existential_scope, existential_inv["invocationDigest"], 0, trace_key, {"kind": "query-satisfied"})]
    existential_collection = branch_collection(
        existential_key["keyDigest"], existential_inv["invocationDigest"], existential_visits,
        coupling="pattern-query", pending=1, stop={"kind": "match-found"},
    )
    existential_collection_key = builder.add("branch-trace-collection", existential_collection, "bag16-collection-existential-match.json")
    existential_outputs = produced_artifacts(existential_visits, existential_collection_key)
    existential_result = execution_wrapper(existential_key, existential_inv, existential_collection, existential_outputs)
    existential_result_key = builder.add("execution-attempt-result", existential_result, "bag16-execution-result-existential.json")
    existential_receipt = complete_receipt(existential_inv, existential_result_key, existential_result["terminalRecord"])
    existential_receipt_key = builder.add("operation-receipt", existential_receipt, "bag16-receipt-execution-existential.json")
    existential_cache = cache_record_v2(
        existential_key, existential_result, existential_receipt_key, existential_collection,
    )
    existential_cache_key = builder.add("cache-record", existential_cache, "bag16-cache-existential.json")
    existential_pattern = pattern_result(existential_collection, {trace["traceId"]: trace}, plan, roots, table_key, table, search_policy="existential-first")
    existential_pattern_key = builder.add("pattern-result", existential_pattern, "bag16-pattern-result-existential.json")

    # Bounded and nonconformant cache examples exercise precedence before native claims.
    bounded_failure = bag10_failure("time-limit", scope="test")
    bounded_bounds = {**deepcopy(old_corpus["bounds"]), "timeMs": 1}
    bounded_test_inv = execution_test_invocation(old_test, old_corpus, bounds=bounded_bounds)
    builder.add("execution-test-invocation", bounded_test_inv, "bag16-execution-test-invocation-bounded.json")
    bounded_execution_key = execution_key(bounded_test_inv, old_corpus, subject, observation_key)
    bounded_inv = invocation(
        "execution-attempt", 2,
        {"executionKey": bounded_execution_key, "keyDigest": bounded_execution_key["keyDigest"]},
        _execution_inputs(bounded_execution_key),
    )
    bounded_scope = collection_scope(bounded_execution_key["keyDigest"], bounded_inv["invocationDigest"])
    bounded_visits = [
        visit_record(
            bounded_scope, bounded_inv["invocationDigest"], 0, trace_key,
            {"kind": "normal", "terminal": terminal_key},
        )
    ]
    bounded_collection = branch_collection(
        bounded_execution_key["keyDigest"], bounded_inv["invocationDigest"], bounded_visits,
        stop={"kind": "time-limit", "failure": bounded_failure},
    )
    bounded_collection_key = builder.add("branch-trace-collection", bounded_collection, "bag16-collection-bounded.json")
    bounded_outputs = produced_artifacts(bounded_visits, bounded_collection_key)
    bounded_result = execution_wrapper(bounded_execution_key, bounded_inv, bounded_collection, bounded_outputs)
    bounded_result_key = builder.add("execution-attempt-result", bounded_result, "bag16-execution-result-bounded.json")
    bounded_receipt = complete_receipt(bounded_inv, bounded_result_key, bounded_result["terminalRecord"], bounded_failure)
    bounded_receipt_key = builder.add("operation-receipt", bounded_receipt, "bag16-receipt-execution-bounded.json")
    bounded_cache = cache_record_v2(
        bounded_execution_key, bounded_result, bounded_receipt_key, bounded_collection,
    )
    bounded_cache_key = builder.add("cache-record", bounded_cache, "bag16-cache-bounded.json")
    diagnostic_receipt = complete_receipt(
        bounded_inv, bounded_result_key, bounded_result["terminalRecord"], bounded_failure,
        conformance="not-proven",
    )
    diagnostic_receipt_key = builder.add(
        "operation-receipt", diagnostic_receipt,
        "bag16-receipt-execution-not-proven.json",
    )
    diagnostic_cache = cache_record_v2(
        bounded_execution_key, bounded_result, diagnostic_receipt_key, bounded_collection,
        conformance="not-proven",
    )
    diagnostic_cache_key = builder.add("cache-record", diagnostic_cache, "bag16-cache-not-proven.json")

    # A second producer receipt over the same clean result demonstrates that
    # nonconformance dominates even a clean exhaustive terminal.
    clean_diagnostic_receipt = complete_receipt(
        execution_inv, execution_result_key, execution_result["terminalRecord"],
        conformance="not-proven",
    )
    clean_diagnostic_receipt_key = builder.add(
        "operation-receipt", clean_diagnostic_receipt,
        "bag16-receipt-execution-clean-not-proven.json",
    )
    clean_diagnostic_cache = cache_record_v2(
        exhaustive_key, execution_result, clean_diagnostic_receipt_key, collection,
        conformance="not-proven",
    )
    clean_diagnostic_cache_key = builder.add(
        "cache-record", clean_diagnostic_cache, "bag16-cache-clean-not-proven.json",
    )

    scenario_ordinal = 0

    def execution_scenario(
        label: str, trace_dispositions: list[tuple[dict[str, str], dict[str, Any]]],
        *, query_roots: dict[str, dict[str, str]] | None = None,
        policy: str = "exhaustive", pending: int = 0,
        stop: dict[str, Any] | None = None, failure: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        nonlocal scenario_ordinal
        scenario_ordinal += 1
        bounds = {
            **deepcopy(old_corpus["bounds"]),
            "depth": old_corpus["bounds"]["depth"] + scenario_ordinal,
        }
        scenario_test = execution_test_invocation(old_test, old_corpus, bounds=bounds)
        test_key_value = builder.add(
            "execution-test-invocation", scenario_test,
            f"bag16-execution-test-invocation-{label}.json",
        )
        attempt = execution_key(
            scenario_test, old_corpus, subject, observation_key,
            query=query_roots,
            side_condition_table=table_key if query_roots is not None else None,
            search_policy=policy,
        )
        operation = invocation(
            "execution-attempt", 2,
            {"executionKey": attempt, "keyDigest": attempt["keyDigest"]},
            _execution_inputs(attempt),
        )
        scope_value = collection_scope(attempt["keyDigest"], operation["invocationDigest"])
        scenario_visits = [
            visit_record(
                scope_value, operation["invocationDigest"], ordinal,
                trace_key_value, disposition,
            )
            for ordinal, (trace_key_value, disposition) in enumerate(trace_dispositions)
        ]
        scenario_collection = branch_collection(
            attempt["keyDigest"], operation["invocationDigest"], scenario_visits,
            coupling="pattern-query" if query_roots is not None else "query-independent",
            pending=pending, stop=stop,
        )
        scenario_collection_key = builder.add(
            "branch-trace-collection", scenario_collection,
            f"bag16-collection-{label}.json",
        )
        scenario_outputs = produced_artifacts(
            scenario_visits, scenario_collection_key,
            assets={**old_assets, **builder.assets},
        )
        scenario_result = execution_wrapper(
            attempt, operation, scenario_collection, scenario_outputs,
        )
        scenario_result_key = builder.add(
            "execution-attempt-result", scenario_result,
            f"bag16-execution-result-{label}.json",
        )
        scenario_receipt = complete_receipt(
            operation, scenario_result_key, scenario_result["terminalRecord"], failure,
        )
        scenario_receipt_key = builder.add(
            "operation-receipt", scenario_receipt,
            f"bag16-receipt-execution-{label}.json",
        )
        scenario_cache = cache_record_v2(
            attempt, scenario_result, scenario_receipt_key, scenario_collection,
        )
        scenario_cache_key = builder.add(
            "cache-record", scenario_cache, f"bag16-cache-{label}.json",
        )
        return {
            "test": scenario_test, "testKey": test_key_value, "key": attempt,
            "invocation": operation, "collection": scenario_collection,
            "collectionKey": scenario_collection_key, "result": scenario_result,
            "resultKey": scenario_result_key, "receipt": scenario_receipt,
            "receiptKey": scenario_receipt_key, "cache": scenario_cache,
            "cacheKey": scenario_cache_key,
        }

    crash_key = next(
        typed("semantic-crash", identity)
        for (role, identity), value in old_assets.items()
        if role == "semantic-crash" and value["terminalState"] == terminal_key
    )
    semantic_crash_execution = execution_scenario(
        "semantic-crash-output-order",
        [(trace_key, {"kind": "semantic-crash", "crash": crash_key})],
    )

    no_match_trace = event_trace_v2(
        old_trace, observation["eventVocabularyDigest"], events=[],
    )
    no_match_trace_key = builder.add(
        "event-trace", no_match_trace, "bag16-event-trace-no-match.json",
    )
    exhaustive_no_match = execution_scenario(
        "exhaustive-no-match",
        [(no_match_trace_key, {"kind": "normal", "terminal": terminal_key})],
    )
    exhaustive_no_match_pattern = pattern_result(
        exhaustive_no_match["collection"], {no_match_trace["traceId"]: no_match_trace},
        plan, roots, table_key, table, search_policy="exhaustive",
    )
    exhaustive_no_match_pattern_key = builder.add(
        "pattern-result", exhaustive_no_match_pattern,
        "bag16-pattern-result-exhaustive-no-match.json",
    )

    existential_no_match = execution_scenario(
        "existential-exhausted-no-match",
        [(no_match_trace_key, {"kind": "normal", "terminal": terminal_key})],
        query_roots=roots, policy="existential-first",
    )
    existential_no_match_pattern = pattern_result(
        existential_no_match["collection"], {no_match_trace["traceId"]: no_match_trace},
        plan, roots, table_key, table, search_policy="existential-first",
    )
    existential_no_match_pattern_key = builder.add(
        "pattern-result", existential_no_match_pattern,
        "bag16-pattern-result-existential-exhausted-no-match.json",
    )

    existential_zero_pending = execution_scenario(
        "existential-match-pending-zero",
        [(trace_key, {"kind": "query-satisfied"})], query_roots=roots,
        policy="existential-first", pending=0, stop={"kind": "match-found"},
    )
    existential_zero_pattern = pattern_result(
        existential_zero_pending["collection"], {trace["traceId"]: trace},
        plan, roots, table_key, table, search_policy="existential-first",
    )
    existential_zero_pattern_key = builder.add(
        "pattern-result", existential_zero_pattern,
        "bag16-pattern-result-existential-match-pending-zero.json",
    )

    side_plan = read_json(root / "material" / "pattern-plan-write-then-load-side-condition.json")
    side_query = read_json(root / "material" / "pattern-query-write-then-load-side-condition.json")
    side_roots = {
        "patternSource": deepcopy(side_query["patternSource"]),
        "patternPlan": deepcopy(side_query["patternPlan"]),
        "patternQuery": typed("pattern-query", side_query["queryId"]),
    }
    indeterminate_events = deepcopy(trace["events"])
    for event in indeterminate_events:
        event["payload"][0]["node"]["text"] = "99"
    indeterminate_trace = event_trace_v2(
        old_trace, observation["eventVocabularyDigest"], events=indeterminate_events,
    )
    indeterminate_trace_key = builder.add(
        "event-trace", indeterminate_trace, "bag16-event-trace-indeterminate.json",
    )
    indeterminate_execution = execution_scenario(
        "side-condition-indeterminate",
        [(indeterminate_trace_key, {"kind": "normal", "terminal": terminal_key})],
    )
    indeterminate_pattern = pattern_result(
        indeterminate_execution["collection"],
        {indeterminate_trace["traceId"]: indeterminate_trace}, side_plan,
        side_roots, table_key, table, search_policy="exhaustive",
    )
    indeterminate_pattern_key = builder.add(
        "pattern-result", indeterminate_pattern,
        "bag16-pattern-result-side-condition-indeterminate.json",
    )
    mixed_execution = execution_scenario(
        "mixed-match-indeterminate",
        [
            (trace_key, {"kind": "normal", "terminal": terminal_key}),
            (indeterminate_trace_key, {"kind": "normal", "terminal": terminal_key}),
        ],
    )
    mixed_pattern = pattern_result(
        mixed_execution["collection"], {
            trace["traceId"]: trace,
            indeterminate_trace["traceId"]: indeterminate_trace,
        }, side_plan, side_roots, table_key, table, search_policy="exhaustive",
    )
    mixed_pattern_key = builder.add(
        "pattern-result", mixed_pattern,
        "bag16-pattern-result-mixed-match-indeterminate.json",
    )

    path_limit = bag10_failure("time-limit", scope="path")
    backend_failure = bag10_failure("backend-error", scope="test")
    backend_after_bounded = execution_scenario(
        "backend-after-bounded-path",
        [(trace_key, {"kind": "time-limit", "failure": path_limit})],
        stop={"kind": "backend-failure", "failure": backend_failure},
        failure=backend_failure,
    )
    error_pattern = pattern_result(
        backend_after_bounded["collection"], {trace["traceId"]: trace},
        plan, roots, table_key, table, search_policy="exhaustive",
    )
    error_pattern_key = builder.add(
        "pattern-result", error_pattern, "bag16-pattern-result-backend-error.json",
    )
    error_pattern_invocation = invocation(
        "pattern-evaluation", 1,
        {
            "collection": backend_after_bounded["collectionKey"],
            "executionResult": backend_after_bounded["resultKey"],
            **{name: deepcopy(roots[name]) for name in roots},
            "sideConditionTable": table_key, "searchPolicy": "exhaustive",
        },
        [
            ("execution-result", backend_after_bounded["resultKey"]),
            ("branch-collection", backend_after_bounded["collectionKey"]),
            ("pattern-source", roots["patternSource"]),
            ("pattern-plan", roots["patternPlan"]),
            ("pattern-query", roots["patternQuery"]),
            ("side-condition-conformance-table", table_key),
        ],
        [("execution-production", backend_after_bounded["receiptKey"])],
    )
    error_pattern_wrapper = result_wrapper(
        "pattern-evaluation-result", error_pattern_invocation["invocationDigest"],
        "patternResult", error_pattern_key,
    )
    error_pattern_wrapper_key = builder.add(
        "pattern-evaluation-result", error_pattern_wrapper,
        "bag16-pattern-evaluation-result-backend-error.json",
    )
    error_pattern_receipt = complete_receipt(
        error_pattern_invocation, error_pattern_wrapper_key,
        error_pattern["decision"], failure=None,
    )
    error_pattern_receipt_key = builder.add(
        "operation-receipt", error_pattern_receipt,
        "bag16-receipt-pattern-backend-error.json",
    )

    # Full producer-failure fold.  Both components are explicit and the first
    # manifest-order unknown cause wins deterministically.
    failure_slots = [[
        corpus_slot(
            0, ordinal, test_inv["testInvocationDigest"], declaration_key,
            roots, table_key, "exhaustive",
        )
        for ordinal in range(2)
    ]]
    failure_corpus = corpus_manifest_v2(old_corpus, [test_inv], failure_slots)
    failure_corpus_key = builder.add(
        "corpus-manifest", failure_corpus, "bag16-corpus-manifest-failures.json",
    )
    failed_execution_receipt = failed_receipt(execution_inv, infrastructure_failure("worker-lost"))
    failed_execution_receipt_key = builder.add(
        "operation-receipt", failed_execution_receipt,
        "bag16-receipt-execution-producer-failed.json",
    )
    failure_component_invocation_0 = component_invocation(
        failure_corpus, failure_slots[0][0], exhaustive_key,
    )
    builder.add(
        "corpus-component-invocation", failure_component_invocation_0,
        "bag16-component-invocation-execution-failure.json",
    )
    failure_component_0 = execution_failure_component(
        failure_corpus, failure_slots[0][0], failure_component_invocation_0,
        exhaustive_key, failed_execution_receipt_key,
    )
    failure_component_0_key = builder.add(
        "corpus-component-result", failure_component_0,
        "bag16-component-result-execution-failure.json",
    )
    failed_pattern_receipt = failed_receipt(pattern_inv, infrastructure_failure("io"))
    failed_pattern_receipt_key = builder.add(
        "operation-receipt", failed_pattern_receipt,
        "bag16-receipt-pattern-producer-failed.json",
    )
    failure_component_invocation_1 = component_invocation(
        failure_corpus, failure_slots[0][1], exhaustive_key,
    )
    builder.add(
        "corpus-component-invocation", failure_component_invocation_1,
        "bag16-component-invocation-pattern-failure.json",
    )
    failure_component_1 = pattern_failure_component(
        failure_corpus, failure_slots[0][1], failure_component_invocation_1,
        exhaustive_key, execution_result_key, execution_receipt_key,
        collection_key, pattern_inv, failed_pattern_receipt_key,
    )
    failure_component_1_key = builder.add(
        "corpus-component-result", failure_component_1,
        "bag16-component-result-pattern-failure.json",
    )
    failure_components = [failure_component_0, failure_component_1]
    failure_fold_assets = {**old_assets, **builder.assets}
    failure_corpus_result = corpus_result_v2(
        failure_corpus, failure_components, failure_fold_assets,
    )
    failure_corpus_result_key = builder.add(
        "corpus-result", failure_corpus_result, "bag16-corpus-result-failures.json",
    )
    failure_component_keys = [failure_component_0_key, failure_component_1_key]
    failure_corpus_invocation = invocation(
        "corpus-derivation", 1,
        {
            "corpusManifest": failure_corpus_key, "schedulingPolicy": "full",
            "components": failure_component_keys,
        },
        [
            ("corpus-manifest", failure_corpus_key),
            *[("component-result", item) for item in failure_component_keys],
        ],
        [
            ("execution-production", failed_execution_receipt_key),
            ("execution-production", execution_receipt_key),
            ("pattern-evaluation-production", failed_pattern_receipt_key),
        ],
    )
    failure_corpus_wrapper = result_wrapper(
        "corpus-derivation-result", failure_corpus_invocation["invocationDigest"],
        "corpusResult", failure_corpus_result_key,
    )
    failure_corpus_wrapper_key = builder.add(
        "corpus-derivation-result", failure_corpus_wrapper,
        "bag16-corpus-derivation-result-failures.json",
    )
    failure_corpus_receipt = complete_receipt(
        failure_corpus_invocation, failure_corpus_wrapper_key,
        failure_corpus_result["decision"],
    )
    failure_corpus_receipt_key = builder.add(
        "operation-receipt", failure_corpus_receipt,
        "bag16-receipt-corpus-failures.json",
    )

    # Stop-after-test-match fold evaluates every declaration of the matching
    # test and represents only the later test suffix as explicit skipped
    # components with no attempt/result/receipt evidence.
    stop_slots = [
        [corpus_slot(
            0, 0, test_inv["testInvocationDigest"], declaration_key,
            roots, table_key, "exhaustive",
        )],
        [corpus_slot(
            1, 0, empty_test_inv["testInvocationDigest"], empty_declaration_key,
            roots, table_key, "exhaustive",
        )],
    ]
    stop_corpus = corpus_manifest_v2(
        old_corpus, [test_inv, empty_test_inv], stop_slots,
        scheduling="stop-after-test-match",
    )
    stop_corpus_key = builder.add(
        "corpus-manifest", stop_corpus, "bag16-corpus-manifest-stop-after-match.json",
    )
    stop_component_invocation = component_invocation(
        stop_corpus, stop_slots[0][0], exhaustive_key,
    )
    builder.add(
        "corpus-component-invocation", stop_component_invocation,
        "bag16-component-invocation-stop-match.json",
    )
    stop_match_component = evaluated_component(
        stop_corpus, stop_slots[0][0], stop_component_invocation, exhaustive_key,
        execution_result_key, execution_receipt_key, collection_key, pattern_inv,
        pattern_key, pattern_wrapper_key, pattern_receipt_key,
    )
    stop_match_component_key = builder.add(
        "corpus-component-result", stop_match_component,
        "bag16-component-result-stop-match.json",
    )
    stop_skipped_component = skipped_component(stop_corpus, stop_slots[1][0], 0)
    stop_skipped_component_key = builder.add(
        "corpus-component-result", stop_skipped_component,
        "bag16-component-result-stop-skipped.json",
    )
    stop_components = [stop_match_component, stop_skipped_component]
    stop_corpus_result = corpus_result_v2(
        stop_corpus, stop_components, {**old_assets, **builder.assets},
    )
    stop_corpus_result_key = builder.add(
        "corpus-result", stop_corpus_result,
        "bag16-corpus-result-stop-after-match.json",
    )
    stop_component_keys = [stop_match_component_key, stop_skipped_component_key]
    stop_corpus_invocation = invocation(
        "corpus-derivation", 1,
        {
            "corpusManifest": stop_corpus_key,
            "schedulingPolicy": "stop-after-test-match",
            "components": stop_component_keys,
        },
        [
            ("corpus-manifest", stop_corpus_key),
            *[("component-result", item) for item in stop_component_keys],
        ],
        [
            ("execution-production", execution_receipt_key),
            ("pattern-evaluation-production", pattern_receipt_key),
        ],
    )
    stop_corpus_wrapper = result_wrapper(
        "corpus-derivation-result", stop_corpus_invocation["invocationDigest"],
        "corpusResult", stop_corpus_result_key,
    )
    stop_corpus_wrapper_key = builder.add(
        "corpus-derivation-result", stop_corpus_wrapper,
        "bag16-corpus-derivation-result-stop-after-match.json",
    )
    stop_corpus_receipt = complete_receipt(
        stop_corpus_invocation, stop_corpus_wrapper_key, stop_corpus_result["decision"],
    )
    stop_corpus_receipt_key = builder.add(
        "operation-receipt", stop_corpus_receipt,
        "bag16-receipt-corpus-stop-after-match.json",
    )

    # BAG-12 execution-pattern projection produced only through the v2
    # collection-backed oracle operation and its exact pattern-evaluation
    # child receipt.
    baseline_subject = {
        "side": "baseline", "definitionDigest": old_corpus["definitionDigest"],
    }
    pattern_operand = oracle_operand(
        declaration_key, baseline_subject, test_inv["testInvocationDigest"], old_corpus,
        {"kind": "pattern-result", "patternResult": pattern_key},
        {
            "patternResult": pattern_key, "outcome": pattern["decision"]["kind"],
            "bindingTuples": [],
        },
    )
    pattern_operand_key = builder.add(
        "oracle-operand", pattern_operand, "bag16-oracle-operand-execution-pattern.json",
    )
    pattern_operand_invocation = invocation(
        "oracle-operand-production", 2,
        {
            "projectionKind": "execution-pattern",
            "declaration": declaration_key, "subject": subject,
            "patternEvaluationInvocation": pattern_inv,
            "patternEvaluationResult": pattern_wrapper_key,
            "patternResult": pattern_key, "collection": collection_key,
            **{field: deepcopy(roots[field]) for field in roots},
            "sideConditionTable": table_key, "searchPolicy": "exhaustive",
        },
        [
            ("declaration", declaration_key),
            ("pattern-evaluation-result", pattern_wrapper_key),
            ("pattern-result", pattern_key),
            ("branch-collection", collection_key),
        ],
        [("pattern-evaluation-production", pattern_receipt_key)],
    )
    pattern_operand_wrapper = oracle_operand_result(
        pattern_operand_invocation["invocationDigest"], pattern_operand_key,
    )
    pattern_operand_wrapper_key = builder.add(
        "oracle-operand-production-result", pattern_operand_wrapper,
        "bag16-oracle-operand-production-result-execution-pattern.json",
    )
    pattern_operand_receipt = complete_receipt(
        pattern_operand_invocation, pattern_operand_wrapper_key,
        pattern_operand_wrapper["outcome"],
    )
    pattern_operand_receipt_key = builder.add(
        "operation-receipt", pattern_operand_receipt,
        "bag16-receipt-oracle-operand-execution-pattern.json",
    )
    bindings_declaration = deepcopy(declaration)
    bindings_declaration["slotOrdinal"] += 1
    bindings_declaration["slotId"] = "execution-pattern-collection-bindings"
    bindings_declaration["oracleId"] = "execution-pattern-collection-bindings"
    bindings_declaration["projectionSpec"]["projectionId"] = "pattern-outcome-bindings-v1"
    bindings_declaration["comparisonSpec"]["comparatorId"] = "exact-pattern-outcome-bindings-v1"
    identify(bindings_declaration, "declarationId", "k-in-k/oracle-declaration/v1")
    bindings_declaration_key = builder.add(
        "oracle-declaration", bindings_declaration,
        "bag16-oracle-declaration-execution-pattern-bindings.json",
        bindings_declaration["declarationId"],
    )
    binding_tuples = [
        [
            {
                "name": binding["name"], "sort": binding["term"]["sort"],
                "value": deepcopy(binding["term"]),
            }
            for binding in witness["bindings"]
        ]
        for witness in pattern["witnesses"]
    ]
    bindings_operand = oracle_operand(
        bindings_declaration_key, baseline_subject,
        test_inv["testInvocationDigest"], old_corpus,
        {"kind": "pattern-result", "patternResult": pattern_key},
        {
            "patternResult": pattern_key, "outcome": pattern["decision"]["kind"],
            "bindingTuples": binding_tuples,
        },
    )
    bindings_operand_key = builder.add(
        "oracle-operand", bindings_operand,
        "bag16-oracle-operand-execution-pattern-bindings.json",
    )
    bindings_operand_invocation = invocation(
        "oracle-operand-production", 2,
        {
            "projectionKind": "execution-pattern",
            "declaration": bindings_declaration_key, "subject": subject,
            "patternEvaluationInvocation": pattern_inv,
            "patternEvaluationResult": pattern_wrapper_key,
            "patternResult": pattern_key, "collection": collection_key,
            **{field: deepcopy(roots[field]) for field in roots},
            "sideConditionTable": table_key, "searchPolicy": "exhaustive",
        },
        [
            ("declaration", bindings_declaration_key),
            ("pattern-evaluation-result", pattern_wrapper_key),
            ("pattern-result", pattern_key),
            ("branch-collection", collection_key),
        ],
        [("pattern-evaluation-production", pattern_receipt_key)],
    )
    bindings_operand_wrapper = oracle_operand_result(
        bindings_operand_invocation["invocationDigest"], bindings_operand_key,
    )
    bindings_operand_wrapper_key = builder.add(
        "oracle-operand-production-result", bindings_operand_wrapper,
        "bag16-oracle-operand-production-result-execution-pattern-bindings.json",
    )
    bindings_operand_receipt = complete_receipt(
        bindings_operand_invocation, bindings_operand_wrapper_key,
        bindings_operand_wrapper["outcome"],
    )
    bindings_operand_receipt_key = builder.add(
        "operation-receipt", bindings_operand_receipt,
        "bag16-receipt-oracle-operand-execution-pattern-bindings.json",
    )

    def derived_declaration(
        source_name: str, scenario_test: dict[str, Any], label: str,
        *, query: dict[str, str] | None = None,
    ) -> tuple[dict[str, Any], dict[str, str]]:
        value = deepcopy(read_json(fixtures / source_name))
        value["testInvocationDigest"] = scenario_test["testInvocationDigest"]
        value["boundsDigest"] = digest("k-in-k/bounds/v1", scenario_test["bounds"])
        if query is not None:
            value["kindConfig"]["query"] = deepcopy(query)
        identify(value, "declarationId", "k-in-k/oracle-declaration/v1")
        return value, builder.add(
            "oracle-declaration", value, f"bag16-oracle-declaration-{label}.json",
            value["declarationId"],
        )

    # An outcome-only execution-pattern projection may consume a trustworthy
    # match even when another occurrence is indeterminate.  The corresponding
    # bindings declaration is valid catalog material, but cannot consume this
    # false-coverage result.
    mixed_pattern_invocation = invocation(
        "pattern-evaluation", 1,
        {
            "collection": mixed_execution["collectionKey"],
            "executionResult": mixed_execution["resultKey"],
            **{name: deepcopy(side_roots[name]) for name in side_roots},
            "sideConditionTable": table_key, "searchPolicy": "exhaustive",
        },
        [
            ("execution-result", mixed_execution["resultKey"]),
            ("branch-collection", mixed_execution["collectionKey"]),
            ("pattern-source", side_roots["patternSource"]),
            ("pattern-plan", side_roots["patternPlan"]),
            ("pattern-query", side_roots["patternQuery"]),
            ("side-condition-conformance-table", table_key),
        ],
        [("execution-production", mixed_execution["receiptKey"])],
    )
    mixed_pattern_wrapper = result_wrapper(
        "pattern-evaluation-result", mixed_pattern_invocation["invocationDigest"],
        "patternResult", mixed_pattern_key,
    )
    mixed_pattern_wrapper_key = builder.add(
        "pattern-evaluation-result", mixed_pattern_wrapper,
        "bag16-pattern-evaluation-result-mixed-match-indeterminate.json",
    )
    mixed_pattern_receipt = complete_receipt(
        mixed_pattern_invocation, mixed_pattern_wrapper_key, mixed_pattern["decision"],
    )
    mixed_pattern_receipt_key = builder.add(
        "operation-receipt", mixed_pattern_receipt,
        "bag16-receipt-pattern-mixed-match-indeterminate.json",
    )
    mixed_outcome_declaration = deepcopy(declaration)
    mixed_outcome_declaration["testInvocationDigest"] = mixed_execution["test"]["testInvocationDigest"]
    mixed_outcome_declaration["boundsDigest"] = digest(
        "k-in-k/bounds/v1", mixed_execution["test"]["bounds"],
    )
    mixed_outcome_declaration["kindConfig"].update({
        **{name: deepcopy(side_roots[name]) for name in side_roots},
        "searchPolicy": "exhaustive",
    })
    identify(mixed_outcome_declaration, "declarationId", "k-in-k/oracle-declaration/v1")
    mixed_outcome_declaration_key = builder.add(
        "oracle-declaration", mixed_outcome_declaration,
        "bag16-oracle-declaration-execution-pattern-false-coverage-outcome.json",
        mixed_outcome_declaration["declarationId"],
    )
    mixed_bindings_declaration = deepcopy(mixed_outcome_declaration)
    mixed_bindings_declaration["slotOrdinal"] += 1
    mixed_bindings_declaration["slotId"] = "execution-pattern-false-coverage-bindings"
    mixed_bindings_declaration["oracleId"] = "execution-pattern-false-coverage-bindings"
    mixed_bindings_declaration["projectionSpec"]["projectionId"] = "pattern-outcome-bindings-v1"
    mixed_bindings_declaration["comparisonSpec"]["comparatorId"] = "exact-pattern-outcome-bindings-v1"
    identify(mixed_bindings_declaration, "declarationId", "k-in-k/oracle-declaration/v1")
    mixed_bindings_declaration_key = builder.add(
        "oracle-declaration", mixed_bindings_declaration,
        "bag16-oracle-declaration-execution-pattern-false-coverage-bindings.json",
        mixed_bindings_declaration["declarationId"],
    )
    mixed_outcome_operand = oracle_operand(
        mixed_outcome_declaration_key, baseline_subject,
        mixed_execution["test"]["testInvocationDigest"], old_corpus,
        {"kind": "pattern-result", "patternResult": mixed_pattern_key},
        {
            "patternResult": mixed_pattern_key,
            "outcome": mixed_pattern["decision"]["kind"], "bindingTuples": [],
        },
    )
    mixed_outcome_operand_key = builder.add(
        "oracle-operand", mixed_outcome_operand,
        "bag16-oracle-operand-execution-pattern-false-coverage-outcome.json",
    )
    mixed_outcome_invocation = invocation(
        "oracle-operand-production", 2,
        {
            "projectionKind": "execution-pattern",
            "declaration": mixed_outcome_declaration_key, "subject": subject,
            "patternEvaluationInvocation": mixed_pattern_invocation,
            "patternEvaluationResult": mixed_pattern_wrapper_key,
            "patternResult": mixed_pattern_key,
            "collection": mixed_execution["collectionKey"],
            **{field: deepcopy(side_roots[field]) for field in side_roots},
            "sideConditionTable": table_key, "searchPolicy": "exhaustive",
        },
        [
            ("declaration", mixed_outcome_declaration_key),
            ("pattern-evaluation-result", mixed_pattern_wrapper_key),
            ("pattern-result", mixed_pattern_key),
            ("branch-collection", mixed_execution["collectionKey"]),
        ],
        [("pattern-evaluation-production", mixed_pattern_receipt_key)],
    )
    mixed_outcome_wrapper = oracle_operand_result(
        mixed_outcome_invocation["invocationDigest"], mixed_outcome_operand_key,
    )
    mixed_outcome_wrapper_key = builder.add(
        "oracle-operand-production-result", mixed_outcome_wrapper,
        "bag16-oracle-operand-production-result-execution-pattern-false-coverage-outcome.json",
    )
    mixed_outcome_receipt = complete_receipt(
        mixed_outcome_invocation, mixed_outcome_wrapper_key,
        mixed_outcome_wrapper["outcome"],
    )
    mixed_outcome_receipt_key = builder.add(
        "operation-receipt", mixed_outcome_receipt,
        "bag16-receipt-oracle-operand-execution-pattern-false-coverage-outcome.json",
    )

    def occurrence_joins(scenario: dict[str, Any]) -> list[dict[str, Any]]:
        return [
            {
                "collection": scenario["collectionKey"],
                "branchKey": visit["branchKey"],
                "traceOccurrence": visit["traceOccurrence"],
            }
            for visit in scenario["collection"]["visited"]
        ]

    def publish_finite_operand(
        label: str, projection_kind: str, declaration_value: dict[str, Any],
        declaration_key_value: dict[str, str], scenario: dict[str, Any],
        table_key_value: dict[str, str], row_value: dict[str, Any],
        query_key_value: dict[str, str] | None,
        completion_evidence: dict[str, Any], normalized_value: dict[str, Any],
        extra_inputs: list[tuple[str, dict[str, str]]],
    ) -> tuple[dict[str, str], dict[str, str], dict[str, str]]:
        operand_value = oracle_operand(
            declaration_key_value, baseline_subject,
            scenario["test"]["testInvocationDigest"], old_corpus,
            completion_evidence, normalized_value,
        )
        operand_key_value = builder.add(
            "oracle-operand", operand_value, f"bag16-oracle-operand-{label}.json",
        )
        finite_parameters: dict[str, Any] = {
            "projectionKind": projection_kind,
            "declaration": declaration_key_value, "subject": subject,
            "executionInvocation": scenario["invocation"],
            "executionResult": scenario["resultKey"],
            "collection": scenario["collectionKey"],
            "finiteTable": table_key_value,
            "finiteRow": deepcopy(row_value),
            "occurrences": occurrence_joins(scenario),
        }
        finite_invocation = invocation(
            "oracle-operand-production", 2, finite_parameters,
            [
                ("declaration", declaration_key_value),
                ("execution-result", scenario["resultKey"]),
                ("branch-collection", scenario["collectionKey"]),
                *extra_inputs,
            ],
            [("execution-production", scenario["receiptKey"])],
        )
        finite_wrapper = oracle_operand_result(
            finite_invocation["invocationDigest"], operand_key_value,
        )
        finite_wrapper_key = builder.add(
            "oracle-operand-production-result", finite_wrapper,
            f"bag16-oracle-operand-production-result-{label}.json",
        )
        finite_receipt = complete_receipt(
            finite_invocation, finite_wrapper_key, finite_wrapper["outcome"],
        )
        finite_receipt_key = builder.add(
            "operation-receipt", finite_receipt,
            f"bag16-receipt-oracle-operand-{label}.json",
        )
        return operand_key_value, finite_wrapper_key, finite_receipt_key

    # Concrete-output finite row over the exact sole occurrence.
    concrete_declaration, concrete_declaration_key = derived_declaration(
        "oracle-declaration-concrete-output-ordered-output-bytes-agree.json",
        exhaustive_no_match["test"], "concrete-output",
    )
    base_output_table = read_json(fixtures / "semantic-output-finite-table.json")
    base_output_declaration = read_json(
        fixtures / "oracle-declaration-concrete-output-ordered-output-bytes-agree.json"
    )
    concrete_row = deepcopy(next(
        row for row in base_output_table["rows"]
        if row["declaration"]["digest"] == base_output_declaration["declarationId"]
        and row["subject"] == baseline_subject
        and row["terminal"]["artifact"] == terminal_key
    ))
    concrete_row["declaration"] = concrete_declaration_key
    concrete_row["testInvocationDigest"] = exhaustive_no_match["test"]["testInvocationDigest"]
    concrete_row["producerTrace"] = no_match_trace_key
    identify(concrete_row, "rowId", "k-in-k/semantic-output-finite-row/v1")
    concrete_table = identify({
        "schemaVersion": 1, "tableId": "0" * 64, "rows": [concrete_row],
    }, "tableId", "k-in-k/semantic-output-finite-table/v1")
    concrete_table_key = builder.add(
        "semantic-output-finite-table", concrete_table,
        "bag16-semantic-output-finite-table.json", concrete_table["tableId"],
    )
    concrete_operand_key, concrete_wrapper_key, concrete_receipt_key = publish_finite_operand(
        "concrete-output", "concrete-output", concrete_declaration,
        concrete_declaration_key, exhaustive_no_match, concrete_table_key,
        concrete_row, None,
        {
            "kind": "semantic-output-finite-row", "table": concrete_table_key,
            "rowId": concrete_row["rowId"],
        },
        {"channels": deepcopy(concrete_row["channels"])},
        [
            ("semantic-output-finite-table", concrete_table_key),
            ("row-terminal", terminal_key),
        ],
    )

    # Multi-occurrence reachability row equals the complete clean-exhausted
    # collection vector in visit order.  The selected accepted query has no
    # witnesses for this terminal, avoiding a digest-only witness collapse.
    not_reached_query_value = read_json(fixtures / "reachability-query-not-reached.json")
    not_reached_query_key = typed(
        "reachability-query", not_reached_query_value["queryId"],
    )
    reach_declaration, reach_declaration_key = derived_declaration(
        "oracle-declaration-reachability-reachability-truth-agree.json",
        mixed_execution["test"], "reachability", query=not_reached_query_key,
    )
    base_reach_table = read_json(fixtures / "reachability-conformance-table.json")
    base_reach_row = next(
        row for row in base_reach_table["rows"]
        if row["query"] == not_reached_query_key
        and row["subject"] == baseline_subject
        and row["terminalStates"] == [terminal_key]
    )
    reach_row = deepcopy(base_reach_row)
    reach_row["testInvocationDigest"] = mixed_execution["test"]["testInvocationDigest"]
    reach_row["terminalStates"] = [terminal_key, terminal_key]
    reach_row["producerTraces"] = [trace_key, indeterminate_trace_key]
    reach_row["finiteComplete"] = True
    reach_row["inputVectorDigest"] = digest(
        "k-in-k/reachability-finite-input/v1",
        {"terminalStates": reach_row["terminalStates"], "finiteComplete": True},
    )
    reach_row["witnesses"] = []
    reach_table = identify({
        "schemaVersion": 1, "tableId": "0" * 64, "rows": [reach_row],
    }, "tableId", "k-in-k/reachability-conformance-table/v1")
    reach_table_key = builder.add(
        "reachability-conformance-table", reach_table,
        "bag16-reachability-conformance-table.json", reach_table["tableId"],
    )
    reach_operand_key, reach_wrapper_key, reach_receipt_key = publish_finite_operand(
        "reachability", "reachability", reach_declaration, reach_declaration_key,
        mixed_execution,
        reach_table_key, reach_row, not_reached_query_key,
        {
            "kind": "reachability-finite-row", "table": reach_table_key,
            "query": not_reached_query_key,
            "inputVectorDigest": reach_row["inputVectorDigest"],
            "producerTraces": deepcopy(reach_row["producerTraces"]),
        },
        {"status": "not-reached", "witnesses": []},
        [
            ("reachability-conformance-table", reach_table_key),
            ("reachability-query", not_reached_query_key),
            *[("row-terminal", item) for item in reach_row["terminalStates"]],
        ],
    )

    # Structured-predicate finite row over the exact sole occurrence terminal.
    predicate_declaration, predicate_declaration_key = derived_declaration(
        "oracle-declaration-structured-predicate-predicate-bool-agree.json",
        exhaustive_no_match["test"], "structured-predicate",
    )
    predicate_query_key = deepcopy(predicate_declaration["kindConfig"]["query"])
    base_predicate_table = read_json(fixtures / "predicate-conformance-table.json")
    predicate_row = deepcopy(next(
        row for row in base_predicate_table["rows"]
        if row["query"] == predicate_query_key
        and row["subject"] == baseline_subject and row["input"] == terminal_key
    ))
    predicate_row["testInvocationDigest"] = exhaustive_no_match["test"]["testInvocationDigest"]
    predicate_row["producerTrace"] = no_match_trace_key
    predicate_table = identify({
        "schemaVersion": 1, "tableId": "0" * 64, "rows": [predicate_row],
    }, "tableId", "k-in-k/predicate-conformance-table/v1")
    predicate_table_key = builder.add(
        "predicate-conformance-table", predicate_table,
        "bag16-predicate-conformance-table.json", predicate_table["tableId"],
    )
    predicate_normalized = {
        field: deepcopy(predicate_row[field])
        for field in (
            "query", "input", "inputProjectionDigest", "bindings",
            "bindingsDigest", "result",
        )
    }
    predicate_operand_key, predicate_wrapper_key, predicate_receipt_key = publish_finite_operand(
        "structured-predicate", "structured-predicate", predicate_declaration,
        predicate_declaration_key, exhaustive_no_match, predicate_table_key,
        predicate_row, predicate_query_key,
        {
            "kind": "predicate-finite-row", "table": predicate_table_key,
            "query": predicate_query_key, "input": predicate_row["input"],
            "bindingsDigest": predicate_row["bindingsDigest"],
            "producerTrace": no_match_trace_key,
        },
        predicate_normalized,
        [
            ("predicate-conformance-table", predicate_table_key),
            ("predicate-query", predicate_query_key),
            ("predicate-input", predicate_row["input"]),
        ],
    )

    role_registry = build_role_spec_registry(root)

    def registry_for(
        result_key_value: dict[str, str] | None,
        receipt_key_value: dict[str, str], name: str,
    ) -> tuple[dict[str, Any], dict[str, str]]:
        all_assets = {**old_assets, **builder.assets}
        reached, operations, seed_schemas = _reachable(
            all_assets, result_key_value, receipt_key_value,
        )
        schema_names = _schema_names_for_assets(
            root, role_registry, all_assets, reached, seed_schemas,
        )
        registry = build_replay_registry(root, schema_names, operations)
        return registry, builder.add("replay-version-registry", registry, name)

    replay_registry, replay_registry_key = registry_for(
        corpus_wrapper_key, corpus_receipt_key, "bag16-replay-version-registry.json",
    )
    empty_registry, _ = registry_for(
        empty_result_key, empty_receipt_key, "bag16-replay-version-registry-empty.json",
    )
    existential_registry, _ = registry_for(
        existential_result_key, existential_receipt_key,
        "bag16-replay-version-registry-existential.json",
    )
    bounded_registry, _ = registry_for(
        bounded_result_key, bounded_receipt_key, "bag16-replay-version-registry-bounded.json",
    )
    failure_corpus_registry, _ = registry_for(
        failure_corpus_wrapper_key, failure_corpus_receipt_key,
        "bag16-replay-version-registry-corpus-failures.json",
    )
    stop_corpus_registry, _ = registry_for(
        stop_corpus_wrapper_key, stop_corpus_receipt_key,
        "bag16-replay-version-registry-corpus-stop.json",
    )
    multi_corpus_registry, _ = registry_for(
        multi_corpus_wrapper_key, multi_corpus_receipt_key,
        "bag16-replay-version-registry-corpus-two-execution.json",
    )
    pattern_root_registry, _ = registry_for(
        pattern_wrapper_key, pattern_receipt_key,
        "bag16-replay-version-registry-pattern-root.json",
    )
    failed_root_registry, _ = registry_for(
        None, failed_execution_receipt_key,
        "bag16-replay-version-registry-failed-execution-root.json",
    )
    pattern_operand_registry, _ = registry_for(
        pattern_operand_wrapper_key, pattern_operand_receipt_key,
        "bag16-replay-version-registry-oracle-pattern.json",
    )
    bindings_operand_registry, _ = registry_for(
        bindings_operand_wrapper_key, bindings_operand_receipt_key,
        "bag16-replay-version-registry-oracle-pattern-bindings.json",
    )
    mixed_outcome_registry, _ = registry_for(
        mixed_outcome_wrapper_key, mixed_outcome_receipt_key,
        "bag16-replay-version-registry-oracle-pattern-false-coverage.json",
    )
    concrete_registry, _ = registry_for(
        concrete_wrapper_key, concrete_receipt_key,
        "bag16-replay-version-registry-oracle-concrete.json",
    )
    reach_registry, _ = registry_for(
        reach_wrapper_key, reach_receipt_key,
        "bag16-replay-version-registry-oracle-reachability.json",
    )
    predicate_registry, _ = registry_for(
        predicate_wrapper_key, predicate_receipt_key,
        "bag16-replay-version-registry-oracle-predicate.json",
    )

    entries = deepcopy(old_entries)
    for entry in builder.publish():
        entries[(entry["role"], entry["digest"])] = entry
    catalog = {
        "schemaVersion": 2, "catalogId": "0" * 64,
        "roleSpecRegistryId": role_registry["registryId"],
        "entries": sorted(entries.values(), key=lambda item: (item["role"], item["digest"])),
        "unboundRequirements": [],
    }
    catalog = identify(catalog, "catalogId", "k-in-k/artifact-catalog/v2")
    write_json(fixtures / "bag16-artifact-role-specs.json", role_registry)
    write_json(fixtures / "bag16-artifact-catalog.json", catalog)

    def closure(
        root_kind: str, result_key: dict[str, str] | None,
        receipt_key_value: dict[str, str], caches: list[dict[str, str]],
        registry: dict[str, Any], name: str,
    ) -> dict[str, Any]:
        value = {
            "schemaVersion": 1, "closureId": "0" * 64, "rootKind": root_kind,
            "result": deepcopy(result_key), "receipt": deepcopy(receipt_key_value),
            "cacheRecords": deepcopy(caches), "artifactRoleSpecs": deepcopy(role_registry),
            "artifactCatalog": deepcopy(catalog), "registry": deepcopy(registry),
        }
        identify(value, "closureId", DOMAINS["closure"])
        write_json(fixtures / name, value)
        return value

    corpus_closure = closure(
        "corpus-derivation-result", corpus_wrapper_key, corpus_receipt_key,
        [cache_key], replay_registry, "bag16-closure-corpus.json",
    )
    execution_closure = closure(
        "execution-attempt-result", empty_result_key, empty_receipt_key,
        [empty_cache_key], empty_registry, "bag16-closure-empty-execution.json",
    )
    existential_closure = closure(
        "execution-attempt-result", existential_result_key, existential_receipt_key,
        [existential_cache_key], existential_registry,
        "bag16-closure-existential-execution.json",
    )
    bounded_closure = closure(
        "execution-attempt-result", bounded_result_key, bounded_receipt_key,
        [bounded_cache_key], bounded_registry, "bag16-closure-bounded-execution.json",
    )
    failure_corpus_closure = closure(
        "corpus-derivation-result", failure_corpus_wrapper_key,
        failure_corpus_receipt_key, [cache_key], failure_corpus_registry,
        "bag16-closure-corpus-failures.json",
    )
    stop_corpus_closure = closure(
        "corpus-derivation-result", stop_corpus_wrapper_key,
        stop_corpus_receipt_key, [cache_key], stop_corpus_registry,
        "bag16-closure-corpus-stop-after-match.json",
    )
    multi_corpus_closure = closure(
        "corpus-derivation-result", multi_corpus_wrapper_key,
        multi_corpus_receipt_key, [cache_key, empty_cache_key],
        multi_corpus_registry, "bag16-closure-corpus-two-execution.json",
    )
    pattern_root_closure = closure(
        "pattern-evaluation-result", pattern_wrapper_key,
        pattern_receipt_key, [cache_key], pattern_root_registry,
        "bag16-closure-pattern-evaluation.json",
    )
    failed_root_closure = closure(
        "execution-attempt-result", None, failed_execution_receipt_key, [],
        failed_root_registry, "bag16-closure-failed-execution.json",
    )
    pattern_operand_closure = closure(
        "oracle-operand-production-result", pattern_operand_wrapper_key,
        pattern_operand_receipt_key, [cache_key], pattern_operand_registry,
        "bag16-closure-oracle-execution-pattern.json",
    )
    bindings_operand_closure = closure(
        "oracle-operand-production-result", bindings_operand_wrapper_key,
        bindings_operand_receipt_key, [cache_key], bindings_operand_registry,
        "bag16-closure-oracle-execution-pattern-bindings.json",
    )
    mixed_outcome_closure = closure(
        "oracle-operand-production-result", mixed_outcome_wrapper_key,
        mixed_outcome_receipt_key, [mixed_execution["cacheKey"]],
        mixed_outcome_registry,
        "bag16-closure-oracle-execution-pattern-false-coverage.json",
    )
    concrete_closure = closure(
        "oracle-operand-production-result", concrete_wrapper_key,
        concrete_receipt_key, [exhaustive_no_match["cacheKey"]], concrete_registry,
        "bag16-closure-oracle-concrete-output.json",
    )
    reach_closure = closure(
        "oracle-operand-production-result", reach_wrapper_key, reach_receipt_key,
        [mixed_execution["cacheKey"]], reach_registry,
        "bag16-closure-oracle-reachability.json",
    )
    predicate_closure = closure(
        "oracle-operand-production-result", predicate_wrapper_key,
        predicate_receipt_key, [exhaustive_no_match["cacheKey"]], predicate_registry,
        "bag16-closure-oracle-structured-predicate.json",
    )
    vector = {
        "schemaVersion": 1, "artifactRoleSpecsId": role_registry["registryId"], "artifactCatalogId": catalog["catalogId"],
        "roots": {
            "twoBranchCorpus": corpus_closure["closureId"], "emptyExecution": execution_closure["closureId"],
            "existentialExecution": existential_closure["closureId"], "boundedExecution": bounded_closure["closureId"],
            "failureCorpus": failure_corpus_closure["closureId"],
            "stopAfterMatchCorpus": stop_corpus_closure["closureId"],
            "twoExecutionCorpus": multi_corpus_closure["closureId"],
            "patternEvaluation": pattern_root_closure["closureId"],
            "failedExecution": failed_root_closure["closureId"],
            "executionPatternOperand": pattern_operand_closure["closureId"],
            "executionPatternBindingsOperand": bindings_operand_closure["closureId"],
            "falseCoverageOutcomeOperand": mixed_outcome_closure["closureId"],
            "concreteOutputOperand": concrete_closure["closureId"],
            "reachabilityOperand": reach_closure["closureId"],
            "structuredPredicateOperand": predicate_closure["closureId"],
        },
        "evidence": {
            "sharedTrace": trace_key, "twoBranchCollection": collection_key, "twoBranchPattern": pattern_key,
            "emptyDecision": empty_key, "emptyPattern": empty_pattern_key,
            "existentialPattern": existential_pattern_key, "diagnosticCache": diagnostic_cache_key,
            "executionTestInvocation": test_inv_key, "replayRegistry": replay_registry_key,
            "exhaustiveNoMatch": exhaustive_no_match_pattern_key,
            "existentialExhaustedNoMatch": existential_no_match_pattern_key,
            "existentialPendingZero": existential_zero_pattern_key,
            "indeterminatePattern": indeterminate_pattern_key,
            "mixedIndeterminatePattern": mixed_pattern_key,
            "cleanDiagnosticCache": clean_diagnostic_cache_key,
            "backendAfterBoundedCache": backend_after_bounded["cacheKey"],
            "semanticCrashExecution": semantic_crash_execution["resultKey"],
            "errorPattern": error_pattern_key,
            "failureCorpusResult": failure_corpus_result_key,
            "stopAfterMatchCorpusResult": stop_corpus_result_key,
            "twoExecutionCorpusResult": multi_corpus_result_key,
            "patternOperand": pattern_operand_key,
            "patternBindingsOperand": bindings_operand_key,
            "falseCoverageOutcomeOperand": mixed_outcome_operand_key,
            "falseCoverageOutcomeReceipt": mixed_outcome_receipt_key,
            "falseCoverageBindingsDeclaration": mixed_bindings_declaration_key,
            "concreteOutputOperand": concrete_operand_key,
            "reachabilityOperand": reach_operand_key,
            "predicateOperand": predicate_operand_key,
        },
        "adversaries": [{"probe": name, "expected": "reject", "refreshModes": ["unchanged", "fully-refreshed"]} for name in ADVERSARIES],
    }
    write_json(root / "vectors" / "bag16-branch-collection-vectors.json", vector)


class Bag16Verifier:
    def __init__(self, root: Path, api: dict[str, Any]):
        self.root = root
        self.fixtures = root / "fixtures"
        self.api = api
        self.ok: Callable[[bool, str], None] = api["ok"]
        self.expect_schema_rejection: Callable[..., None] | None = api.get("expect_schema_rejection")
        self.role_registry = read_json(self.fixtures / "bag16-artifact-role-specs.json")
        self.catalog = read_json(self.fixtures / "bag16-artifact-catalog.json")
        self.entries = {(item["role"], item["digest"]): item for item in self.catalog["entries"]}
        self.assets: dict[tuple[str, str], Any] = {}
        for identity, entry in self.entries.items():
            if entry["availability"] != "bundled" or entry["contentModel"] != "canonical-json":
                continue
            path = root.parents[1] / entry["logicalPath"].removeprefix("repo://")
            if not path.is_file():
                continue
            data = path.read_bytes()
            if raw_sha256(data) != entry["contentSha256"]:
                continue
            value = json.loads(data.decode("utf-8"))
            if data == canonical(value).encode("utf-8"):
                self.assets[identity] = value
        self.vector = read_json(root / "vectors" / "bag16-branch-collection-vectors.json")
        self._bag12_oracle: Any | None = None
        self.bag14_manifest = read_json(
            self.fixtures / "bag14-cache-campaign-manifest.json",
        )
        definition_authorities = [
            read_json(self.fixtures / name)
            for name in (
                "semantic-definition-memory.json",
                "semantic-definition-counter.json",
                "semantic-definition-generated.json",
            )
        ]
        self.definition_authorities = {
            value["definitionDigest"]: value for value in definition_authorities
        }
        self.ok(
            len(self.definition_authorities) == len(definition_authorities),
            "BAG-16 accepted definition authorities repeat an identity",
        )
        self.receipts = {identity: value for (role, identity), value in self.assets.items() if role == "operation-receipt" and value.get("schemaVersion") == 2}
        taxonomies = [value for (role, _), value in self.assets.items() if role == "failure-taxonomy"]
        self.ok(len(taxonomies) == 1, "BAG-16 catalog does not select one successor failure taxonomy")
        self.taxonomy = taxonomies[0]
        self.validate_successor_taxonomy(self.taxonomy)

    def validate_successor_taxonomy(self, taxonomy: dict[str, Any]) -> None:
        self.ok(
            taxonomy["taxonomyId"]
            == digest("k-in-k/failure-taxonomy/v1", without(taxonomy, "taxonomyId"))
            and taxonomy == successor_failure_taxonomy(self.root),
            "BAG-16 successor failure taxonomy differs from its exact extension authority",
        )

    def resolve(self, artifact: dict[str, str]) -> Any:
        self.ok(set(artifact) == {"role", "digest"}, "BAG-16 artifact key is open")
        identity = (artifact["role"], artifact["digest"])
        self.ok(identity in self.entries, f"BAG-16 unresolved artifact {artifact}")
        self.ok(identity in self.assets, f"BAG-16 semantic artifact is unavailable {artifact}")
        return self.assets[identity]

    def validate_catalog(self, catalog: dict[str, Any]) -> None:
        self.ok(
            catalog["catalogId"]
            == digest("k-in-k/artifact-catalog/v2", without(catalog, "catalogId")),
            "BAG-16 catalog identity drift",
        )
        self.ok(
            catalog["roleSpecRegistryId"] == self.role_registry["registryId"],
            "BAG-16 catalog selects another role registry",
        )
        identities = [(item["role"], item["digest"]) for item in catalog["entries"]]
        self.ok(
            identities == sorted(identities) and len(identities) == len(set(identities)),
            "BAG-16 catalog duplicates or reorders an artifact key",
        )
        specs = {item["role"]: item for item in self.role_registry["specs"]}
        repository_root = self.root.parents[1].resolve()
        for entry in catalog["entries"]:
            self.ok(
                entry["role"] in specs
                and entry["contentModel"]
                == specs[entry["role"]]["contentModel"]
                and entry["mediaType"] == specs[entry["role"]]["mediaType"],
                "BAG-16 catalog entry metadata differs from its role authority",
            )
            scheme, separator, tail = entry["logicalPath"].partition("://")
            segments = tail.split("/")
            self.ok(
                bool(separator)
                and scheme in {"repo", "artifact"}
                and bool(tail)
                and all(segments)
                and all(segment not in {".", ".."} for segment in segments)
                and all(
                    all(0x20 <= ord(character) < 0x7f for character in segment)
                    for segment in segments
                )
                and "\\" not in tail
                and "%" not in tail
                and not tail.startswith("/"),
                "BAG-16 catalog entry locator is not normalized",
            )
            expected_resolution = (
                ("repo-v1", "bundled")
                if scheme == "repo"
                else ("rust-artifact-store-v1", "external-required")
            )
            self.ok(
                (entry["resolverId"], entry["availability"])
                == expected_resolution,
                "BAG-16 catalog resolver/scheme/availability drift",
            )
            if entry["availability"] != "bundled":
                continue
            try:
                path = (repository_root / tail).resolve(strict=True)
            except (FileNotFoundError, RuntimeError) as error:
                raise AssertionError(
                    "BAG-16 bundled catalog target cannot be resolved",
                ) from error
            self.ok(
                path.is_file() and path.is_relative_to(repository_root),
                "BAG-16 bundled catalog target is missing or escapes the repository",
            )
            data = path.read_bytes()
            content_hash = raw_sha256(data)
            self.ok(
                content_hash == entry["contentSha256"],
                "BAG-16 bundled artifact exact-byte hash drift",
            )
            if entry["contentModel"] == "opaque-bytes":
                self.ok(
                    entry["digest"]
                    == digest("k-in-k/opaque-artifact/v1", {
                        "role": entry["role"],
                        "mediaType": entry["mediaType"],
                        "contentSha256": content_hash,
                    }),
                    "BAG-16 opaque artifact semantic envelope drift",
                )
            else:
                try:
                    value = json.loads(data.decode("utf-8"))
                except (UnicodeDecodeError, json.JSONDecodeError) as error:
                    raise AssertionError(
                        "BAG-16 structured artifact is not UTF-8 JSON",
                    ) from error
                self.ok(
                    data == canonical(value).encode("utf-8"),
                    "BAG-16 structured artifact bytes are not canonical JSON",
                )

    def validate_resolver(self) -> None:
        self.ok(self.role_registry["registryId"] == digest("k-in-k/artifact-role-specs/v2", without(self.role_registry, "registryId")), "BAG-16 role registry identity drift")
        specs = self.role_registry["specs"]
        self.ok([item["role"] for item in specs] == sorted(item["role"] for item in specs) and len({item["role"] for item in specs}) == len(specs), "BAG-16 role specs are duplicate or unordered")
        self.ok(
            self.role_registry == build_role_spec_registry(self.root),
            "BAG-16 role registry differs from exact historical/successor authority",
        )
        self.validate_catalog(self.catalog)
        self.ok(len(self.entries) == len(self.catalog["entries"]), "BAG-16 catalog duplicates an artifact key")
        by_role = {item["role"]: item for item in specs}
        for identity, value in self.assets.items():
            self.validate_asset_identity(identity, value, by_role)

    def validate_asset_identity(
        self, identity: tuple[str, str], value: dict[str, Any],
        by_role: dict[str, dict[str, Any]] | None = None,
    ) -> None:
        by_role = by_role or {
            item["role"]: item for item in self.role_registry["specs"]
        }
        self.ok(
            identity[0] in by_role,
            f"BAG-16 active catalog role has no v2 dispatch {identity[0]}",
        )
        arm = select_structured_version(by_role[identity[0]], value)
        schema_for_artifact(self.root, self.role_registry, identity[0], value)
        projection = arm["projection"]
        if projection["kind"] == "without-field":
            payload = without(value, arm["selfIdField"])
        elif projection["kind"] == "complete":
            payload = value
        elif projection["kind"] == "field":
            payload = value[projection["field"]]
        elif projection["kind"] == "select-fields":
            payload = {
                field: value[field] for field in projection["fields"]
            }
        elif projection["kind"] == "definition-summary":
            payload = {
                "schemaVersion": value["schemaVersion"],
                "representation": value["representation"],
                "baselineFamilyId": value["baselineFamilyId"],
                "modules": [
                    {
                        "name": module["name"],
                        "ordinal": module["ordinal"],
                        "imports": module["imports"],
                        "sentenceContentFingerprints": [
                            sentence["provenance"]["contentFingerprint"]
                            for sentence in module["sentences"]
                        ],
                    }
                    for module in value["modules"]
                ],
            }
        else:
            raise AssertionError("BAG-16 resolver selected an unknown projection kind")
        self.ok(
            identity[1] == digest(arm["digestDomain"], payload),
            f"BAG-16 v2 dispatch digest drift for {identity}",
        )
        if arm.get("selfIdField") is not None:
            self.ok(
                value[arm["selfIdField"]] == identity[1],
                f"BAG-16 self ID/catalog key drift for {identity}",
            )

    def validate_test_invocation(
        self, value: dict[str, Any], manifest: dict[str, Any] | None = None,
    ) -> None:
        self.ok(
            value["testInvocationDigest"]
            == digest(DOMAINS["execution-test"], without(value, "testInvocationDigest")),
            "BAG-16 execution-test invocation identity drift",
        )
        self.ok(
            all(
                (value[field]["role"], value[field]["digest"]) in self.entries
                for field in ("program", "parser", "options")
            ),
            "BAG-16 execution-test invocation has an uncataloged input root",
        )
        if manifest is not None:
            self.ok(
                value["bounds"] == manifest["bounds"],
                "BAG-16 execution-test invocation bounds differ from corpus roots",
            )

    def validate_pattern_roots(
        self, pattern_source: dict[str, str], pattern_plan: dict[str, str],
        pattern_query: dict[str, str], observation: dict[str, str],
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        plan = self.resolve(pattern_plan)
        query = self.resolve(pattern_query)
        observation_value = self.resolve(observation)
        self.ok(
            pattern_source["role"] == "pattern-source"
            and pattern_plan["role"] == "pattern-plan"
            and pattern_query["role"] == "pattern-query"
            and (pattern_source["role"], pattern_source["digest"])
            in self.entries
            and plan["patternPlanDigest"]
            == digest("k-in-k/pattern-plan/v1", without(plan, "patternPlanDigest"))
            == pattern_plan["digest"]
            and query["queryId"]
            == digest("k-in-k/pattern-query/v1", without(query, "queryId"))
            == pattern_query["digest"]
            and query["patternPlan"] == pattern_plan
            and query["patternSource"] == pattern_source
            and plan["eventVocabularyDigest"]
            == observation_value["eventVocabularyDigest"],
            "BAG-16 pattern query/plan/source/observation roots drift",
        )
        self.validate_plan_semantics(plan, observation_value)
        return plan, query

    def validate_plan_semantics(
        self, plan: dict[str, Any], observation: dict[str, Any],
    ) -> None:
        constructors = observation["eventVocabulary"]
        self.ok(
            observation["eventVocabularyDigest"]
            == digest("k-in-k/event-vocabulary/v1", constructors),
            "BAG-16 event vocabulary identity drift",
        )
        declarations = {item["constructor"]: item for item in constructors}
        variables = plan["variables"]
        variable_sorts = {item["name"]: item["sort"] for item in variables}
        self.ok(
            len(variable_sorts) == len(variables)
            and all(
                re.fullmatch(r"[A-Z][A-Za-z0-9_]*", item["name"])
                for item in variables
            ),
            "BAG-16 pattern plan variable interface is invalid",
        )
        for arm in plan["arms"]:
            self.ok(
                len(arm["relations"]) == len(arm["atoms"]) - 1,
                "BAG-16 pattern arm relation/atom arity drift",
            )
            bound: set[str] = set()
            for atom in arm["atoms"]:
                self.ok(
                    atom["constructor"] in declarations,
                    "BAG-16 pattern atom uses an unknown constructor",
                )
                declaration = declarations[atom["constructor"]]
                positions = [clause["position"] for clause in atom["payload"]]
                self.ok(
                    positions == sorted(set(positions)),
                    "BAG-16 pattern atom payload positions are noncanonical",
                )
                for clause in atom["payload"]:
                    position, variable = clause["position"], clause["variable"]
                    self.ok(
                        re.fullmatch(r"[A-Z][A-Za-z0-9_]*", variable) is not None
                        and variable in variable_sorts
                        and position < len(declaration["payloadSorts"])
                        and variable_sorts[variable]
                        == declaration["payloadSorts"][position],
                        "BAG-16 pattern payload variable/arity/sort drift",
                    )
                    if clause["mode"] == "bind":
                        self.ok(
                            variable not in bound,
                            "BAG-16 pattern variable is multiply introduced",
                        )
                        bound.add(variable)
                    else:
                        self.ok(
                            variable in bound,
                            "BAG-16 pattern variable is used before binding",
                        )
            self.ok(
                bound == set(variable_sorts),
                "BAG-16 pattern arm does not bind its exact variable interface",
            )
        side = plan["sideCondition"]
        if side is not None:
            canonical_inputs = [
                item["name"] for item in variables
                if item["name"] in side["inputVariables"]
            ]
            self.ok(
                side["inputVariables"] == canonical_inputs
                and (side["artifact"]["role"], side["artifact"]["digest"])
                in self.entries,
                "BAG-16 pattern side-condition input/artifact drift",
            )

    def validate_side_condition_table(self, table: dict[str, Any]) -> None:
        self.ok(
            table["tableDigest"]
            == digest(
                "k-in-k/side-condition-conformance-table/v1",
                without(table, "tableDigest"),
            ),
            "BAG-16 side-condition table identity drift",
        )
        keys = [
            (
                row["condition"]["digest"], row["bindingsDigest"],
                row["pathPredicateDigest"],
            )
            for row in table["rows"]
        ]
        self.ok(
            keys == sorted(keys) and len(keys) == len(set(keys)),
            "BAG-16 side-condition table semantic keys are duplicate or noncanonical",
        )

    def validate_manifest(self, manifest: dict[str, Any]) -> None:
        self.ok(
            manifest["manifestId"]
            == digest(DOMAINS["corpus-manifest"], without(manifest, "manifestId")),
            "BAG-16 corpus manifest identity drift",
        )
        self.ok(
            [test["testOrdinal"] for test in manifest["tests"]]
            == list(range(len(manifest["tests"]))),
            "BAG-16 corpus test ordinals are noncontiguous",
        )
        for test in manifest["tests"]:
            test_invocation = self.resolve(typed(
                "execution-test-invocation", test["testInvocationDigest"],
            ))
            self.validate_test_invocation(test_invocation, manifest)
            self.ok(
                [slot["slotOrdinal"] for slot in test["slots"]]
                == list(range(len(test["slots"])))
                and all(
                    slot["testOrdinal"] == test["testOrdinal"]
                    and slot["testInvocationDigest"] == test["testInvocationDigest"]
                    and slot["slotId"]
                    == digest(DOMAINS["slot"], without(slot, "slotId"))
                    for slot in test["slots"]
                ),
                "BAG-16 corpus slot identity/test order drift",
            )
            for slot in test["slots"]:
                declaration = self.resolve(slot["declaration"])
                self.ok(
                    declaration["declarationId"]
                    == digest(
                        "k-in-k/oracle-declaration/v1",
                        without(declaration, "declarationId"),
                    )
                    and declaration["kind"] == "execution-pattern"
                    and declaration["testInvocationDigest"]
                    == test["testInvocationDigest"]
                    and declaration["compatibilityProfileDigest"]
                    == manifest["compatibilityProfileDigest"]
                    and declaration["executionProfileDigest"]
                    == manifest["executionProfileDigest"]
                    and declaration["solverProfileDigest"]
                    == manifest["solverProfileDigest"]
                    and declaration["boundsDigest"]
                    == digest("k-in-k/bounds/v1", manifest["bounds"])
                    and all(
                        declaration["kindConfig"][field] == slot[field]
                        for field in (
                            "patternSource", "patternPlan", "patternQuery",
                            "searchPolicy",
                        )
                    ),
                    "BAG-16 corpus slot/declaration/test/profile/query roots drift",
                )
                self.validate_pattern_roots(
                    slot["patternSource"], slot["patternPlan"], slot["patternQuery"],
                    typed("observation-manifest", manifest["observationManifestDigest"]),
                )
                self.validate_side_condition_table(
                    self.resolve(slot["sideConditionTable"]),
                )

    def validate_execution_key(
        self, value: dict[str, Any], *, manifest: dict[str, Any] | None = None,
        slot: dict[str, Any] | None = None,
    ) -> None:
        self.ok(
            value["keyDigest"]
            == digest(DOMAINS["execution-key"], without(value, "keyDigest")),
            "BAG-16 execution key identity drift",
        )
        self.ok(
            value["operation"] == {
                "operationId": "portable-finite-execution", "operationVersion": 4,
                "adapterId": "bag16-vector-adapter", "adapterVersion": 1,
            },
            "BAG-16 execution key portable operation drift",
        )
        isolation = value["isolationPolicy"]
        self.ok(
            isolation["isolationPolicyDigest"]
            == digest("k-in-k/isolation-policy/v1", without(isolation, "isolationPolicyDigest")),
            "BAG-16 execution key isolation policy identity drift",
        )
        self.ok(
            value["loweringProfileDigest"]
            == self.bag14_manifest["loweringProfile"]["digest"]
            and value["executionProfileDigest"]
            == self.bag14_manifest["executionProfile"]["digest"]
            and value["solverProfileDigest"]
            == self.bag14_manifest["solverProfile"]["digest"]
            and isolation == self.bag14_manifest["isolationPolicy"],
            "BAG-16 execution key differs from accepted BAG-14 profile/isolation authority",
        )
        test_invocation = self.resolve(typed(
            "execution-test-invocation", value["testInvocationDigest"],
        ))
        self.validate_test_invocation(test_invocation, manifest)
        attempt = value["attemptKind"]
        self.ok(
            len(attempt["observationInputs"]) == 1,
            "BAG-16 execution key observation input cardinality drift",
        )
        observation = self.resolve(attempt["observationInputs"][0])
        subject_definition = (
            value["subject"]["definition"]["digest"]
            if value["subject"]["kind"] == "baseline"
            else value["subject"]["mutantDefinition"]["digest"]
        )
        subject_role = (
            "definition"
            if value["subject"]["kind"] == "baseline"
            else "mutant-definition"
        )
        self.ok(
            observation["manifestId"]
            == digest(
                "k-in-k/observation-manifest/v1",
                without(observation, "manifestId"),
            )
            and observation["inputDefinitionDigest"]
            == observation["outputDefinitionDigest"]
            == subject_definition
            and observation["compatibilityProfileDigest"]
            == value["compatibilityProfileDigest"],
            "BAG-16 execution observation interface belongs to another subject/profile",
        )
        self.ok(
            (subject_role, subject_definition) in self.entries,
            "BAG-16 execution subject is absent from catalog authority",
        )
        if attempt["kind"] == "observed-exhaustive":
            self.ok(
                set(attempt) == {"kind", "observationInputs"},
                "BAG-16 generic exhaustive key is polluted with query identity",
            )
        else:
            self.ok(
                attempt["kind"] == "query-coupled"
                and set(attempt) == {
                    "kind", "observationInputs", "patternSource", "patternPlan",
                    "patternQuery", "sideConditionTable", "searchPolicy",
                }
                and attempt["searchPolicy"] == "existential-first",
                "BAG-16 existential execution key lacks exact query identity",
            )
        if manifest is not None:
            self.ok(
                value["subject"] == {"kind": "baseline", "definition": manifest["definition"]}
                and value["compatibilityProfileDigest"] == manifest["compatibilityProfileDigest"]
                and value["executionProfileDigest"] == manifest["executionProfileDigest"]
                and value["solverProfileDigest"] == manifest["solverProfileDigest"]
                and attempt["observationInputs"] == [typed(
                    "observation-manifest", manifest["observationManifestDigest"],
                )],
                "BAG-16 execution key differs from corpus subject/profile roots",
            )
        if slot is not None:
            self.ok(
                manifest is not None
                and value["testInvocationDigest"] == slot["testInvocationDigest"],
                "BAG-16 execution key/test/slot invocation drift",
            )
            if slot["searchPolicy"] == "exhaustive":
                self.ok(
                    attempt == {
                        "kind": "observed-exhaustive",
                        "observationInputs": [typed(
                            "observation-manifest", manifest["observationManifestDigest"],
                        )],
                    },
                    "BAG-16 exhaustive slot did not select an exact query-neutral key",
                )
            else:
                self.ok(
                    slot["searchPolicy"] == "existential-first"
                    and attempt == {
                        "kind": "query-coupled",
                        "observationInputs": [typed(
                            "observation-manifest", manifest["observationManifestDigest"],
                        )],
                        **{field: deepcopy(slot[field]) for field in (
                            "patternSource", "patternPlan", "patternQuery",
                            "sideConditionTable", "searchPolicy",
                        )},
                    },
                    "BAG-16 existential slot did not select its exact query-coupled key",
                )

    def execution_invocation_for_collection(self, collection: dict[str, Any]) -> dict[str, Any]:
        matches = [
            value for value in self.receipts.values()
            if value["invocation"]["operationKind"] == "execution-attempt"
            and value["producerStatus"] == "complete"
            and value["invocationDigest"] == collection["invocationDigest"]
            and value["invocation"]["parameters"]["keyDigest"] == collection["attemptKeyDigest"]
            and value["outputs"]
            and self.assets.get((
                value["outputs"][0]["artifact"]["role"],
                value["outputs"][0]["artifact"]["digest"],
            ), {}).get("branchCollection")
            == typed("branch-trace-collection", collection["collectionId"])
        ]
        invocations = {canonical(value["invocation"]): value["invocation"] for value in matches}
        self.ok(
            len(invocations) == 1,
            "BAG-16 collection has no single exact completed execution invocation",
        )
        return next(iter(invocations.values()))

    def validate_trace(self, trace: dict[str, Any]) -> None:
        self.ok(trace["traceId"] == digest(DOMAINS["trace"], without(trace, "traceId")), "BAG-16 trace identity drift")
        forbidden = {"testId", "pathKey", "pathOrdinal", "visitOrdinal", "disposition", "executionTerminal", "stopReason", "receipt"}
        self.ok(not (forbidden & set(trace)), "BAG-16 occurrence-neutral trace contains occurrence/result provenance")
        self.ok([event["index"] for event in trace["events"]] == list(range(len(trace["events"]))), "BAG-16 trace event indices are noncontiguous")

    def validate_portable_term(
        self, term: dict[str, Any],
        signatures: dict[str, tuple[str, str, int, tuple[str, ...]]],
        variables: dict[str, str],
    ) -> None:
        self.ok(
            term["encoding"] == "portable-term-v1",
            "BAG-16 trace term uses a nonportable encoding",
        )
        node = term["node"]
        kind = node["kind"]
        self.ok(
            kind in {
                "token", "variable", "rewrite", "application", "sequence",
                "injection",
            },
            "BAG-16 trace term uses an unknown node kind",
        )
        if kind == "variable":
            previous = variables.setdefault(node["name"], term["sort"])
            self.ok(
                previous == term["sort"],
                "BAG-16 trace variable has conflicting local sorts",
            )
        elif kind == "rewrite":
            self.validate_portable_term(node["left"], signatures, variables)
            self.validate_portable_term(node["right"], signatures, variables)
            self.ok(
                node["left"]["sort"] == node["right"]["sort"],
                "BAG-16 trace rewrite children have different sorts",
            )
        elif kind == "application":
            for argument in node["args"]:
                self.validate_portable_term(argument, signatures, variables)
            signature = (
                node["label"], term["sort"], len(node["args"]),
                tuple(argument["sort"] for argument in node["args"]),
            )
            previous = signatures.setdefault(node["symbolId"], signature)
            self.ok(
                previous == signature,
                "BAG-16 trace symbol has a conflicting label or signature",
            )
        elif kind == "sequence":
            for item in node["items"]:
                self.validate_portable_term(item, signatures, variables)
        elif kind == "injection":
            self.validate_portable_term(node["term"], signatures, variables)
            self.ok(
                node["term"]["sort"] == node["fromSort"]
                and term["sort"] == node["toSort"],
                "BAG-16 trace injection sorts contradict its wrapper",
            )

    def definition_signatures(
        self, definition: dict[str, Any],
    ) -> dict[str, tuple[str, str, int, tuple[str, ...]]]:
        signatures: dict[str, tuple[str, str, int, tuple[str, ...]]] = {}
        for module in definition["modules"]:
            for sentence in module["sentences"]:
                variables: dict[str, str] = {}
                value = sentence["value"]
                self.validate_portable_term(value["body"], signatures, variables)
                for field in ("requires", "ensures"):
                    condition = value[field]
                    if condition is not None:
                        self.ok(
                            condition["sort"] == "Bool",
                            "BAG-16 definition condition is not Bool-sorted",
                        )
                        self.validate_portable_term(
                            condition, signatures, variables,
                        )
                for attribute in value["attributes"]:
                    if attribute["value"] is not None:
                        self.validate_portable_term(
                            attribute["value"], signatures, variables,
                        )
        return signatures

    def validate_trace_execution_relation(
        self, trace: dict[str, Any], disposition: dict[str, Any],
        attempt: dict[str, Any],
    ) -> None:
        subject = attempt["subject"]
        definition = (
            subject["definition"]["digest"] if subject["kind"] == "baseline"
            else subject["mutantDefinition"]["digest"]
        )
        observation = self.resolve(attempt["attemptKind"]["observationInputs"][0])
        definition_value = self.definition_authorities.get(definition)
        self.ok(
            definition_value is not None
            and trace["definitionDigest"] == definition
            and trace["eventVocabularyDigest"] == observation["eventVocabularyDigest"]
            and observation["compatibilityProfileDigest"]
            == attempt["compatibilityProfileDigest"],
            "BAG-16 trace definition/vocabulary differs from its execution roots",
        )
        signatures = self.definition_signatures(definition_value)
        variables: dict[str, str] = {}
        self.validate_portable_term(
            trace["pathPredicate"], signatures, variables,
        )
        self.ok(
            trace["pathPredicate"]["sort"] == "Bool",
            "BAG-16 trace path predicate is not Bool-sorted",
        )
        provenances = {
            sentence["provenance"]["lineageId"]: sentence["provenance"]
            for module in definition_value["modules"]
            for sentence in module["sentences"]
        }
        declarations = {
            item["constructor"]: item for item in observation["eventVocabulary"]
        }
        previous_transition = -1
        expected_emission = 0
        for event in trace["events"]:
            transition = event["transitionOrdinal"]
            if transition != previous_transition:
                expected_emission = 0
            self.ok(
                transition >= previous_transition
                and event["emissionOrdinal"] == expected_emission,
                "BAG-16 trace transition/emission order drift",
            )
            expected_emission += 1
            previous_transition = transition
            self.ok(
                event["constructor"] in declarations,
                "BAG-16 trace event uses an undeclared constructor",
            )
            declaration = declarations[event["constructor"]]
            self.ok(
                [term["sort"] for term in event["payload"]]
                == declaration["payloadSorts"]
                and all(term.get("encoding") == "portable-term-v1" for term in event["payload"]),
                "BAG-16 trace event payload arity/sort/encoding drift",
            )
            for term in event["payload"]:
                self.validate_portable_term(term, signatures, variables)
            emitting = event["origin"]["emittingSentence"]
            lineage = emitting["lineageId"]
            self.ok(
                lineage in provenances and emitting == provenances[lineage],
                "BAG-16 trace emitting provenance differs from definition authority",
            )
            matching = [
                emission
                for selection in observation["selections"]
                if lineage in selection["matchedLineages"]
                for emission in selection["emissions"]
                if emission["constructor"] == event["constructor"]
            ]
            self.ok(
                len(matching) == 1,
                "BAG-16 trace event lineage is not uniquely observation-authorized",
            )
            template = matching[0]["semanticSite"]
            expected_site = None
            if template is not None:
                expected_site = {
                    "siteId": digest("k-in-k/observation-site/v1", {
                        "observerDigest": observation["observerDigest"],
                        "observerVersion": 1,
                        "definitionDigest": observation["inputDefinitionDigest"],
                        "targetLineage": lineage, "role": template["role"],
                        "termPath": template["termPath"],
                    }),
                    "role": template["role"], "termPath": template["termPath"],
                }
            self.ok(
                event["origin"]["semanticSite"] == expected_site
                and (
                    (declaration["originMode"] == "emitting-sentence" and expected_site is None)
                    or (
                        declaration["originMode"]
                        == "emitting-sentence-and-semantic-site"
                        and expected_site is not None
                    )
                ),
                "BAG-16 trace event semantic-site provenance drift",
            )
        terminal: dict[str, Any] | None = None
        if disposition["kind"] in {"normal", "stuck"}:
            terminal = self.resolve(disposition["terminal"])
            self.ok(
                terminal["definitionDigest"] == definition,
                "BAG-16 occurrence terminal belongs to another definition",
            )
        elif disposition["kind"] == "semantic-crash":
            crash = self.resolve(disposition["crash"])
            terminal = self.resolve(crash["terminalState"])
            self.ok(
                crash["crashDigest"]
                == digest("k-in-k/semantic-crash/v1", without(crash, "crashDigest"))
                and terminal["definitionDigest"] == definition
                and crash["executionProfileDigest"]
                == attempt["executionProfileDigest"],
                "BAG-16 semantic crash terminal/profile differs from its execution",
            )
        if terminal is not None:
            self.ok(
                terminal["terminalStateDigest"]
                == digest(
                    "k-in-k/terminal-state/v1",
                    without(terminal, "terminalStateDigest"),
                ),
                "BAG-16 occurrence terminal identity drift",
            )
            self.validate_portable_term(
                terminal["value"], signatures, {},
            )

    def validate_collection_stop_relation(
        self, collection: dict[str, Any], attempt: dict[str, Any],
    ) -> None:
        visits = collection["visited"]
        stop = collection["stopReason"]
        pending = collection["pendingWork"]["discoveredCount"]
        if stop["kind"] == "search-exhausted":
            self.ok(pending == 0, "BAG-16 search exhaustion retained pending work")
        if stop["kind"] == "match-found":
            self.ok(
                bool(visits)
                and visits[-1]["disposition"]["kind"] == "query-satisfied",
                "BAG-16 existential stop lacks final query-satisfied path",
            )
        query_satisfied = [
            index for index, visit in enumerate(visits)
            if visit["disposition"]["kind"] == "query-satisfied"
        ]
        self.ok(
            not query_satisfied
            or (
                stop["kind"] == "match-found"
                and query_satisfied == [len(visits) - 1]
                and attempt["attemptKind"]["kind"] == "query-coupled"
            ),
            "BAG-16 query-satisfied occurrence is not the sole final match-found record",
        )

    def validate_collection(self, collection: dict[str, Any]) -> None:
        self.ok(collection["collectionId"] == digest(DOMAINS["collection"], without(collection, "collectionId")), "BAG-16 collection identity drift")
        expected_scope = collection_scope(collection["attemptKeyDigest"], collection["invocationDigest"])
        self.ok(collection["collectionScopeId"] == expected_scope, "BAG-16 collection scope drift")
        invocation_value = self.execution_invocation_for_collection(collection)
        attempt = invocation_value["parameters"]["executionKey"]
        self.validate_execution_key(attempt)
        attempt_kind = attempt["attemptKind"]
        expected_coupling = "query-independent" if attempt_kind["kind"] == "observed-exhaustive" else "pattern-query"
        self.ok(collection["queryCoupling"] == {"kind": expected_coupling}, "BAG-16 query coupling/request kind drift")
        if expected_coupling == "query-independent":
            self.ok(collection["stopReason"]["kind"] != "match-found", "BAG-16 query-neutral exhaustive attempt stopped on match")
        else:
            self.ok(attempt_kind["searchPolicy"] == "existential-first", "BAG-16 query-coupled attempt is not existential-first")
        visits = collection["visited"]
        self.ok([item["visitOrdinal"] for item in visits] == list(range(len(visits))), "BAG-16 collection visit ordinals are noncontiguous")
        for visit in visits:
            expected = visit_record(expected_scope, collection["invocationDigest"], visit["visitOrdinal"], visit["trace"], visit["disposition"])
            self.ok(visit == expected, "BAG-16 branch or occurrence identity drift")
            trace = self.resolve(visit["trace"])
            self.validate_trace(trace)
            self.validate_trace_execution_relation(trace, visit["disposition"], attempt)
        self.validate_collection_stop_relation(collection, attempt)
        stop = collection["stopReason"]
        pending = collection["pendingWork"]["discoveredCount"]
        if stop["kind"] == "search-exhausted":
            self.ok(pending == 0, "BAG-16 search exhaustion retained pending work")
        if stop["kind"] == "match-found":
            self.ok(bool(visits) and visits[-1]["disposition"]["kind"] == "query-satisfied", "BAG-16 existential stop lacks final query-satisfied path")
        query_satisfied = [
            index for index, visit in enumerate(visits)
            if visit["disposition"]["kind"] == "query-satisfied"
        ]
        self.ok(
            not query_satisfied
            or (
                stop["kind"] == "match-found"
                and query_satisfied == [len(visits) - 1]
                and attempt_kind["kind"] == "query-coupled"
            ),
            "BAG-16 query-satisfied occurrence is not the sole final match-found record",
        )
        marker = collection["emptySearchDecision"]
        if not visits and stop["kind"] == "search-exhausted":
            self.ok(marker is not None, "BAG-16 empty exhaustion lacks explicit execution decision")
            decision = self.resolve(marker)
            self.ok(decision == empty_search_decision(collection["attemptKeyDigest"], collection["invocationDigest"]), "BAG-16 empty decision/request roots drift")
        else:
            self.ok(marker is None, "BAG-16 nonempty/nonexhausted collection carries empty marker")

    def validate_execution_wrapper(self, result: dict[str, Any], receipt: dict[str, Any]) -> None:
        inv = receipt["invocation"]
        execution_key_value = inv["parameters"]["executionKey"]
        self.validate_execution_key(execution_key_value)
        self.ok(result["resultId"] == digest(DOMAINS["execution-result"], without(result, "resultId")), "BAG-16 execution wrapper identity drift")
        collection = self.resolve(result["branchCollection"])
        self.validate_collection(collection)
        expected_outputs = produced_artifacts(
            collection["visited"], result["branchCollection"],
            collection["emptySearchDecision"], self.assets,
        )
        self.ok(result["producedArtifacts"] == expected_outputs, "BAG-16 execution output order/cardinality drift")
        expected_terminal = {"kind": "branch-collection", "collection": result["branchCollection"], "stopReason": collection["stopReason"]}
        self.ok(result["terminalRecord"] == expected_terminal == receipt["semanticTerminal"], "BAG-16 wrapper/receipt/collection terminal drift")
        self.ok(result["attemptKeyDigest"] == execution_key_value["keyDigest"] == inv["parameters"]["keyDigest"], "BAG-16 execution key relation drift")
        self.ok(result["invocationDigest"] == receipt["invocationDigest"], "BAG-16 execution wrapper names another invocation")

    def validate_execution_invocation(self, invocation_value: dict[str, Any]) -> None:
        execution_key_value = invocation_value["parameters"]["executionKey"]
        self.validate_execution_key(execution_key_value)
        self.ok(
            invocation_value == invocation(
                "execution-attempt", 2,
                {
                    "executionKey": execution_key_value,
                    "keyDigest": execution_key_value["keyDigest"],
                },
                _execution_inputs(execution_key_value),
            ),
            "BAG-16 execution invocation/key/input closure drift",
        )

    def validate_pattern_invocation(
        self, invocation_value: dict[str, Any],
    ) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
        parameters = invocation_value["parameters"]
        self.ok(
            len(invocation_value["childReceipts"]) == 1,
            "BAG-16 pattern invocation child cardinality drift",
        )
        self.ok(
            invocation_value == invocation(
                "pattern-evaluation", 1, parameters,
                [
                    ("execution-result", parameters["executionResult"]),
                    ("branch-collection", parameters["collection"]),
                    ("pattern-source", parameters["patternSource"]),
                    ("pattern-plan", parameters["patternPlan"]),
                    ("pattern-query", parameters["patternQuery"]),
                    ("side-condition-conformance-table", parameters["sideConditionTable"]),
                ],
                [("execution-production", invocation_value["childReceipts"][0]["receipt"])],
            )
            and invocation_value["childReceipts"][0]["edgeRole"] == "execution-production",
            "BAG-16 pattern invocation input/child closure drift",
        )
        execution_receipt = self.resolve(invocation_value["childReceipts"][0]["receipt"])
        self.validate_receipt(execution_receipt)
        self.ok(
            execution_receipt["producerStatus"] == "complete"
            and execution_receipt["outputs"][0]["artifact"] == parameters["executionResult"],
            "BAG-16 pattern invocation lacks its paired completed execution",
        )
        execution_result_value = self.resolve(parameters["executionResult"])
        collection = self.resolve(parameters["collection"])
        self.validate_side_condition_table(self.resolve(parameters["sideConditionTable"]))
        self.ok(
            execution_result_value["branchCollection"] == parameters["collection"],
            "BAG-16 pattern invocation execution/collection drift",
        )
        attempt = execution_receipt["invocation"]["parameters"]["executionKey"]
        self.validate_pattern_roots(
            parameters["patternSource"], parameters["patternPlan"],
            parameters["patternQuery"], attempt["attemptKind"]["observationInputs"][0],
        )
        attempt_kind = attempt["attemptKind"]
        if attempt_kind["kind"] == "observed-exhaustive":
            self.ok(
                parameters["searchPolicy"] == "exhaustive"
                and collection["queryCoupling"] == {"kind": "query-independent"},
                "BAG-16 pattern invocation polluted a query-neutral execution",
            )
        else:
            self.ok(
                attempt_kind["kind"] == "query-coupled"
                and collection["queryCoupling"] == {"kind": "pattern-query"}
                and all(
                    parameters[field] == attempt_kind[field]
                    for field in (
                        "patternSource", "patternPlan", "patternQuery",
                        "sideConditionTable", "searchPolicy",
                    )
                ),
                "BAG-16 pattern invocation differs from its query-coupled execution",
            )
        return execution_receipt, execution_result_value, collection

    def validate_pattern_operation(
        self, wrapper: dict[str, Any], receipt: dict[str, Any],
    ) -> None:
        _, _, collection = self.validate_pattern_invocation(receipt["invocation"])
        parameters = receipt["invocation"]["parameters"]
        pattern = self.resolve(wrapper["patternResult"])
        self.validate_pattern(pattern)
        self.ok(
            pattern["collection"] == parameters["collection"]
            and all(
                pattern[field] == parameters[field]
                for field in (
                    "patternSource", "patternPlan", "patternQuery",
                    "sideConditionTable", "searchPolicy",
                )
            )
            and receipt["semanticTerminal"] == pattern["decision"]
            and receipt["failure"] is None,
            "BAG-16 pattern wrapper/request/decision terminal drift",
        )
        if not collection["visited"]:
            execution_result_value = self.resolve(parameters["executionResult"])
            self.ok(
                collection["emptySearchDecision"] is not None
                and execution_result_value["producedArtifacts"][-2]
                == collection["emptySearchDecision"],
                "BAG-16 empty pattern invocation lost its execution-produced marker",
            )

    def validate_corpus_invocation(
        self, invocation_value: dict[str, Any],
    ) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        parameters = invocation_value["parameters"]
        manifest = self.resolve(parameters["corpusManifest"])
        self.validate_manifest(manifest)
        components = [self.resolve(item) for item in parameters["components"]]
        expected_children: list[tuple[str, dict[str, str]]] = []
        for component in components:
            if component["kind"] in {"evaluated", "pattern-failure"}:
                expected_children.append(("execution-production", component["executionReceipt"]))
                expected_children.append((
                    "pattern-evaluation-production",
                    component["patternEvaluationReceipt"],
                ))
            elif component["kind"] == "execution-failure":
                expected_children.append(("execution-production", component["executionReceipt"]))
        expected = invocation(
            "corpus-derivation", 1,
            {
                "corpusManifest": parameters["corpusManifest"],
                "schedulingPolicy": manifest["aggregation"]["schedulingPolicy"],
                "components": parameters["components"],
            },
            [
                ("corpus-manifest", parameters["corpusManifest"]),
                *[("component-result", item) for item in parameters["components"]],
            ],
            expected_children,
        )
        self.ok(
            invocation_value == expected,
            "BAG-16 corpus invocation manifest/component/input/child closure drift",
        )
        return manifest, components

    def validate_corpus_operation(
        self, wrapper: dict[str, Any], receipt: dict[str, Any],
    ) -> None:
        manifest, components = self.validate_corpus_invocation(receipt["invocation"])
        corpus = self.resolve(wrapper["corpusResult"])
        self.validate_corpus(corpus)
        parameters = receipt["invocation"]["parameters"]
        self.ok(
            corpus["corpusManifest"] == parameters["corpusManifest"]
            and corpus["schedulingPolicy"] == parameters["schedulingPolicy"]
            and corpus["components"] == parameters["components"]
            and receipt["semanticTerminal"] == corpus["decision"]
            and receipt["failure"] is None,
            "BAG-16 corpus wrapper/request/aggregate terminal drift",
        )

    def validate_receipt(self, value: dict[str, Any]) -> None:
        self.ok(value["receiptId"] == digest(DOMAINS["receipt"], without(value, "receiptId")), "BAG-16 receipt identity drift")
        inv = value["invocation"]
        self.ok(value["invocationDigest"] == inv["invocationDigest"] == digest(DOMAINS["invocation"], without(inv, "invocationDigest")), "BAG-16 invocation/receipt identity drift")
        operation = inv["operationKind"]
        expected_version = {"execution-attempt": 2, "pattern-evaluation": 1, "corpus-derivation": 1, "oracle-operand-production": 2}[operation]
        self.ok(inv["operationVersion"] == expected_version and inv["outputRoles"] == [OUTPUT_ROLES[operation]], "BAG-16 operation version/output role drift")
        if operation == "execution-attempt":
            self.validate_execution_invocation(inv)
        elif operation == "pattern-evaluation":
            self.validate_pattern_invocation(inv)
        if value["producerStatus"] == "failed":
            self.ok(
                value["producer"] == {
                    "producerId": "bag16-unavailable-producer",
                    "producerVersion": 1,
                    "executionConformance": "not-proven",
                },
                "BAG-16 failed receipt overclaims producer/conformance authority",
            )
            self.ok(value["outputs"] == [] and value["semanticTerminal"] is None and value["failure"] is not None, "BAG-16 failed producer fabricated output")
            self.ok(operation in {"execution-attempt", "pattern-evaluation"} and value["failure"]["context"] == "pattern-test", "BAG-16 failed producer placement drift")
            failure = value["failure"]
            entries = [
                entry for entry in self.taxonomy["entries"]
                if (entry["stage"], entry["classification"])
                == (failure["stage"], failure["classification"])
            ]
            self.ok(len(entries) == 1, "BAG-16 failed producer classification is absent from its taxonomy")
            placements = [
                item for item in entries[0]["placements"]
                if (item["context"], item["scope"])
                == (failure["context"], failure["scope"])
            ]
            self.ok(
                len(placements) == 1
                and placements[0]["consequence"] == {"disposition": "error"}
                and failure["retryability"] == entries[0]["retryability"]
                and failure["semanticEvidence"] == [],
                "BAG-16 failed producer contradicts successor taxonomy placement",
            )
            return
        self.ok(
            value["producer"]["producerId"] == "bag16-deterministic-python"
            and value["producer"]["producerVersion"] == 1
            and value["producer"]["executionConformance"]
            in {"finite-vector-proven", "not-proven"},
            "BAG-16 completed receipt overclaims producer/conformance authority",
        )
        terminal_failure = None
        if operation == "execution-attempt" and isinstance(value["semanticTerminal"], dict):
            terminal_failure = value["semanticTerminal"].get("failure")
            if terminal_failure is None:
                stop_reason = value["semanticTerminal"].get("stopReason")
                if isinstance(stop_reason, dict):
                    terminal_failure = stop_reason.get("failure")
        self.ok(
            len(value["outputs"]) == 1 and value["failure"] == terminal_failure,
            "BAG-16 complete receipt publication/failure drift",
        )
        output = value["outputs"][0]["artifact"]
        self.ok(output["role"] == OUTPUT_ROLES[operation], "BAG-16 receipt published another wrapper role")
        result = self.resolve(output)
        self.validate_result_wrapper(result, value)
        if operation == "execution-attempt":
            self.validate_execution_wrapper(result, value)
        elif operation == "pattern-evaluation":
            self.validate_pattern_operation(result, value)
        elif operation == "corpus-derivation":
            self.validate_corpus_operation(result, value)
        elif operation == "oracle-operand-production":
            self.validate_oracle_operation(result, value)

    def validate_result_wrapper(self, result: dict[str, Any], receipt: dict[str, Any]) -> None:
        operation = receipt["invocation"]["operationKind"]
        identity_field = "resultId"
        expected_domain = RESULT_DOMAINS[OUTPUT_ROLES[operation]]
        self.ok(
            result[identity_field] == digest(expected_domain, without(result, identity_field)),
            "BAG-16 result wrapper identity drift",
        )
        self.ok(
            result["invocationDigest"] == receipt["invocationDigest"],
            "BAG-16 result wrapper names another invocation",
        )
        self.ok(
            receipt["receiptId"] not in {item["digest"] for item in artifact_keys(result)},
            "BAG-16 wrapper points to its producing receipt",
        )

    def validate_pattern(self, result: dict[str, Any]) -> None:
        self.ok(result["resultId"] == digest(DOMAINS["pattern"], without(result, "resultId")), "BAG-16 pattern result identity drift")
        collection = self.resolve(result["collection"])
        self.validate_collection(collection)
        traces = {visit["trace"]["digest"]: self.resolve(visit["trace"]) for visit in collection["visited"]}
        execution_invocation = self.execution_invocation_for_collection(collection)
        attempt = execution_invocation["parameters"]["executionKey"]
        plan, query = self.validate_pattern_roots(
            result["patternSource"], result["patternPlan"], result["patternQuery"],
            attempt["attemptKind"]["observationInputs"][0],
        )
        table = self.resolve(result["sideConditionTable"])
        self.validate_side_condition_table(table)
        self.ok(
            all(
                trace["eventVocabularyDigest"] == plan["eventVocabularyDigest"]
                for trace in traces.values()
            ),
            "BAG-16 pattern query/plan/source/vocabulary roots drift",
        )
        roots = {field: result[field] for field in ("patternSource", "patternPlan", "patternQuery")}
        expected = pattern_result(collection, traces, plan, roots, result["sideConditionTable"], table, search_policy=result["searchPolicy"])
        self.ok(result == expected, "BAG-16 persisted pattern denotation/decision/witness order drift")

    @staticmethod
    def oracle_subject(attempt: dict[str, Any]) -> dict[str, Any]:
        subject = attempt["subject"]
        if subject["kind"] == "baseline":
            return {
                "side": "baseline",
                "definitionDigest": subject["definition"]["digest"],
            }
        return {
            "side": "mutant",
            "baselineDefinitionDigest": subject["baselineDefinition"]["digest"],
            "mutantId": subject["mutantId"],
            "mutantDefinitionDigest": subject["mutantDefinition"]["digest"],
        }

    def validate_oracle_operation(
        self, wrapper: dict[str, Any], receipt: dict[str, Any],
    ) -> None:
        invocation_value = receipt["invocation"]
        parameters = invocation_value["parameters"]
        self.ok(
            wrapper["failure"] is None
            and wrapper["outcome"]["kind"] == "operand"
            and receipt["semanticTerminal"] == wrapper["outcome"],
            "BAG-16 completed oracle operation lacks one operand outcome",
        )
        operand_key_value = wrapper["outcome"]["operand"]
        operand = self.resolve(operand_key_value)
        self.ok(
            operand["operandId"]
            == digest("k-in-k/oracle-operand/v1", without(operand, "operandId")),
            "BAG-16 oracle operand identity drift",
        )
        declaration = self.resolve(operand["declaration"])
        self.ok(
            operand["declaration"] == parameters["declaration"]
            and operand["testInvocationDigest"] == declaration["testInvocationDigest"],
            "BAG-16 oracle operand declaration/test roots drift",
        )
        for field in (
            "compatibilityProfileDigest", "executionProfileDigest", "solverProfileDigest",
        ):
            self.ok(
                operand[field] == declaration[field],
                f"BAG-16 oracle operand {field} drift",
            )
        child_edges = invocation_value["childReceipts"]
        self.ok(len(child_edges) == 1, "BAG-16 oracle operation has surplus child receipts")
        child_receipt = self.resolve(child_edges[0]["receipt"])
        self.validate_receipt(child_receipt)
        projection_kind = parameters["projectionKind"]
        if projection_kind == "execution-pattern":
            self.ok(
                declaration["kind"] == "execution-pattern"
                and child_edges[0]["edgeRole"] == "pattern-evaluation-production"
                and child_receipt["producerStatus"] == "complete",
                "BAG-16 pattern operand lacks its exact completed evaluator child",
            )
            self.ok(
                parameters["patternEvaluationInvocation"] == child_receipt["invocation"]
                and child_receipt["outputs"][0]["artifact"] == parameters["patternEvaluationResult"],
                "BAG-16 pattern operand child invocation/wrapper drift",
            )
            pattern_wrapper_value = self.resolve(parameters["patternEvaluationResult"])
            pattern_value = self.resolve(parameters["patternResult"])
            self.validate_pattern(pattern_value)
            pattern_collection = self.resolve(pattern_value["collection"])
            pattern_attempt = self.execution_invocation_for_collection(
                pattern_collection,
            )["parameters"]["executionKey"]
            expected_subject = self.oracle_subject(pattern_attempt)
            self.ok(
                pattern_wrapper_value["patternResult"] == parameters["patternResult"]
                and pattern_value["collection"] == parameters["collection"],
                "BAG-16 pattern operand wrapper/result/collection drift",
            )
            self.ok(
                parameters["subject"] == pattern_attempt["subject"]
                and operand["subject"] == expected_subject,
                "BAG-16 pattern operand operation/execution subject drift",
            )
            config = declaration["kindConfig"]
            for field in (
                "patternSource", "patternPlan", "patternQuery", "searchPolicy",
            ):
                self.ok(parameters[field] == config[field], f"BAG-16 pattern operand {field} drift")
            self.ok(
                parameters["sideConditionTable"] == pattern_value["sideConditionTable"],
                "BAG-16 pattern operand side-condition authority drift",
            )
            expected_inputs = [
                artifact_edge("declaration", parameters["declaration"]),
                artifact_edge("pattern-evaluation-result", parameters["patternEvaluationResult"]),
                artifact_edge("pattern-result", parameters["patternResult"]),
                artifact_edge("branch-collection", parameters["collection"]),
            ]
            self.ok(invocation_value["inputs"] == expected_inputs, "BAG-16 pattern operand input order drift")
            decision = pattern_value["decision"]
            projection = declaration["projectionSpec"]["projectionId"]
            eligible = decision["kind"] == "match" or (
                decision["kind"] == "no-match" and decision["completeCoverage"]
            )
            if projection == "pattern-outcome-bindings-v1":
                eligible = eligible and decision["completeCoverage"] and parameters["searchPolicy"] == "exhaustive"
            self.ok(eligible, "BAG-16 pattern operand was produced from ineligible coverage")
            self.ok(
                operand["completionEvidence"]
                == {"kind": "pattern-result", "patternResult": parameters["patternResult"]},
                "BAG-16 pattern operand completion evidence drift",
            )
            self.ok(
                operand["normalizedValue"]["patternResult"] == parameters["patternResult"]
                and operand["normalizedValue"]["outcome"] == decision["kind"],
                "BAG-16 pattern operand normalized outcome drift",
            )
            if projection == "pattern-outcome-v1":
                self.ok(
                    operand["normalizedValue"]["bindingTuples"] == [],
                    "BAG-16 outcome-only pattern operand retained bindings",
                )
            self.validate_successor_inline_operand(operand)
            return

        self.ok(
            projection_kind in {"concrete-output", "reachability", "structured-predicate"}
            and declaration["kind"] == projection_kind,
            "BAG-16 finite-row oracle kind/declaration drift",
        )
        if self._bag12_oracle is None:
            from bag12 import OracleVerifier

            self._bag12_oracle = OracleVerifier(self.root, dict(self.api))
        accepted_declaration = declaration
        if projection_kind == "structured-predicate":
            accepted_declarations = [
                value for value in self._bag12_oracle.declarations.values()
                if value["kind"] == declaration["kind"]
                and value["kindConfig"] == declaration["kindConfig"]
                and value["projectionSpec"] == declaration["projectionSpec"]
                and value["comparisonSpec"] == declaration["comparisonSpec"]
            ]
            self.ok(
                bool(accepted_declarations),
                "BAG-16 predicate row lacks accepted BAG-12 kind authority",
            )
            accepted_declaration = accepted_declarations[0]
        self._bag12_oracle.validate_expected_normal_value(
            accepted_declaration, operand["normalizedValue"],
        )
        self.ok(
            child_edges[0]["edgeRole"] == "execution-production"
            and child_receipt["producerStatus"] == "complete"
            and child_receipt["invocation"] == parameters["executionInvocation"]
            and child_receipt["outputs"][0]["artifact"] == parameters["executionResult"],
            "BAG-16 finite-row operand lacks its exact execution child",
        )
        execution_result_value = self.resolve(parameters["executionResult"])
        collection = self.resolve(parameters["collection"])
        self.validate_execution_wrapper(execution_result_value, child_receipt)
        self.ok(
            execution_result_value["branchCollection"] == parameters["collection"],
            "BAG-16 finite-row execution/collection drift",
        )
        attempt = parameters["executionInvocation"]["parameters"]["executionKey"]
        self.ok(
            all(
                declaration[field] == attempt[field]
                for field in (
                    "compatibilityProfileDigest", "executionProfileDigest",
                    "solverProfileDigest",
                )
            ),
            "BAG-16 finite-row declaration/execution profile drift",
        )
        self.ok(
            attempt["attemptKind"]["kind"] == "observed-exhaustive"
            and collection["queryCoupling"] == {"kind": "query-independent"}
            and collection["stopReason"] == {"kind": "search-exhausted"}
            and collection["pendingWork"] == {"discoveredCount": 0}
            and bool(collection["visited"]),
            "BAG-16 finite-row operand bypassed the complete query-neutral gate",
        )
        self.ok(
            all(visit["disposition"]["kind"] in {"normal", "stuck", "semantic-crash"} for visit in collection["visited"]),
            "BAG-16 finite-row operand consumed an incomplete occurrence",
        )
        expected_occurrences = [
            {
                "collection": parameters["collection"],
                "branchKey": visit["branchKey"],
                "traceOccurrence": visit["traceOccurrence"],
            }
            for visit in collection["visited"]
        ]
        self.ok(parameters["occurrences"] == expected_occurrences, "BAG-16 finite-row occurrence join drift")
        expected_subject = self.oracle_subject(attempt)
        self.ok(
            parameters["subject"] == attempt["subject"]
            and operand["subject"] == expected_subject
            and operand["testInvocationDigest"] == attempt["testInvocationDigest"],
            "BAG-16 finite-row operand subject/test drift",
        )
        table_key_value = parameters["finiteTable"]
        table = self.resolve(table_key_value)
        selected_row = parameters["finiteRow"]
        self.ok(selected_row in table["rows"], "BAG-16 invocation finite row is absent from its exact table")
        self.ok(table_key_value["role"] == {
            "concrete-output": "semantic-output-finite-table",
            "reachability": "reachability-conformance-table",
            "structured-predicate": "predicate-conformance-table",
        }[projection_kind], "BAG-16 finite-row parameter names another table role")
        visits = collection["visited"]
        if projection_kind == "concrete-output":
            evidence = operand["completionEvidence"]
            rows = [row for row in table["rows"] if row["rowId"] == evidence["rowId"]]
            self.ok(len(rows) == 1 and len(visits) == 1, "BAG-16 concrete-output row/occurrence cardinality drift")
            row = rows[0]
            self.ok(row == selected_row, "BAG-16 concrete-output invocation selected another finite row")
            self.ok(
                row["rowId"] == digest("k-in-k/semantic-output-finite-row/v1", without(row, "rowId"))
                and table["tableId"] == digest("k-in-k/semantic-output-finite-table/v1", without(table, "tableId")),
                "BAG-16 concrete-output finite authority identity drift",
            )
            disposition = visits[0]["disposition"]
            self.ok(
                row["producerTrace"] == visits[0]["trace"]
                and row["terminal"] == {"kind": disposition["kind"], "artifact": disposition["terminal"]},
                "BAG-16 concrete-output terminal/occurrence join drift",
            )
            self.ok(
                row["declaration"] == operand["declaration"]
                and row["testInvocationDigest"] == operand["testInvocationDigest"]
                and row["subject"] == operand["subject"]
                and operand["normalizedValue"] == {"channels": row["channels"]},
                "BAG-16 concrete-output row roots/projection drift",
            )
            expected_tail = [
                ("semantic-output-finite-table", table_key_value),
                ("row-terminal", disposition["terminal"]),
            ]
        elif projection_kind == "reachability":
            evidence = operand["completionEvidence"]
            rows = [
                row for row in table["rows"]
                if row["query"] == evidence["query"]
                and row["inputVectorDigest"] == evidence["inputVectorDigest"]
            ]
            self.ok(len(rows) == 1, "BAG-16 reachability row selection is ambiguous")
            row = rows[0]
            self.ok(row == selected_row, "BAG-16 reachability invocation selected another finite row")
            terminals: list[dict[str, str]] = []
            for visit in visits:
                disposition = visit["disposition"]
                if disposition["kind"] in {"normal", "stuck"}:
                    terminals.append(disposition["terminal"])
                else:
                    crash = self.resolve(disposition["crash"])
                    terminals.append(crash["terminalState"])
            self.ok(
                row["producerTraces"] == [visit["trace"] for visit in visits]
                and row["terminalStates"] == terminals and row["finiteComplete"] is True,
                "BAG-16 reachability row omitted/reordered a collection occurrence",
            )
            self.ok(
                row["inputVectorDigest"] == digest(
                    "k-in-k/reachability-finite-input/v1",
                    {"terminalStates": terminals, "finiteComplete": True},
                )
                and table["tableId"] == digest("k-in-k/reachability-conformance-table/v1", without(table, "tableId")),
                "BAG-16 reachability finite authority identity drift",
            )
            self.ok(
                row["testInvocationDigest"] == operand["testInvocationDigest"]
                and row["subject"] == operand["subject"]
                and operand["normalizedValue"] == {
                    "status": "reached" if row["witnesses"] else "not-reached",
                    "witnesses": row["witnesses"],
                },
                "BAG-16 reachability row roots/truth drift",
            )
            expected_tail = [
                ("reachability-conformance-table", table_key_value),
                ("reachability-query", row["query"]),
                *[("row-terminal", item) for item in terminals],
            ]
        else:
            evidence = operand["completionEvidence"]
            rows = [
                row for row in table["rows"]
                if row["query"] == evidence["query"] and row["input"] == evidence["input"]
                and row["bindingsDigest"] == evidence["bindingsDigest"]
            ]
            self.ok(len(rows) == 1 and len(visits) == 1, "BAG-16 predicate row/occurrence cardinality drift")
            row = rows[0]
            self.ok(row == selected_row, "BAG-16 predicate invocation selected another finite row")
            disposition = visits[0]["disposition"]
            self.ok(
                disposition["kind"] in {"normal", "stuck"}
                and row["producerTrace"] == visits[0]["trace"]
                and row["input"] == disposition["terminal"],
                "BAG-16 predicate input differs from its occurrence terminal",
            )
            expected_normalized = {
                field: row[field] for field in (
                    "query", "input", "inputProjectionDigest", "bindings",
                    "bindingsDigest", "result",
                )
            }
            self.ok(
                row["testInvocationDigest"] == operand["testInvocationDigest"]
                and row["subject"] == operand["subject"]
                and row["bindingsDigest"] == digest("k-in-k/bindings/v1", row["bindings"])
                and operand["normalizedValue"] == expected_normalized
                and table["tableId"] == digest("k-in-k/predicate-conformance-table/v1", without(table, "tableId")),
                "BAG-16 predicate finite authority roots/projection drift",
            )
            expected_tail = [
                ("predicate-conformance-table", table_key_value),
                ("predicate-query", row["query"]),
                ("predicate-input", row["input"]),
            ]
        expected_inputs = [
            artifact_edge("declaration", parameters["declaration"]),
            artifact_edge("execution-result", parameters["executionResult"]),
            artifact_edge("branch-collection", parameters["collection"]),
            *[artifact_edge(edge, artifact) for edge, artifact in expected_tail],
        ]
        self.ok(invocation_value["inputs"] == expected_inputs, "BAG-16 finite-row input order/cardinality drift")

    def validate_cache(self, record: dict[str, Any]) -> None:
        self.ok(record["recordId"] == digest(DOMAINS["cache"], without(record, "recordId")), "BAG-16 cache record identity drift")
        receipt = self.resolve(record["productionEvidence"]["receipt"])
        result = self.resolve(record["productionEvidence"]["result"])
        self.validate_receipt(receipt)
        self.ok(
            receipt["producerStatus"] == "complete"
            and receipt["outputs"][0]["artifact"] == record["productionEvidence"]["result"]
            and record["completion"]["producerStatus"] == receipt["producerStatus"]
            and record["completion"]["executionConformance"]
            == receipt["producer"]["executionConformance"]
            and record["completion"]["materialClosure"] == "repo-complete",
            "BAG-16 cache producer/result/conformance projection drift",
        )
        self.ok(record["key"] == receipt["invocation"]["parameters"]["executionKey"] and record["keyDigest"] == record["key"]["keyDigest"], "BAG-16 cache request drift")
        self.validate_execution_key(record["key"])
        self.ok(record["terminalRecord"] == result["terminalRecord"] and record["producedArtifacts"] == result["producedArtifacts"], "BAG-16 cache/wrapper projection drift")
        collection = self.resolve(result["branchCollection"])
        kinds = {collection["stopReason"]["kind"], *[item["disposition"]["kind"] for item in collection["visited"]]}
        conformance = record["completion"]["executionConformance"]
        if conformance == "not-proven" or kinds & {"backend-failure"}:
            expected = ("diagnostic-only", "not-reusable")
        elif kinds & {"depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown"}:
            expected = ("exact-bounded-attempt", "exact-bounded-attempt")
        else:
            expected = ("semantic-result", "semantic-result")
        self.ok((record["completion"]["evidenceClass"], record["reuseClass"]) == expected, "BAG-16 cache conformance/terminal precedence drift")

    def validate_component(self, component: dict[str, Any], manifest: dict[str, Any]) -> None:
        self.ok(component["componentResultId"] == digest(DOMAINS["component-result"], without(component, "componentResultId")), "BAG-16 component identity drift")
        slot = manifest["tests"][component["testOrdinal"]]["slots"][component["slotOrdinal"]]
        self.ok(component["slotId"] == slot["slotId"] and component["corpusManifest"]["digest"] == manifest["manifestId"], "BAG-16 component slot/manifest drift")
        if component["kind"] == "skipped":
            forbidden = {"executionResult", "executionReceipt", "collection", "patternResult", "patternEvaluationReceipt"}
            self.ok(not (forbidden & set(component)), "BAG-16 skipped component retained producer evidence")
            self.ok(
                component["testOrdinal"] > component["schedulingReason"]["stoppedAfterTestOrdinal"],
                "BAG-16 skipped component is not in the suffix after its matching test",
            )
            return
        self.validate_execution_key(
            component["executionAttemptKey"], manifest=manifest, slot=slot,
        )
        component_invocation_value = self.resolve(typed(
            "corpus-component-invocation", component["componentInvocationId"],
        ))
        expected_component_invocation = component_invocation(
            manifest, slot, component["executionAttemptKey"],
        )
        self.ok(
            component_invocation_value == expected_component_invocation,
            "BAG-16 component invocation/request/slot roots drift",
        )

        def validate_execution_request(execution_receipt: dict[str, Any]) -> None:
            expected = invocation(
                "execution-attempt", 2,
                {
                    "executionKey": component["executionAttemptKey"],
                    "keyDigest": component["executionAttemptKey"]["keyDigest"],
                },
                _execution_inputs(component["executionAttemptKey"]),
            )
            self.ok(
                execution_receipt["invocation"] == expected,
                "BAG-16 component execution receipt names another exact request",
            )

        def validate_pattern_request(
            pattern_receipt: dict[str, Any], execution_receipt_key: dict[str, str],
        ) -> None:
            parameters = pattern_receipt["invocation"]["parameters"]
            expected = invocation(
                "pattern-evaluation", 1, parameters,
                [
                    ("execution-result", parameters["executionResult"]),
                    ("branch-collection", parameters["collection"]),
                    ("pattern-source", parameters["patternSource"]),
                    ("pattern-plan", parameters["patternPlan"]),
                    ("pattern-query", parameters["patternQuery"]),
                    ("side-condition-conformance-table", parameters["sideConditionTable"]),
                ],
                [("execution-production", execution_receipt_key)],
            )
            self.ok(
                pattern_receipt["invocation"] == expected,
                "BAG-16 component pattern receipt names another exact request/child",
            )

        if component["kind"] == "evaluated":
            execution_receipt = self.resolve(component["executionReceipt"])
            pattern_receipt = self.resolve(component["patternEvaluationReceipt"])
            self.validate_receipt(execution_receipt)
            self.validate_receipt(pattern_receipt)
            validate_execution_request(execution_receipt)
            validate_pattern_request(pattern_receipt, component["executionReceipt"])
            self.ok(execution_receipt["outputs"][0]["artifact"] == component["executionResult"], "BAG-16 component execution pair drift")
            self.ok(pattern_receipt["outputs"][0]["artifact"] == component["patternEvaluationResult"], "BAG-16 component pattern pair drift")
            execution_result_value = self.resolve(component["executionResult"])
            pattern_wrapper_value = self.resolve(component["patternEvaluationResult"])
            self.ok(
                component["executionAttemptKey"] == execution_receipt["invocation"]["parameters"]["executionKey"]
                and component["collection"] == execution_result_value["branchCollection"],
                "BAG-16 evaluated component execution request/collection drift",
            )
            self.ok(
                component["patternEvaluationInvocation"] == pattern_receipt["invocation"]
                and pattern_wrapper_value["patternResult"] == component["patternResult"]
                and pattern_receipt["invocation"]["parameters"]["executionResult"]
                == component["executionResult"]
                and pattern_receipt["invocation"]["parameters"]["collection"]
                == component["collection"],
                "BAG-16 evaluated component pattern invocation/wrapper drift",
            )
            for field in (
                "patternSource", "patternPlan", "patternQuery", "sideConditionTable",
                "searchPolicy",
            ):
                self.ok(
                    pattern_receipt["invocation"]["parameters"][field] == slot[field],
                    f"BAG-16 evaluated component pattern {field} drift",
                )
            self.validate_pattern(self.resolve(component["patternResult"]))
            return
        execution_receipt = self.resolve(component["executionReceipt"])
        self.validate_receipt(execution_receipt)
        validate_execution_request(execution_receipt)
        self.ok(
            execution_receipt["invocation"]["parameters"]["executionKey"]
            == component["executionAttemptKey"],
            "BAG-16 failure component execution request drift",
        )
        if component["kind"] == "execution-failure":
            self.ok(
                execution_receipt["producerStatus"] == "failed"
                and execution_receipt["outputs"] == [],
                "BAG-16 execution-failure component cites a completed producer",
            )
            return
        self.ok(component["kind"] == "pattern-failure", "BAG-16 open component kind")
        self.ok(
            execution_receipt["producerStatus"] == "complete"
            and execution_receipt["outputs"][0]["artifact"] == component["executionResult"],
            "BAG-16 pattern-failure component lacks its completed execution",
        )
        execution_result_value = self.resolve(component["executionResult"])
        self.ok(
            execution_result_value["branchCollection"] == component["collection"],
            "BAG-16 pattern-failure component collection drift",
        )
        pattern_receipt = self.resolve(component["patternEvaluationReceipt"])
        self.validate_receipt(pattern_receipt)
        validate_pattern_request(pattern_receipt, component["executionReceipt"])
        self.ok(
            pattern_receipt["producerStatus"] == "failed"
            and pattern_receipt["invocation"] == component["patternEvaluationInvocation"]
            and pattern_receipt["outputs"] == [],
            "BAG-16 pattern-failure component cites another producer request",
        )
        parameters = pattern_receipt["invocation"]["parameters"]
        self.ok(
            parameters["executionResult"] == component["executionResult"]
            and parameters["collection"] == component["collection"],
            "BAG-16 failed pattern request execution/collection drift",
        )
        for field in (
            "patternSource", "patternPlan", "patternQuery", "sideConditionTable",
            "searchPolicy",
        ):
            self.ok(parameters[field] == slot[field], f"BAG-16 failed pattern {field} drift")

    def validate_corpus(self, result: dict[str, Any]) -> None:
        self.ok(result["corpusResultId"] == digest(DOMAINS["corpus-result"], without(result, "corpusResultId")), "BAG-16 corpus result identity drift")
        manifest = self.resolve(result["corpusManifest"])
        self.validate_manifest(manifest)
        components = [self.resolve(item) for item in result["components"]]
        self.ok([(item["testOrdinal"], item["slotOrdinal"]) for item in components] == [(test["testOrdinal"], slot["slotOrdinal"]) for test in manifest["tests"] for slot in test["slots"]], "BAG-16 corpus components are not exact manifest order")
        for component in components:
            self.validate_component(component, manifest)
        scheduling = manifest["aggregation"]["schedulingPolicy"]
        if scheduling == "full":
            self.ok(
                all(component["kind"] != "skipped" for component in components),
                "BAG-16 full scheduling contains a skipped component",
            )
        else:
            matches = [
                item["testOrdinal"] for item in result["testResults"]
                if item["decision"]["kind"] == "match"
            ]
            self.ok(bool(matches), "BAG-16 stopped scheduling has no matching test")
            stopped_after = min(matches)
            for component in components:
                if component["testOrdinal"] <= stopped_after:
                    self.ok(component["kind"] != "skipped", "BAG-16 stopped test retained unevaluated declarations")
                else:
                    self.ok(
                        component["kind"] == "skipped"
                        and component["schedulingReason"]["stoppedAfterTestOrdinal"] == stopped_after,
                        "BAG-16 stop-after-match suffix is not exactly skipped",
                    )
        expected = corpus_result_v2(manifest, components, self.assets)
        self.ok(result == expected, "BAG-16 corpus fold/cause selection/coverage drift")

    def validate_registry(self, closure: dict[str, Any]) -> None:
        registry = closure["registry"]
        self.ok(registry["registryId"] == digest("k-in-k/replay-version-registry/v2", without(registry, "registryId")), "BAG-16 replay registry identity drift")
        result_key = closure["result"]
        reached, operations, seed = _reachable(self.assets, result_key, closure["receipt"])
        schemas = _schema_names_for_assets(self.root, self.role_registry, self.assets, reached, seed)
        expected = build_replay_registry(self.root, schemas, operations)
        self.ok(registry == expected, "BAG-16 recursive schema/operation registry set drift")

    def validate_successor_inline_operand(self, operand: dict[str, Any]) -> None:
        self.ok(
            operand["operandId"]
            == digest("k-in-k/oracle-operand/v1", without(operand, "operandId")),
            "BAG-16 successor inline operand identity drift",
        )
        declaration = self.resolve(operand["declaration"])
        normalized = operand["normalizedValue"]
        result_key_value = normalized["patternResult"]
        result = self.resolve(result_key_value)
        pattern_role = next(
            item for item in self.role_registry["specs"]
            if item["role"] == "pattern-result"
        )
        arm = select_structured_version(pattern_role, result)
        self.ok(
            arm["schemaVersion"] == 2 and arm["digestDomain"] == DOMAINS["pattern"],
            "BAG-16 successor inline operand bypassed pattern-result v2 dispatch",
        )
        self.validate_pattern(result)
        config = declaration["kindConfig"]
        self.ok(
            declaration["kind"] == "execution-pattern"
            and operand["testInvocationDigest"] == declaration["testInvocationDigest"]
            and operand["completionEvidence"]
            == {"kind": "pattern-result", "patternResult": result_key_value}
            and all(result[field] == config[field] for field in (
                "patternSource", "patternPlan", "patternQuery", "searchPolicy",
            )),
            "BAG-16 successor inline operand declaration/query provenance drift",
        )
        projection = declaration["projectionSpec"]["projectionId"]
        expected = {
            "patternResult": result_key_value,
            "outcome": result["decision"]["kind"], "bindingTuples": [],
        }
        if projection == "pattern-outcome-bindings-v1":
            self.ok(
                result["searchPolicy"] == "exhaustive"
                and result["decision"]["kind"] in {"match", "no-match"}
                and result["decision"]["completeCoverage"] is True,
                "BAG-16 successor inline bindings bypassed complete exhaustive coverage",
            )
            expected["bindingTuples"] = [
                [
                    {
                        "name": binding["name"], "sort": binding["term"]["sort"],
                        "value": deepcopy(binding["term"]),
                    }
                    for binding in witness["bindings"]
                ]
                for witness in result["witnesses"]
            ]
        else:
            self.ok(
                projection == "pattern-outcome-v1"
                and (
                    result["decision"]["kind"] == "match"
                    or (
                        result["decision"]["kind"] == "no-match"
                        and result["decision"]["completeCoverage"] is True
                    )
                ),
                "BAG-16 successor inline outcome bypassed its coverage gate",
            )
        self.ok(
            normalized == expected,
            "BAG-16 successor inline normalized value is not kind-specifically derived",
        )

    def validate_inline_expectations(self) -> None:
        # Re-run every accepted BAG-12 portable built-in pair while requiring
        # every declaration, operand, and expected-value provenance key to be
        # resolvable through the embedded successor catalog.
        from bag12 import OracleVerifier

        oracle_api = dict(self.api)
        if not callable(oracle_api.get("validate_pattern_result_semantics")):
            def validate_legacy_pattern_result(
                result: dict[str, Any], traces: dict[str, dict[str, Any]],
                _taxonomy: dict[str, Any],
            ) -> None:
                """Re-derive the complete denotation used by BAG-12 inline cases."""
                from refresh_fixture_ids import bag11_fixture_witnesses

                self.ok(
                    result["schemaVersion"] == 1
                    and result["resultId"]
                    == digest("k-in-k/pattern-result/v1", without(result, "resultId")),
                    "BAG-16 legacy inline pattern identity drift",
                )
                plan = oracle.pattern_plans[result["inputs"]["patternPlan"]["digest"]]
                self.ok(
                    plan["sideCondition"] is None and result["failures"] == [],
                    "BAG-16 local legacy inline checker exceeded its complete finite arm",
                )
                expected_witnesses: list[dict[str, Any]] = []
                paths = result["pathResults"]
                self.ok(
                    [path["pathOrdinal"] for path in paths] == list(range(len(paths))),
                    "BAG-16 legacy inline pattern path order drift",
                )
                for path in paths:
                    trace = traces.get(path["traceDigest"])
                    self.ok(
                        trace is not None
                        and path["traceDigest"] == digest("k-in-k/event-trace/v1", trace)
                        and trace["testId"] == result["testId"]
                        and trace["pathIdentityDigest"] == path["pathIdentityDigest"]
                        and trace["pathKey"] == path["pathKey"]
                        and trace["complete"] == path["completeCoverage"]
                        and trace["stopReason"] == path["executionStopReason"]
                        and trace["executionTerminal"] == path["executionTerminal"]
                        and path["failures"] == [],
                        "BAG-16 legacy inline pattern path/trace provenance drift",
                    )
                    derived = bag11_fixture_witnesses(plan, trace, path)
                    expected_status = "match" if derived else "no-match"
                    self.ok(
                        trace["complete"] and path["status"] == expected_status,
                        "BAG-16 legacy inline path differs from complete finite denotation",
                    )
                    expected_witnesses.extend(derived)
                expected_witnesses.sort(key=lambda witness: (
                    witness.get("pathKey", ""), tuple(witness["eventIndices"]),
                    digest("k-in-k/bindings/v1", witness["bindings"]), witness["armOrdinal"],
                ))
                expected_outcome = "match" if expected_witnesses else "no-match"
                self.ok(
                    result["witnesses"] == expected_witnesses
                    and result["outcome"] == expected_outcome
                    and result["completeCoverage"] is True
                    and result["inputs"]["searchPolicy"] == "exhaustive",
                    "BAG-16 legacy inline result differs from complete finite denotation",
                )

            oracle_api["validate_pattern_result_semantics"] = validate_legacy_pattern_result
        oracle = OracleVerifier(self.root, oracle_api)
        vectors = read_json(self.root / "vectors" / "oracle-semantics-vectors.json")
        cases = vectors["inlineExpectationCases"]
        expected_pairs = {
            (item["kind"], item["projectionId"], item["comparatorId"])
            for item in vectors["registry"]
        }
        actual_pairs = {
            (item["kind"], item["projectionId"], item["comparatorId"])
            for item in cases
        }
        self.ok(
            actual_pairs == expected_pairs and len(cases) == len(expected_pairs),
            "BAG-16 inline rerun does not cover every BAG-12 built-in pair exactly once",
        )
        by_kind: dict[str, dict[str, Any]] = {}
        for case in cases:
            declaration_key_value = case["declaration"]
            operand_key_value = case["baselineOperand"]
            self.ok(
                (declaration_key_value["role"], declaration_key_value["digest"]) in self.entries
                and (operand_key_value["role"], operand_key_value["digest"]) in self.entries,
                f"BAG-16 inline {case['kind']} roots are absent from the v2 catalog",
            )
            declaration = oracle.declarations[declaration_key_value["digest"]]
            operand = oracle.operands[operand_key_value["digest"]]
            expected_side = case["expectedSide"]
            for artifact in artifact_keys(expected_side):
                self.ok(
                    (artifact["role"], artifact["digest"]) in self.entries,
                    f"BAG-16 inline {case['kind']} provenance is absent from the v2 catalog",
                )
            self.ok(
                operand["declaration"] == declaration_key_value
                and operand["subject"]["side"] == "baseline"
                and expected_side["kind"] == declaration["kind"],
                f"BAG-16 inline {case['kind']} declaration/operand/side drift",
            )
            oracle.validate_expected_normal_value(
                declaration, expected_side["normalizedValue"],
            )
            self.ok(
                oracle.comparator(
                    declaration, expected_side["normalizedValue"],
                    operand["normalizedValue"],
                ) == "agree",
                f"BAG-16 inline {case['kind']} positive did not agree",
            )
            by_kind.setdefault(case["kind"], case)
        self.ok(
            set(by_kind) == {
                "exit-stop", "final-result", "concrete-output", "reachability",
                "execution-pattern", "structured-predicate",
            },
            "BAG-16 inline rerun omits an oracle kind",
        )

        # Re-run collection-backed successor values through the pattern-result
        # v2 dispatch arm rather than treating BAG-12's v1 result shape as the
        # only execution-pattern inline authority.
        pattern_role = next(
            item for item in self.role_registry["specs"]
            if item["role"] == "pattern-result"
        )
        for evidence_name in (
            "patternOperand", "patternBindingsOperand",
            "falseCoverageOutcomeOperand",
        ):
            successor_operand = self.resolve(self.vector["evidence"][evidence_name])
            self.validate_successor_inline_operand(successor_operand)
            successor_declaration = self.resolve(successor_operand["declaration"])
            normalized = successor_operand["normalizedValue"]
            result_key_value = normalized["patternResult"]
            result = self.resolve(result_key_value)
            arm = select_structured_version(pattern_role, result)
            self.ok(
                arm["schemaVersion"] == 2
                and arm["digestDomain"] == DOMAINS["pattern"],
                "BAG-16 collection-backed inline value bypassed pattern-result v2 dispatch",
            )
            self.validate_pattern(result)
            config = successor_declaration["kindConfig"]
            projection = successor_declaration["projectionSpec"]["projectionId"]
            expected_normalized = {
                "patternResult": result_key_value,
                "outcome": result["decision"]["kind"],
                "bindingTuples": [],
            }
            if projection == "pattern-outcome-bindings-v1":
                self.ok(
                    result["searchPolicy"] == "exhaustive"
                    and result["decision"]["completeCoverage"] is True,
                    "BAG-16 collection-backed inline bindings bypassed its coverage gate",
                )
                expected_normalized["bindingTuples"] = [
                    [
                        {
                            "name": binding["name"],
                            "sort": binding["term"]["sort"],
                            "value": deepcopy(binding["term"]),
                        }
                        for binding in witness["bindings"]
                    ]
                    for witness in result["witnesses"]
                ]
            else:
                self.ok(
                    projection == "pattern-outcome-v1"
                    and (
                        result["decision"]["kind"] == "match"
                        or result["decision"]["completeCoverage"] is True
                    ),
                    "BAG-16 collection-backed inline outcome bypassed its eligibility gate",
                )
            self.ok(
                successor_declaration["kind"] == "execution-pattern"
                and successor_declaration["projectionSpec"]["mode"] == "portable-built-in"
                and all(result[field] == config[field] for field in (
                    "patternSource", "patternPlan", "patternQuery", "searchPolicy",
                ))
                and result["decision"]["kind"] == "match"
                and normalized == expected_normalized,
                "BAG-16 collection-backed inline outcome is self-asserted or cross-declaration",
            )
        for kind, case in by_kind.items():
            declaration = oracle.declarations[case["declaration"]["digest"]]
            bad = deepcopy(case["expectedSide"]["normalizedValue"])
            if kind == "exit-stop":
                bad["exitCode"] = 0 if declaration["kindConfig"]["exitCodeMode"] == "none" else None
            elif kind == "final-result":
                bad["terminalState"]["digest"] = "f" * 64
            elif kind == "concrete-output":
                bad["channels"][0]["contentSha256"] = "f" * 64
            elif kind == "reachability":
                if bad["witnesses"]:
                    bad["witnesses"][0]["digest"] = "f" * 64
                else:
                    bad["witnesses"].append(typed("reachability-witness", "f" * 64))
            elif kind == "execution-pattern":
                bad["patternResult"]["digest"] = "f" * 64
            else:
                bad["inputProjectionDigest"] = "f" * 64
            self.expect_rejection(
                lambda value=bad, declaration_value=declaration: oracle.validate_expected_normal_value(
                    declaration_value, value,
                ),
                f"inline-wrong-provenance-{kind}",
            )

    def validate_closure(self, closure: dict[str, Any]) -> None:
        self.ok(closure["closureId"] == digest(DOMAINS["closure"], without(closure, "closureId")), "BAG-16 closure root identity drift")
        self.ok(closure["artifactRoleSpecs"] == self.role_registry and closure["artifactCatalog"] == self.catalog, "BAG-16 closure resolver authority drift")
        receipt = self.resolve(closure["receipt"])
        self.validate_receipt(receipt)
        if receipt["producerStatus"] == "complete":
            self.ok(closure["result"] == receipt["outputs"][0]["artifact"], "BAG-16 closure result/receipt drift")
            self.ok(closure["rootKind"] == closure["result"]["role"], "BAG-16 closure root kind/result role drift")
        else:
            self.ok(
                closure["result"] is None
                and closure["rootKind"]
                == OUTPUT_ROLES[receipt["invocation"]["operationKind"]],
                "BAG-16 failed root result/operation kind drift",
            )
        expected_caches: list[dict[str, str]] = []
        reached, _, _ = _reachable(self.assets, closure["result"], closure["receipt"])
        execution_receipts = [self.assets[item] for item in reached if item[0] == "operation-receipt" and self.assets[item]["invocation"]["operationKind"] == "execution-attempt" and self.assets[item]["producerStatus"] == "complete"]
        for execution_receipt in execution_receipts:
            matches = [
                typed("cache-record", identity) for (role, identity), value in self.assets.items()
                if role == "cache-record" and value.get("schemaVersion") == 2
                and value["productionEvidence"]["receipt"]["digest"] == execution_receipt["receiptId"]
            ]
            self.ok(len(matches) == 1, "BAG-16 completed execution lacks one exact cache record")
            expected_caches.extend(matches)
        self.ok(closure["cacheRecords"] == unique_artifacts(expected_caches), "BAG-16 closure cache projection drift")
        for cache_key_value in closure["cacheRecords"]:
            self.validate_cache(self.resolve(cache_key_value))
        self.validate_registry(closure)

    def expect_rejection(self, callback: Callable[[], None], message: str) -> None:
        try:
            callback()
        except (AssertionError, KeyError, ValueError, TypeError):
            self.ok(True, message)
        else:
            raise AssertionError(f"BAG-16 adversary survived: {message}")

    def adversaries(self) -> None:
        collection = self.resolve(self.vector["evidence"]["twoBranchCollection"])
        pattern = self.resolve(self.vector["evidence"]["twoBranchPattern"])
        diagnostic = self.resolve(self.vector["evidence"]["diagnosticCache"])
        corpus_closure = read_json(self.fixtures / "bag16-closure-corpus.json")
        corpus_wrapper = self.resolve(corpus_closure["result"])
        corpus_result = self.resolve(corpus_wrapper["corpusResult"])
        failure_corpus_result = self.resolve(
            self.vector["evidence"]["failureCorpusResult"],
        )
        corpus_manifest = self.resolve(corpus_result["corpusManifest"])
        components = [self.resolve(item) for item in corpus_result["components"]]
        main_cache = self.resolve(corpus_closure["cacheRecords"][0])
        main_execution_result = self.resolve(main_cache["productionEvidence"]["result"])
        main_execution_receipt = self.resolve(main_cache["productionEvidence"]["receipt"])
        empty_closure = read_json(self.fixtures / "bag16-closure-empty-execution.json")
        two_execution_closure = read_json(
            self.fixtures / "bag16-closure-corpus-two-execution.json",
        )
        empty_result = self.resolve(empty_closure["result"])
        empty_collection = self.resolve(empty_result["branchCollection"])
        failed_execution_receipt = self.resolve(
            read_json(self.fixtures / "bag16-closure-failed-execution.json")["receipt"],
        )
        existential_pattern = self.resolve(self.vector["evidence"]["existentialPattern"])
        existential_collection = self.resolve(existential_pattern["collection"])
        pattern_receipt = next(
            value for value in self.receipts.values()
            if value["invocation"]["operationKind"] == "pattern-evaluation"
            and value["producerStatus"] == "complete"
        )
        pattern_wrapper = self.resolve(pattern_receipt["outputs"][0]["artifact"])
        old_trace = read_json(self.fixtures / "bag12-baseline-event-trace.json")
        old_trace_key = typed("event-trace", digest("k-in-k/event-trace/v1", old_trace))
        probes: dict[str, Callable[[bool], None]] = {}

        def refreshed(value: dict[str, Any], field: str, domain: str, refresh: bool) -> dict[str, Any]:
            if refresh:
                identify(value, field, domain)
            return value

        def receipt_for_operand(operand_key_value: dict[str, str]) -> dict[str, Any]:
            matches = []
            for receipt_value in self.receipts.values():
                if (
                    receipt_value["producerStatus"] != "complete"
                    or receipt_value["invocation"]["operationKind"]
                    != "oracle-operand-production"
                ):
                    continue
                wrapper_value = self.resolve(receipt_value["outputs"][0]["artifact"])
                if wrapper_value["outcome"].get("operand") == operand_key_value:
                    matches.append(receipt_value)
            self.ok(len(matches) == 1, "BAG-16 oracle operand has no unique receipt")
            return matches[0]

        concrete_receipt = receipt_for_operand(
            self.vector["evidence"]["concreteOutputOperand"],
        )
        reach_receipt = receipt_for_operand(
            self.vector["evidence"]["reachabilityOperand"],
        )
        predicate_receipt = receipt_for_operand(
            self.vector["evidence"]["predicateOperand"],
        )
        false_coverage_receipt = receipt_for_operand(
            self.vector["evidence"]["falseCoverageOutcomeOperand"],
        )
        bindings_receipt = receipt_for_operand(
            self.vector["evidence"]["patternBindingsOperand"],
        )

        def temporarily_register(
            values: list[tuple[dict[str, str], dict[str, Any]]],
            callback: Callable[[], None],
        ) -> None:
            saved_assets: dict[tuple[str, str], Any | None] = {}
            saved_entries: dict[tuple[str, str], Any | None] = {}
            for artifact, value in values:
                identity = (artifact["role"], artifact["digest"])
                saved_assets[identity] = self.assets.get(identity)
                saved_entries[identity] = self.entries.get(identity)
                self.assets[identity] = value
                self.entries[identity] = {
                    "role": artifact["role"], "digest": artifact["digest"],
                }
            try:
                callback()
            finally:
                for identity, previous in saved_assets.items():
                    if previous is None:
                        self.assets.pop(identity, None)
                    else:
                        self.assets[identity] = previous
                for identity, previous in saved_entries.items():
                    if previous is None:
                        self.entries.pop(identity, None)
                    else:
                        self.entries[identity] = previous

        def key_probe(
            base: dict[str, Any], change: Callable[[dict[str, Any]], None],
            *, manifest: dict[str, Any] | None = None,
            slot: dict[str, Any] | None = None,
        ) -> Callable[[bool], None]:
            def check(refresh: bool) -> None:
                bad = deepcopy(base)
                change(bad)
                refreshed(bad, "keyDigest", DOMAINS["execution-key"], refresh)
                self.validate_execution_key(bad, manifest=manifest, slot=slot)
            return check

        main_key = main_execution_receipt["invocation"]["parameters"]["executionKey"]
        main_slot = corpus_manifest["tests"][0]["slots"][0]
        empty_test_digest = self.resolve(empty_closure["receipt"])["invocation"]["parameters"]["executionKey"]["testInvocationDigest"]
        probes["execution-key-wrong-test"] = key_probe(
            main_key,
            lambda value: value.__setitem__("testInvocationDigest", empty_test_digest),
            manifest=corpus_manifest, slot=main_slot,
        )
        probes["execution-key-wrong-subject"] = key_probe(
            main_key,
            lambda value: value["subject"]["definition"].__setitem__("digest", "f" * 64),
            manifest=corpus_manifest, slot=main_slot,
        )
        probes["exhaustive-key-query-pollution"] = key_probe(
            main_key,
            lambda value: value["attemptKind"].__setitem__(
                "patternQuery", deepcopy(main_slot["patternQuery"]),
            ),
            manifest=corpus_manifest, slot=main_slot,
        )
        existential_key = self.resolve(
            read_json(self.fixtures / "bag16-closure-existential-execution.json")["receipt"],
        )["invocation"]["parameters"]["executionKey"]
        probes["existential-key-query-omitted"] = key_probe(
            existential_key,
            lambda value: value["attemptKind"].pop("patternQuery"),
        )
        probes["exhaustive-slot-query-coupled"] = key_probe(
            main_key,
            lambda value: value.__setitem__(
                "attemptKind", deepcopy(existential_key["attemptKind"]),
            ),
            manifest=corpus_manifest, slot=main_slot,
        )
        mutation_observation_key = next(
            typed("observation-manifest", identity)
            for (role, identity), value in self.assets.items()
            if role == "observation-manifest"
            and value["inputDefinitionDigest"]
            != main_key["subject"]["definition"]["digest"]
        )
        probes["execution-key-observation-subject-drift"] = key_probe(
            main_key,
            lambda value: value["attemptKind"].__setitem__(
                "observationInputs", [mutation_observation_key],
            ),
        )

        def observation_output_drift(refresh: bool) -> None:
            observation_key = main_key["attemptKind"]["observationInputs"][0]
            bad_observation = deepcopy(self.resolve(observation_key))
            bad_observation["outputDefinitionDigest"] = "f" * 64
            refreshed(
                bad_observation, "manifestId",
                "k-in-k/observation-manifest/v1", refresh,
            )
            bad_observation_key = typed(
                "observation-manifest", bad_observation["manifestId"],
            )
            bad_key = deepcopy(main_key)
            bad_key["attemptKind"]["observationInputs"] = [bad_observation_key]
            refreshed(bad_key, "keyDigest", DOMAINS["execution-key"], refresh)
            temporarily_register(
                [(bad_observation_key, bad_observation)],
                lambda: self.validate_execution_key(bad_key),
            )

        probes["execution-key-observation-output-drift"] = observation_output_drift
        probes["execution-key-lowering-profile-drift"] = key_probe(
            main_key,
            lambda value: value.__setitem__("loweringProfileDigest", "f" * 64),
        )
        probes["execution-key-execution-profile-drift"] = key_probe(
            main_key,
            lambda value: value.__setitem__("executionProfileDigest", "f" * 64),
        )
        probes["execution-key-solver-profile-drift"] = key_probe(
            main_key,
            lambda value: value.__setitem__("solverProfileDigest", "f" * 64),
        )

        def isolation_policy_drift(value: dict[str, Any]) -> None:
            value["isolationPolicy"]["observerState"] = "fresh-per-mutant"
            identify(
                value["isolationPolicy"], "isolationPolicyDigest",
                "k-in-k/isolation-policy/v1",
            )

        probes["execution-key-isolation-policy-drift"] = key_probe(
            main_key, isolation_policy_drift,
        )

        def unresolved_subject(refresh: bool) -> None:
            observation_key = main_key["attemptKind"]["observationInputs"][0]
            bad_observation = deepcopy(self.resolve(observation_key))
            bad_observation["inputDefinitionDigest"] = "f" * 64
            bad_observation["outputDefinitionDigest"] = "f" * 64
            refreshed(
                bad_observation, "manifestId",
                "k-in-k/observation-manifest/v1", refresh,
            )
            bad_observation_key = typed(
                "observation-manifest", bad_observation["manifestId"],
            )
            bad_key = deepcopy(main_key)
            bad_key["subject"]["definition"]["digest"] = "f" * 64
            bad_key["attemptKind"]["observationInputs"] = [bad_observation_key]
            refreshed(bad_key, "keyDigest", DOMAINS["execution-key"], refresh)
            temporarily_register(
                [(bad_observation_key, bad_observation)],
                lambda: self.validate_execution_key(bad_key),
            )

        probes["execution-key-subject-catalog-unresolved"] = unresolved_subject

        def unresolved_test_program(refresh: bool) -> None:
            base_invocation = self.resolve(typed(
                "execution-test-invocation", main_key["testInvocationDigest"],
            ))
            bad_invocation = deepcopy(base_invocation)
            bad_invocation["program"] = typed("program", "f" * 64)
            refreshed(
                bad_invocation, "testInvocationDigest",
                DOMAINS["execution-test"], refresh,
            )
            bad_invocation_key = typed(
                "execution-test-invocation",
                bad_invocation["testInvocationDigest"],
            )
            bad_key = deepcopy(main_key)
            bad_key["testInvocationDigest"] = bad_invocation["testInvocationDigest"]
            refreshed(bad_key, "keyDigest", DOMAINS["execution-key"], refresh)
            temporarily_register(
                [(bad_invocation_key, bad_invocation)],
                lambda: self.validate_execution_key(bad_key),
            )

        probes["test-invocation-program-unresolved"] = unresolved_test_program

        def unknown_plan_constructor(refresh: bool) -> None:
            bad_plan = deepcopy(self.resolve(main_slot["patternPlan"]))
            bad_plan["arms"][0]["atoms"][0]["constructor"] = "DefinitelyUnknownConstructor"
            refreshed(
                bad_plan, "patternPlanDigest", "k-in-k/pattern-plan/v1", refresh,
            )
            bad_plan_key = typed("pattern-plan", bad_plan["patternPlanDigest"])
            bad_query = deepcopy(self.resolve(main_slot["patternQuery"]))
            bad_query["patternPlan"] = bad_plan_key
            refreshed(
                bad_query, "queryId", "k-in-k/pattern-query/v1", refresh,
            )
            bad_query_key = typed("pattern-query", bad_query["queryId"])
            temporarily_register(
                [(bad_plan_key, bad_plan), (bad_query_key, bad_query)],
                lambda: self.validate_pattern_roots(
                    main_slot["patternSource"], bad_plan_key, bad_query_key,
                    main_key["attemptKind"]["observationInputs"][0],
                ),
            )

        probes["pattern-plan-unknown-constructor"] = unknown_plan_constructor

        def unresolved_pattern_source(refresh: bool) -> None:
            bad_source = typed("pattern-source", "f" * 64)
            bad_query = deepcopy(self.resolve(main_slot["patternQuery"]))
            bad_query["patternSource"] = bad_source
            refreshed(
                bad_query, "queryId", "k-in-k/pattern-query/v1", refresh,
            )
            bad_query_key = typed("pattern-query", bad_query["queryId"])
            temporarily_register(
                [(bad_query_key, bad_query)],
                lambda: self.validate_pattern_roots(
                    bad_source, main_slot["patternPlan"], bad_query_key,
                    main_key["attemptKind"]["observationInputs"][0],
                ),
            )

        probes["pattern-source-unresolved"] = unresolved_pattern_source

        def unknown_trace_constructor(refresh: bool) -> None:
            bad = deepcopy(main_trace)
            bad["events"][0]["constructor"] = "DefinitelyUnknownConstructor"
            refreshed(bad, "traceId", DOMAINS["trace"], refresh)
            self.validate_trace(bad)
            self.validate_trace_execution_relation(
                bad, collection["visited"][0]["disposition"], main_attempt,
            )

        probes["trace-event-unknown-constructor"] = unknown_trace_constructor

        def trace_provenance_drift(refresh: bool) -> None:
            bad = deepcopy(main_trace)
            bad["events"][0]["origin"]["emittingSentence"]["module"] = "INVENTED"
            refreshed(bad, "traceId", DOMAINS["trace"], refresh)
            self.validate_trace(bad)
            self.validate_trace_execution_relation(
                bad, collection["visited"][0]["disposition"], main_attempt,
            )

        probes["trace-emitting-provenance-drift"] = trace_provenance_drift

        def trace_path_sort_drift(refresh: bool) -> None:
            bad = deepcopy(main_trace)
            bad["pathPredicate"] = {
                "encoding": "portable-term-v1", "sort": "Int",
                "node": {"kind": "token", "text": "1"},
            }
            refreshed(bad, "traceId", DOMAINS["trace"], refresh)
            self.validate_trace(bad)
            self.validate_trace_execution_relation(
                bad, collection["visited"][0]["disposition"], main_attempt,
            )

        probes["trace-path-predicate-sort-drift"] = trace_path_sort_drift

        def terminal_term_sort_drift(refresh: bool) -> None:
            terminal_key = collection["visited"][0]["disposition"]["terminal"]
            bad_terminal = deepcopy(self.resolve(terminal_key))
            bad_terminal["value"] = {
                "encoding": "portable-term-v1", "sort": "K",
                "node": {
                    "kind": "rewrite",
                    "left": {
                        "encoding": "portable-term-v1", "sort": "Int",
                        "node": {"kind": "token", "text": "1"},
                    },
                    "right": {
                        "encoding": "portable-term-v1", "sort": "Bool",
                        "node": {"kind": "token", "text": "true"},
                    },
                },
            }
            refreshed(
                bad_terminal, "terminalStateDigest",
                "k-in-k/terminal-state/v1", refresh,
            )
            bad_terminal_key = typed(
                "terminal-state", bad_terminal["terminalStateDigest"],
            )
            temporarily_register(
                [(bad_terminal_key, bad_terminal)],
                lambda: self.validate_trace_execution_relation(
                    main_trace,
                    {"kind": "normal", "terminal": bad_terminal_key},
                    main_attempt,
                ),
            )

        probes["terminal-term-sort-drift"] = terminal_term_sort_drift

        def duplicate_side_condition_key(refresh: bool) -> None:
            table = deepcopy(self.resolve(main_slot["sideConditionTable"]))
            duplicate = deepcopy(table["rows"][0])
            duplicate["result"] = (
                "false" if duplicate["result"] != "false" else "true"
            )
            table["rows"].insert(1, duplicate)
            refreshed(
                table, "tableDigest",
                "k-in-k/side-condition-conformance-table/v1", refresh,
            )
            self.validate_side_condition_table(table)

        probes["side-condition-table-duplicate-key"] = duplicate_side_condition_key

        def mutated_operation_graph(
            base_receipt: dict[str, Any], refresh: bool,
            change: Callable[[dict[str, Any]], None],
        ) -> None:
            bad_invocation = deepcopy(base_receipt["invocation"])
            change(bad_invocation)
            refreshed(bad_invocation, "invocationDigest", DOMAINS["invocation"], refresh)
            base_wrapper = self.resolve(base_receipt["outputs"][0]["artifact"])
            output_role = base_receipt["outputs"][0]["artifact"]["role"]
            bad_wrapper = deepcopy(base_wrapper)
            bad_wrapper["invocationDigest"] = bad_invocation["invocationDigest"]
            refreshed(
                bad_wrapper, "resultId", RESULT_DOMAINS[output_role], refresh,
            )
            bad_wrapper_key = typed(output_role, bad_wrapper["resultId"])
            bad_receipt = deepcopy(base_receipt)
            bad_receipt["invocation"] = bad_invocation
            bad_receipt["invocationDigest"] = bad_invocation["invocationDigest"]
            bad_receipt["outputs"][0]["artifact"] = bad_wrapper_key
            refreshed(bad_receipt, "receiptId", DOMAINS["receipt"], refresh)
            temporarily_register(
                [(bad_wrapper_key, bad_wrapper)],
                lambda: self.validate_receipt(bad_receipt),
            )

        pattern_operation_receipt = self.resolve(
            read_json(self.fixtures / "bag16-closure-pattern-evaluation.json")["receipt"],
        )
        probes["pattern-operation-wrong-execution-result"] = lambda refresh: mutated_operation_graph(
            pattern_operation_receipt, refresh,
            lambda inv: (
                inv["parameters"].__setitem__(
                    "executionResult", deepcopy(empty_closure["result"]),
                ),
                inv["inputs"][0].__setitem__(
                    "artifact", deepcopy(empty_closure["result"]),
                ),
            ),
        )
        probes["pattern-operation-wrong-query"] = lambda refresh: mutated_operation_graph(
            pattern_operation_receipt, refresh,
            lambda inv: (
                inv["parameters"].__setitem__(
                    "patternQuery", deepcopy(
                        self.resolve(self.vector["evidence"]["indeterminatePattern"])["patternQuery"],
                    ),
                ),
                inv["inputs"][4].__setitem__(
                    "artifact", deepcopy(
                        self.resolve(self.vector["evidence"]["indeterminatePattern"])["patternQuery"],
                    ),
                ),
            ),
        )
        probes["pattern-operation-wrong-policy"] = lambda refresh: mutated_operation_graph(
            pattern_operation_receipt, refresh,
            lambda inv: inv["parameters"].__setitem__("searchPolicy", "existential-first"),
        )
        probes["corpus-operation-child-reordered"] = lambda refresh: mutated_operation_graph(
            self.resolve(corpus_closure["receipt"]), refresh,
            lambda inv: inv.__setitem__(
                "childReceipts", list(reversed(inv["childReceipts"])),
            ),
        )

        def mutated_oracle_graph(
            base_receipt: dict[str, Any], refresh: bool,
            change_invocation: Callable[[dict[str, Any], dict[str, str]], None],
            *, operand_value: dict[str, Any] | None = None,
            extra_assets: list[tuple[dict[str, str], dict[str, Any]]] | None = None,
            enclosing_closure: dict[str, Any] | None = None,
        ) -> None:
            base_wrapper = self.resolve(base_receipt["outputs"][0]["artifact"])
            base_operand = self.resolve(base_wrapper["outcome"]["operand"])
            bad_operand = deepcopy(base_operand if operand_value is None else operand_value)
            if refresh and operand_value is not None:
                identify(bad_operand, "operandId", "k-in-k/oracle-operand/v1")
            bad_operand_key = typed("oracle-operand", bad_operand["operandId"])
            bad_invocation = deepcopy(base_receipt["invocation"])
            change_invocation(bad_invocation, bad_operand_key)
            refreshed(
                bad_invocation, "invocationDigest", DOMAINS["invocation"], refresh,
            )
            bad_wrapper = deepcopy(base_wrapper)
            bad_wrapper["invocationDigest"] = bad_invocation["invocationDigest"]
            bad_wrapper["outcome"]["operand"] = bad_operand_key
            refreshed(
                bad_wrapper, "resultId",
                RESULT_DOMAINS["oracle-operand-production-result"], refresh,
            )
            bad_wrapper_key = typed(
                "oracle-operand-production-result", bad_wrapper["resultId"],
            )
            bad_receipt = deepcopy(base_receipt)
            bad_receipt["invocationDigest"] = bad_invocation["invocationDigest"]
            bad_receipt["invocation"] = bad_invocation
            bad_receipt["outputs"][0]["artifact"] = bad_wrapper_key
            bad_receipt["semanticTerminal"] = deepcopy(bad_wrapper["outcome"])
            refreshed(bad_receipt, "receiptId", DOMAINS["receipt"], refresh)
            bad_receipt_key = typed("operation-receipt", bad_receipt["receiptId"])
            registrations = [
                (bad_operand_key, bad_operand), (bad_wrapper_key, bad_wrapper),
                *(extra_assets or []),
            ]

            if enclosing_closure is None:
                temporarily_register(
                    registrations, lambda: self.validate_receipt(bad_receipt),
                )
                return

            # In the fully refreshed mode, carry the mutation through the
            # receipt, wrapper, catalog, registry, and closure identities so
            # rejection cannot be attributed to a stale enclosing self ID.
            registrations.append((bad_receipt_key, bad_receipt))

            def validate_enclosing() -> None:
                original_catalog = self.catalog
                original_entries = self.entries
                try:
                    entries = {
                        (item["role"], item["digest"]): deepcopy(item)
                        for item in original_catalog["entries"]
                    }
                    for artifact, value in registrations:
                        identity = (artifact["role"], artifact["digest"])
                        old_entry = entries.get(identity)
                        if old_entry is None:
                            template = next(
                                item for item in original_catalog["entries"]
                                if item["role"] == artifact["role"]
                            )
                            old_entry = deepcopy(template)
                        old_entry["digest"] = artifact["digest"]
                        old_entry["contentSha256"] = raw_sha256(
                            canonical(value).encode("utf-8"),
                        )
                        entries[identity] = old_entry
                    bad_catalog = deepcopy(original_catalog)
                    bad_catalog["entries"] = sorted(
                        entries.values(), key=lambda item: (item["role"], item["digest"]),
                    )
                    refreshed(
                        bad_catalog, "catalogId", "k-in-k/artifact-catalog/v2", refresh,
                    )
                    self.catalog = bad_catalog
                    self.entries = {
                        (item["role"], item["digest"]): item
                        for item in bad_catalog["entries"]
                    }
                    bad_closure = deepcopy(enclosing_closure)
                    bad_closure["result"] = bad_wrapper_key
                    bad_closure["receipt"] = bad_receipt_key
                    bad_closure["artifactCatalog"] = deepcopy(bad_catalog)
                    reached, operations, seed = _reachable(
                        self.assets, bad_wrapper_key, bad_receipt_key,
                    )
                    schemas = _schema_names_for_assets(
                        self.root, self.role_registry, self.assets, reached, seed,
                    )
                    bad_closure["registry"] = build_replay_registry(
                        self.root, schemas, operations,
                    )
                    refreshed(bad_closure, "closureId", DOMAINS["closure"], refresh)
                    self.validate_closure(bad_closure)
                finally:
                    self.catalog = original_catalog
                    self.entries = original_entries

            temporarily_register(registrations, validate_enclosing)

        def collection_probe(
            base: dict[str, Any], change: Callable[[dict[str, Any]], None],
            *, rebuild: Iterable[int] = (),
        ) -> Callable[[bool], None]:
            def check(refresh: bool) -> None:
                bad = deepcopy(base)
                change(bad)
                if refresh:
                    for index in rebuild:
                        visit = bad["visited"][index]
                        bad["visited"][index] = visit_record(
                            bad["collectionScopeId"], bad["invocationDigest"],
                            visit["visitOrdinal"], visit["trace"], visit["disposition"],
                        )
                    identify(bad, "collectionId", DOMAINS["collection"])
                self.validate_collection(bad)
            return check

        probes["trace-v1-on-v2-edge"] = collection_probe(
            collection, lambda value: value["visited"][0].__setitem__("trace", old_trace_key), rebuild=(0,),
        )
        probes["branch-ordinal-gap"] = collection_probe(
            collection, lambda value: value["visited"][1].__setitem__("visitOrdinal", 3), rebuild=(1,),
        )

        def query_satisfied_without_match_found(refresh: bool) -> None:
            bad = deepcopy(existential_collection)
            bad["stopReason"] = {"kind": "search-exhausted"}
            bad["pendingWork"] = {"discoveredCount": 0}
            refreshed(bad, "collectionId", DOMAINS["collection"], refresh)
            self.validate_collection_stop_relation(bad, existential_key)

        probes[
            "collection-query-satisfied-without-match-found"
        ] = query_satisfied_without_match_found

        main_attempt = main_execution_receipt["invocation"]["parameters"]["executionKey"]
        main_trace = self.resolve(collection["visited"][0]["trace"])

        def trace_vocabulary_drift(refresh: bool) -> None:
            bad = deepcopy(main_trace)
            bad["eventVocabularyDigest"] = "f" * 64
            refreshed(bad, "traceId", DOMAINS["trace"], refresh)
            self.validate_trace(bad)
            self.validate_trace_execution_relation(
                bad, collection["visited"][0]["disposition"], main_attempt,
            )

        probes["collection-trace-vocabulary-drift"] = trace_vocabulary_drift
        wrong_terminal_key = next(
            typed("terminal-state", identity)
            for (role, identity), value in self.assets.items()
            if role == "terminal-state"
            and isinstance(value, dict)
            and value.get("definitionDigest")
            != main_attempt["subject"]["definition"]["digest"]
        )
        probes["collection-terminal-definition-drift"] = lambda _refresh: self.validate_trace_execution_relation(
            main_trace, {"kind": "normal", "terminal": wrong_terminal_key},
            main_attempt,
        )
        crash_result_value = self.resolve(
            self.vector["evidence"]["semanticCrashExecution"],
        )
        crash_collection_value = self.resolve(crash_result_value["branchCollection"])
        crash_visit_value = crash_collection_value["visited"][0]
        crash_value = self.resolve(crash_visit_value["disposition"]["crash"])

        def crash_profile_drift(refresh: bool) -> None:
            bad = deepcopy(crash_value)
            bad["executionProfileDigest"] = "f" * 64
            refreshed(bad, "crashDigest", "k-in-k/semantic-crash/v1", refresh)
            bad_key = typed("semantic-crash", bad["crashDigest"])
            temporarily_register(
                [(bad_key, bad)],
                lambda: self.validate_trace_execution_relation(
                    self.resolve(crash_visit_value["trace"]),
                    {"kind": "semantic-crash", "crash": bad_key}, main_attempt,
                ),
            )

        probes["collection-crash-profile-drift"] = crash_profile_drift

        def wrong_branch(refresh: bool) -> None:
            bad = deepcopy(collection)
            visit = bad["visited"][0]
            visit["branchKey"] = digest(DOMAINS["branch"], {
                "invocationDigest": bad["invocationDigest"], "visitOrdinal": 0,
            })
            if refresh:
                visit["traceOccurrence"] = digest(DOMAINS["occurrence"], {
                    "collectionScopeId": bad["collectionScopeId"],
                    "invocationDigest": bad["invocationDigest"],
                    **without(visit, "traceOccurrence"),
                })
                identify(bad, "collectionId", DOMAINS["collection"])
            self.validate_collection(bad)

        probes["branch-key-without-scope"] = wrong_branch
        probes["trace-occurrence-without-disposition"] = collection_probe(
            collection,
            lambda value: value["visited"][0].__setitem__(
                "traceOccurrence",
                digest(DOMAINS["occurrence"], without(value["visited"][0], "traceOccurrence", "disposition")),
            ),
        )
        probes["pending-work-proves-coverage"] = collection_probe(
            collection, lambda value: value["pendingWork"].__setitem__("discoveredCount", 1),
        )
        probes["empty-without-produced-decision"] = collection_probe(
            empty_collection, lambda value: value.__setitem__("emptySearchDecision", None),
        )
        probes["empty-marker-on-nonempty"] = collection_probe(
            collection, lambda value: value.__setitem__("emptySearchDecision", self.vector["evidence"]["emptyDecision"]),
        )
        probes["exhaustive-match-found"] = collection_probe(
            collection, lambda value: value.__setitem__("stopReason", {"kind": "match-found"}),
        )

        normal_terminal = deepcopy(collection["visited"][0]["disposition"]["terminal"])
        probes["existential-without-final-query-satisfied"] = collection_probe(
            existential_collection,
            lambda value: value["visited"][-1].__setitem__(
                "disposition", {"kind": "normal", "terminal": normal_terminal},
            ),
            rebuild=(0,),
        )

        def existential_collection_semantics(
            change: Callable[[dict[str, Any]], None], refresh: bool,
        ) -> None:
            bad = deepcopy(existential_collection)
            change(bad)
            refreshed(bad, "collectionId", DOMAINS["collection"], refresh)
            plan_value = self.resolve(existential_pattern["patternPlan"])
            table_value = self.resolve(existential_pattern["sideConditionTable"])
            traces = {
                visit["trace"]["digest"]: self.resolve(visit["trace"])
                for visit in bad["visited"]
            }
            pattern_result(
                bad, traces, plan_value,
                {field: existential_pattern[field] for field in (
                    "patternSource", "patternPlan", "patternQuery",
                )},
                existential_pattern["sideConditionTable"], table_value,
                search_policy="existential-first",
            )

        probes["existential-collection-query-neutral"] = lambda refresh: existential_collection_semantics(
            lambda value: value.__setitem__(
                "queryCoupling", {"kind": "query-independent"},
            ),
            refresh,
        )

        def earlier_match(value: dict[str, Any]) -> None:
            trace_key_value = value["visited"][-1]["trace"]
            value["visited"] = [
                visit_record(
                    value["collectionScopeId"], value["invocationDigest"], 0,
                    trace_key_value, {"kind": "normal", "terminal": normal_terminal},
                ),
                visit_record(
                    value["collectionScopeId"], value["invocationDigest"], 1,
                    trace_key_value, {"kind": "query-satisfied"},
                ),
            ]

        probes["existential-earlier-match"] = lambda refresh: existential_collection_semantics(
            earlier_match, refresh,
        )

        def witness_under_exhaustion(value: dict[str, Any]) -> None:
            value["stopReason"] = {"kind": "search-exhausted"}
            value["pendingWork"] = {"discoveredCount": 0}
            visit = value["visited"][-1]
            value["visited"][-1] = visit_record(
                value["collectionScopeId"], value["invocationDigest"],
                visit["visitOrdinal"], visit["trace"],
                {"kind": "normal", "terminal": normal_terminal},
            )

        probes["existential-witness-under-exhaustion"] = lambda refresh: existential_collection_semantics(
            witness_under_exhaustion, refresh,
        )

        def pattern_probe(change: Callable[[dict[str, Any]], None], base: dict[str, Any] = pattern) -> Callable[[bool], None]:
            def check(refresh: bool) -> None:
                bad = deepcopy(base)
                change(bad)
                refreshed(bad, "resultId", DOMAINS["pattern"], refresh)
                self.validate_pattern(bad)
            return check

        probes["duplicate-trace-denotation-omitted"] = pattern_probe(
            lambda value: (
                value.__setitem__("pathResults", deepcopy(value["pathResults"][:1])),
                value.__setitem__("witnesses", deepcopy(value["witnesses"][:1])),
            )
        )
        probes["witness-digest-order"] = pattern_probe(
            lambda value: value.__setitem__("witnesses", list(reversed(value["witnesses"])))
        )
        probes["match-found-claimed-complete"] = pattern_probe(
            lambda value: value["decision"].__setitem__("completeCoverage", True),
            existential_pattern,
        )
        probes["path-collection-drift"] = pattern_probe(
            lambda value: value.__setitem__("collection", existential_pattern["collection"])
        )
        wrong_query = self.resolve(
            self.resolve(self.vector["evidence"]["indeterminatePattern"])["patternQuery"],
        )
        probes["pattern-query-plan-source-drift"] = pattern_probe(
            lambda value: value.__setitem__(
                "patternQuery", typed("pattern-query", wrong_query["queryId"]),
            )
        )
        failed_pattern_operation = next(
            value for value in self.receipts.values()
            if value["producerStatus"] == "failed"
            and value["invocation"]["operationKind"] == "pattern-evaluation"
        )

        def failed_pattern_wrong_query(refresh: bool) -> None:
            bad = deepcopy(failed_pattern_operation)
            bad["invocation"]["parameters"]["patternQuery"] = typed(
                "pattern-query", wrong_query["queryId"],
            )
            bad["invocation"]["inputs"][4]["artifact"] = typed(
                "pattern-query", wrong_query["queryId"],
            )
            refreshed(
                bad["invocation"], "invocationDigest", DOMAINS["invocation"], refresh,
            )
            bad["invocationDigest"] = bad["invocation"]["invocationDigest"]
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["failed-pattern-operation-wrong-query"] = failed_pattern_wrong_query

        def execution_output_reordered(refresh: bool) -> None:
            bad = deepcopy(main_execution_result)
            bad["producedArtifacts"] = list(reversed(bad["producedArtifacts"]))
            refreshed(bad, "resultId", DOMAINS["execution-result"], refresh)
            self.validate_execution_wrapper(bad, main_execution_receipt)

        probes["execution-output-reordered"] = execution_output_reordered

        crash_result = self.resolve(self.vector["evidence"]["semanticCrashExecution"])
        crash_receipt = next(
            value for value in self.receipts.values()
            if value["producerStatus"] == "complete"
            and value["outputs"][0]["artifact"]
            == self.vector["evidence"]["semanticCrashExecution"]
        )
        crash_cache = next(
            value for (role, _), value in self.assets.items()
            if role == "cache-record" and value.get("schemaVersion") == 2
            and value["productionEvidence"]["receipt"]["digest"]
            == crash_receipt["receiptId"]
        )

        def semantic_crash_graph(
            change: Callable[[list[dict[str, str]]], list[dict[str, str]]],
            refresh: bool,
        ) -> None:
            bad_result = deepcopy(crash_result)
            bad_result["producedArtifacts"] = change(bad_result["producedArtifacts"])
            refreshed(bad_result, "resultId", DOMAINS["execution-result"], refresh)
            bad_result_key = typed("execution-attempt-result", bad_result["resultId"])
            bad_receipt = deepcopy(crash_receipt)
            bad_receipt["outputs"][0]["artifact"] = bad_result_key
            refreshed(bad_receipt, "receiptId", DOMAINS["receipt"], refresh)
            bad_receipt_key = typed("operation-receipt", bad_receipt["receiptId"])
            bad_cache = deepcopy(crash_cache)
            bad_cache["producedArtifacts"] = deepcopy(bad_result["producedArtifacts"])
            bad_cache["productionEvidence"].update({
                "receipt": bad_receipt_key, "result": bad_result_key,
            })
            refreshed(bad_cache, "recordId", DOMAINS["cache"], refresh)
            temporarily_register(
                [(bad_result_key, bad_result), (bad_receipt_key, bad_receipt)],
                lambda: self.validate_cache(bad_cache),
            )

        probes["semantic-crash-terminal-omitted"] = lambda refresh: semantic_crash_graph(
            lambda values: deepcopy(values[1:]), refresh,
        )
        probes["semantic-crash-output-reordered"] = lambda refresh: semantic_crash_graph(
            lambda values: [values[1], values[0], *deepcopy(values[2:])], refresh,
        )
        probes["semantic-crash-output-surplus"] = lambda refresh: semantic_crash_graph(
            lambda values: [*deepcopy(values), deepcopy(values[0])], refresh,
        )

        def terminal_drift(refresh: bool) -> None:
            bad = deepcopy(main_execution_result)
            bad["terminalRecord"]["stopReason"] = {"kind": "branch-limit", "failure": bag10_failure("branch-limit", scope="test")}
            refreshed(bad, "resultId", DOMAINS["execution-result"], refresh)
            self.validate_execution_wrapper(bad, main_execution_receipt)

        probes["execution-wrapper-terminal-drift"] = terminal_drift

        def cache_promotion(refresh: bool) -> None:
            bad = deepcopy(diagnostic)
            bad["completion"]["executionConformance"] = "finite-vector-proven"
            bad["completion"]["evidenceClass"] = "exact-bounded-attempt"
            bad["reuseClass"] = "exact-bounded-attempt"
            refreshed(bad, "recordId", DOMAINS["cache"], refresh)
            self.validate_cache(bad)

        probes["cache-not-proven-promoted"] = cache_promotion

        def completed_without_wrapper(refresh: bool) -> None:
            bad = deepcopy(main_execution_receipt)
            bad["outputs"] = []
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["completed-receipt-without-wrapper"] = completed_without_wrapper

        def failed_with_output(refresh: bool) -> None:
            bad = deepcopy(main_execution_receipt)
            bad["producerStatus"] = "failed"
            bad["semanticTerminal"] = None
            bad["failure"] = infrastructure_failure()
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["failed-receipt-with-output"] = failed_with_output

        def completed_native_conformance(refresh: bool) -> None:
            bad = deepcopy(main_execution_receipt)
            bad["producer"]["executionConformance"] = "native-proven"
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["completed-receipt-native-conformance"] = completed_native_conformance

        def failed_finite_conformance(refresh: bool) -> None:
            bad = deepcopy(failed_execution_receipt)
            bad["producer"]["executionConformance"] = "finite-vector-proven"
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["failed-receipt-finite-conformance"] = failed_finite_conformance

        def receipt_producer_drift(refresh: bool) -> None:
            bad = deepcopy(main_execution_receipt)
            bad["producer"]["producerId"] = "invented-producer"
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["receipt-producer-identity-drift"] = receipt_producer_drift

        def wrapper_cycle(refresh: bool) -> None:
            bad = deepcopy(pattern_wrapper)
            bad["producingReceipt"] = typed("operation-receipt", pattern_receipt["receiptId"])
            refreshed(bad, "resultId", DOMAINS["pattern-evaluation-result"], refresh)
            self.validate_result_wrapper(bad, pattern_receipt)

        probes["pattern-wrapper-self-receipt-cycle"] = wrapper_cycle

        def component_slot_drift(refresh: bool) -> None:
            bad = deepcopy(components[0])
            bad["slotId"] = "f" * 64
            refreshed(bad, "componentResultId", DOMAINS["component-result"], refresh)
            self.validate_component(bad, corpus_manifest)

        probes["component-slot-drift"] = component_slot_drift

        historical_wrong_declaration = read_json(
            self.fixtures
            / "oracle-declaration-execution-pattern-pattern-outcome-bindings-distinguish.json"
        )

        def manifest_declaration_drift(refresh: bool) -> None:
            bad = deepcopy(corpus_manifest)
            slot = bad["tests"][0]["slots"][0]
            slot["declaration"] = typed(
                "oracle-declaration", historical_wrong_declaration["declarationId"],
            )
            refreshed(slot, "slotId", DOMAINS["slot"], refresh)
            refreshed(bad, "manifestId", DOMAINS["corpus-manifest"], refresh)
            self.validate_manifest(bad)

        probes["manifest-slot-declaration-test-drift"] = manifest_declaration_drift

        def manifest_query_plan_drift(refresh: bool) -> None:
            bad = deepcopy(corpus_manifest)
            slot = bad["tests"][0]["slots"][0]
            bad_declaration = deepcopy(self.resolve(slot["declaration"]))
            wrong_query_key = typed("pattern-query", wrong_query["queryId"])
            bad_declaration["kindConfig"]["patternQuery"] = wrong_query_key
            refreshed(
                bad_declaration, "declarationId",
                "k-in-k/oracle-declaration/v1", refresh,
            )
            bad_declaration_key = typed(
                "oracle-declaration", bad_declaration["declarationId"],
            )
            slot["declaration"] = bad_declaration_key
            slot["patternQuery"] = wrong_query_key
            refreshed(slot, "slotId", DOMAINS["slot"], refresh)
            refreshed(bad, "manifestId", DOMAINS["corpus-manifest"], refresh)
            temporarily_register(
                [(bad_declaration_key, bad_declaration)],
                lambda: self.validate_manifest(bad),
            )

        probes["manifest-slot-query-plan-drift"] = manifest_query_plan_drift

        def manifest_side_condition_unresolved(refresh: bool) -> None:
            bad = deepcopy(corpus_manifest)
            slot = bad["tests"][0]["slots"][0]
            slot["sideConditionTable"] = typed(
                "side-condition-conformance-table", "f" * 64,
            )
            refreshed(slot, "slotId", DOMAINS["slot"], refresh)
            refreshed(bad, "manifestId", DOMAINS["corpus-manifest"], refresh)
            self.validate_manifest(bad)

        probes[
            "manifest-slot-side-condition-unresolved"
        ] = manifest_side_condition_unresolved

        def skipped_with_receipt(refresh: bool) -> None:
            bad = skipped_component(corpus_manifest, corpus_manifest["tests"][0]["slots"][0], 0)
            bad["executionReceipt"] = components[0]["executionReceipt"]
            if not refresh:
                bad["componentResultId"] = "0" * 64
            self.validate_component(bad, corpus_manifest)

        probes["skipped-component-with-receipt"] = skipped_with_receipt

        def corpus_reorder(refresh: bool) -> None:
            bad = deepcopy(corpus_result)
            bad["components"] = list(reversed(bad["components"]))
            refreshed(bad, "corpusResultId", DOMAINS["corpus-result"], refresh)
            self.validate_corpus(bad)

        probes["corpus-component-reorder"] = corpus_reorder

        def corpus_skipped(refresh: bool) -> None:
            bad = deepcopy(corpus_result)
            bad["decision"] = {"kind": "skipped", "completeCoverage": False}
            refreshed(bad, "corpusResultId", DOMAINS["corpus-result"], refresh)
            self.validate_corpus(bad)

        probes["corpus-top-level-skipped"] = corpus_skipped

        def corpus_failure_disposition_drift(refresh: bool) -> None:
            bad = deepcopy(failure_corpus_result)
            bad["decision"]["kind"] = "unknown"
            bad["testResults"][0]["decision"]["kind"] = "unknown"
            refreshed(bad, "corpusResultId", DOMAINS["corpus-result"], refresh)
            self.validate_corpus(bad)

        probes[
            "corpus-failure-taxonomy-disposition-drift"
        ] = corpus_failure_disposition_drift

        probes["registry-v1-substitution"] = lambda _refresh: self.validate_registry({
            **deepcopy(corpus_closure),
            "registry": read_json(self.fixtures / "bag15-replay-version-registry.json"),
        })

        def registry_change(change: Callable[[dict[str, Any]], None]) -> Callable[[bool], None]:
            def check(refresh: bool) -> None:
                bad = deepcopy(corpus_closure)
                change(bad["registry"])
                refreshed(bad["registry"], "registryId", "k-in-k/replay-version-registry/v2", refresh)
                self.validate_registry(bad)
            return check

        probes["registry-missing-schema"] = registry_change(
            lambda value: value.__setitem__("schemas", deepcopy(value["schemas"][:-1]))
        )
        probes["registry-surplus-operation"] = registry_change(
            lambda value: value.__setitem__(
                "operations",
                [*deepcopy(value["operations"]), {"operationKind": "oracle-operand-production", "operationVersion": 2}],
            )
        )

        def catalog_alias(refresh: bool) -> None:
            bad = deepcopy(self.catalog)
            duplicate = deepcopy(bad["entries"][0])
            bad["entries"].insert(1, duplicate)
            refreshed(bad, "catalogId", "k-in-k/artifact-catalog/v2", refresh)
            self.validate_catalog(bad)

        probes["catalog-same-key-version-alias"] = catalog_alias

        def catalog_opaque_hash_drift(refresh: bool) -> None:
            bad = deepcopy(self.catalog)
            entry = next(
                item for item in bad["entries"]
                if item["role"] == "pattern-source"
            )
            entry["contentSha256"] = "f" * 64
            refreshed(
                bad, "catalogId", "k-in-k/artifact-catalog/v2", refresh,
            )
            self.validate_catalog(bad)

        probes["catalog-opaque-content-hash-drift"] = catalog_opaque_hash_drift

        def role_registry_authority_drift(refresh: bool) -> None:
            bad_registry = deepcopy(self.role_registry)
            shared = next(
                item for item in bad_registry["specs"]
                if len(item.get("structuredVersions", [])) > 1
            )
            shared["structuredVersions"] = list(
                reversed(shared["structuredVersions"]),
            )
            refreshed(
                bad_registry, "registryId",
                "k-in-k/artifact-role-specs/v2", refresh,
            )
            bad_catalog = deepcopy(self.catalog)
            bad_catalog["roleSpecRegistryId"] = bad_registry["registryId"]
            refreshed(
                bad_catalog, "catalogId",
                "k-in-k/artifact-catalog/v2", refresh,
            )
            original_registry, original_catalog = self.role_registry, self.catalog
            try:
                self.role_registry, self.catalog = bad_registry, bad_catalog
                self.validate_resolver()
            finally:
                self.role_registry, self.catalog = original_registry, original_catalog

        probes["role-registry-authority-drift"] = role_registry_authority_drift

        def projected_artifact_identity_drift(_refresh: bool) -> None:
            identity, value = next(
                (identity, value)
                for identity, value in self.assets.items()
                if identity[0] == "patch"
            )
            bad = deepcopy(value)
            bad["edits"][0]["expectedContent"] = "f" * 64
            self.validate_asset_identity(identity, bad)

        probes[
            "projected-artifact-identity-drift"
        ] = projected_artifact_identity_drift

        def successor_taxonomy_placement_omitted(refresh: bool) -> None:
            bad = deepcopy(self.taxonomy)
            entry = next(
                item for item in bad["entries"]
                if item["stage"] == "infrastructure"
                and item["classification"] == "artifact-corruption"
            )
            entry["placements"] = [
                placement for placement in entry["placements"]
                if (placement["context"], placement["scope"])
                != ("pattern-test", "test")
            ]
            refreshed(
                bad, "taxonomyId", "k-in-k/failure-taxonomy/v1", refresh,
            )
            self.validate_successor_taxonomy(bad)

        probes[
            "successor-taxonomy-placement-omitted"
        ] = successor_taxonomy_placement_omitted
        probes["legacy-schema-version-dispatch"] = lambda _refresh: select_structured_version(
            next(item for item in self.role_registry["specs"] if item["role"] == "pattern-query"),
            {**deepcopy(pattern["patternQuery"]), "schemaVersion": 1},
        )
        probes["schema-version-legacy-dispatch"] = lambda _refresh: select_structured_version(
            next(item for item in self.role_registry["specs"] if item["role"] == "event-trace"),
            without(self.resolve(self.vector["evidence"]["sharedTrace"]), "schemaVersion"),
        )

        def closure_drift(refresh: bool) -> None:
            bad = deepcopy(corpus_closure)
            bad["artifactCatalog"]["roleSpecRegistryId"] = "f" * 64
            if refresh:
                identify(bad["artifactCatalog"], "catalogId", "k-in-k/artifact-catalog/v2")
                identify(bad, "closureId", DOMAINS["closure"])
            self.validate_closure(bad)

        probes["closure-catalog-registry-drift"] = closure_drift

        def cache_projection_probe(
            change: Callable[[list[dict[str, str]]], list[dict[str, str]]],
        ) -> Callable[[bool], None]:
            def check(refresh: bool) -> None:
                bad = deepcopy(two_execution_closure)
                bad["cacheRecords"] = change(bad["cacheRecords"])
                refreshed(bad, "closureId", DOMAINS["closure"], refresh)
                self.validate_closure(bad)
            return check

        probes["cache-projection-omitted"] = cache_projection_probe(
            lambda values: deepcopy(values[1:]),
        )
        probes["cache-projection-reordered"] = cache_projection_probe(
            lambda values: list(reversed(values)),
        )
        probes["cache-projection-surplus"] = cache_projection_probe(
            lambda values: [*deepcopy(values), self.vector["evidence"]["diagnosticCache"]],
        )

        concrete_operand = self.resolve(
            self.vector["evidence"]["concreteOutputOperand"],
        )
        concrete_table = self.resolve(concrete_operand["completionEvidence"]["table"])
        predicate_operand = self.resolve(
            self.vector["evidence"]["predicateOperand"],
        )
        predicate_table = self.resolve(predicate_operand["completionEvidence"]["table"])
        reach_operand = self.resolve(
            self.vector["evidence"]["reachabilityOperand"],
        )
        reach_table = self.resolve(reach_operand["completionEvidence"]["table"])
        terminal_candidates = [
            typed("terminal-state", identity)
            for (role, identity) in sorted(self.assets)
            if role == "terminal-state"
        ]
        concrete_terminal = concrete_table["rows"][0]["terminal"]["artifact"]
        wrong_terminal = next(
            item for item in terminal_candidates if item != concrete_terminal
        )

        def wrong_occurrence_terminal(refresh: bool) -> None:
            bad_table = deepcopy(concrete_table)
            row = bad_table["rows"][0]
            row["terminal"]["artifact"] = wrong_terminal
            identify(row, "rowId", "k-in-k/semantic-output-finite-row/v1")
            refreshed(
                bad_table, "tableId", "k-in-k/semantic-output-finite-table/v1",
                refresh,
            )
            table_key_value = typed(
                "semantic-output-finite-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(concrete_operand)
            bad_operand["completionEvidence"].update({
                "table": table_key_value, "rowId": row["rowId"],
            })

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value
                inv["inputs"][-1]["artifact"] = wrong_terminal

            mutated_oracle_graph(
                concrete_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes["finite-row-wrong-occurrence-terminal"] = wrong_occurrence_terminal

        def reachability_pair_reorder(refresh: bool) -> None:
            bad_table = deepcopy(reach_table)
            row = bad_table["rows"][0]
            row["producerTraces"] = list(reversed(row["producerTraces"]))
            row["terminalStates"] = list(reversed(row["terminalStates"]))
            refreshed(
                bad_table, "tableId", "k-in-k/reachability-conformance-table/v1",
                refresh,
            )
            table_key_value = typed(
                "reachability-conformance-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(reach_operand)
            bad_operand["completionEvidence"]["table"] = table_key_value

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value

            mutated_oracle_graph(
                reach_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes["reachability-row-pair-reorder"] = reachability_pair_reorder

        def predicate_input_drift(refresh: bool) -> None:
            bad_table = deepcopy(predicate_table)
            row = bad_table["rows"][0]
            predicate_wrong_terminal = next(
                item for item in terminal_candidates if item != row["input"]
            )
            row["input"] = predicate_wrong_terminal
            refreshed(
                bad_table, "tableId", "k-in-k/predicate-conformance-table/v1",
                refresh,
            )
            table_key_value = typed(
                "predicate-conformance-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(predicate_operand)
            bad_operand["completionEvidence"].update({
                "table": table_key_value, "input": predicate_wrong_terminal,
            })
            bad_operand["normalizedValue"]["input"] = predicate_wrong_terminal

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value
                inv["inputs"][-1]["artifact"] = predicate_wrong_terminal

            mutated_oracle_graph(
                predicate_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes["predicate-input-occurrence-drift"] = predicate_input_drift

        def concrete_content_hash_drift(refresh: bool) -> None:
            bad_table = deepcopy(concrete_table)
            row = bad_table["rows"][0]
            row["channels"][0]["contentSha256"] = "f" * 64
            identify(row, "rowId", "k-in-k/semantic-output-finite-row/v1")
            refreshed(
                bad_table, "tableId",
                "k-in-k/semantic-output-finite-table/v1", refresh,
            )
            table_key_value = typed(
                "semantic-output-finite-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(concrete_operand)
            bad_operand["completionEvidence"].update({
                "table": table_key_value, "rowId": row["rowId"],
            })
            bad_operand["normalizedValue"] = {"channels": deepcopy(row["channels"])}

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value

            mutated_oracle_graph(
                concrete_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes["concrete-row-content-hash-drift"] = concrete_content_hash_drift

        def reachability_witness_unresolved(refresh: bool) -> None:
            bad_table = deepcopy(reach_table)
            row = bad_table["rows"][0]
            row["witnesses"] = [typed("reachability-witness", "f" * 64)]
            refreshed(
                bad_table, "tableId",
                "k-in-k/reachability-conformance-table/v1", refresh,
            )
            table_key_value = typed(
                "reachability-conformance-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(reach_operand)
            bad_operand["completionEvidence"]["table"] = table_key_value
            bad_operand["normalizedValue"] = {
                "status": "reached", "witnesses": deepcopy(row["witnesses"]),
            }

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value

            mutated_oracle_graph(
                reach_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes[
            "reachability-row-witness-unresolved"
        ] = reachability_witness_unresolved

        def predicate_query_unresolved(refresh: bool) -> None:
            bad_table = deepcopy(predicate_table)
            row = bad_table["rows"][0]
            wrong_query_key = typed("predicate-query", "f" * 64)
            row["query"] = wrong_query_key
            refreshed(
                bad_table, "tableId",
                "k-in-k/predicate-conformance-table/v1", refresh,
            )
            table_key_value = typed(
                "predicate-conformance-table", bad_table["tableId"],
            )
            bad_operand = deepcopy(predicate_operand)
            bad_operand["completionEvidence"].update({
                "table": table_key_value, "query": wrong_query_key,
            })
            bad_operand["normalizedValue"]["query"] = wrong_query_key

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["finiteTable"] = table_key_value
                inv["parameters"]["finiteRow"] = deepcopy(row)
                inv["inputs"][3]["artifact"] = table_key_value
                inv["inputs"][4]["artifact"] = wrong_query_key

            mutated_oracle_graph(
                predicate_receipt, refresh, change, operand_value=bad_operand,
                extra_assets=[(table_key_value, bad_table)],
            )

        probes["predicate-row-query-unresolved"] = predicate_query_unresolved

        probes["oracle-operation-subject-drift"] = lambda refresh: mutated_oracle_graph(
            concrete_receipt, refresh,
            lambda inv, _operand_key: inv["parameters"].__setitem__(
                "subject", {
                    "kind": "baseline",
                    "definition": typed("definition", "f" * 64),
                },
            ),
        )

        def invocation_only_probe(
            base_receipt: dict[str, Any],
            change: Callable[[dict[str, Any]], None],
        ) -> Callable[[bool], None]:
            return lambda refresh: mutated_oracle_graph(
                base_receipt, refresh,
                lambda inv, _operand_key: change(inv),
            )

        probes["finite-row-occurrence-omitted"] = invocation_only_probe(
            reach_receipt,
            lambda inv: inv["parameters"].__setitem__(
                "occurrences", deepcopy(inv["parameters"]["occurrences"][:-1]),
            ),
        )
        probes["finite-row-occurrence-surplus"] = invocation_only_probe(
            concrete_receipt,
            lambda inv: inv["parameters"].__setitem__(
                "occurrences",
                [
                    *deepcopy(inv["parameters"]["occurrences"]),
                    deepcopy(inv["parameters"]["occurrences"][0]),
                ],
            ),
        )

        def scenario_from_receipt(receipt_value: dict[str, Any]) -> dict[str, Any]:
            result_key_value = receipt_value["outputs"][0]["artifact"]
            result_value = self.resolve(result_key_value)
            collection_key_value = result_value["branchCollection"]
            return {
                "invocation": receipt_value["invocation"],
                "result": result_key_value, "collection": collection_key_value,
                "receipt": typed("operation-receipt", receipt_value["receiptId"]),
                "collectionValue": self.resolve(collection_key_value),
            }

        bounded_scenario = scenario_from_receipt(self.resolve(
            read_json(self.fixtures / "bag16-closure-bounded-execution.json")["receipt"],
        ))
        existential_scenario = scenario_from_receipt(self.resolve(
            read_json(self.fixtures / "bag16-closure-existential-execution.json")["receipt"],
        ))
        incomplete_cache = self.resolve(
            self.vector["evidence"]["backendAfterBoundedCache"],
        )
        incomplete_scenario = scenario_from_receipt(self.resolve(
            incomplete_cache["productionEvidence"]["receipt"],
        ))

        def substitute_scenario(
            inv: dict[str, Any], scenario: dict[str, Any],
        ) -> None:
            inv["parameters"]["executionInvocation"] = deepcopy(scenario["invocation"])
            inv["parameters"]["executionResult"] = deepcopy(scenario["result"])
            inv["parameters"]["collection"] = deepcopy(scenario["collection"])
            inv["parameters"]["occurrences"] = [
                {
                    "collection": deepcopy(scenario["collection"]),
                    "branchKey": visit["branchKey"],
                    "traceOccurrence": visit["traceOccurrence"],
                }
                for visit in scenario["collectionValue"]["visited"]
            ]
            inv["inputs"][1]["artifact"] = deepcopy(scenario["result"])
            inv["inputs"][2]["artifact"] = deepcopy(scenario["collection"])
            inv["childReceipts"] = [
                receipt_edge("execution-production", scenario["receipt"]),
            ]

        for probe_name, scenario in (
            ("finite-row-incomplete-collection", incomplete_scenario),
            ("finite-row-bounded-collection", bounded_scenario),
            ("finite-row-existential-collection", existential_scenario),
        ):
            probes[probe_name] = invocation_only_probe(
                concrete_receipt,
                lambda inv, scenario_value=scenario: substitute_scenario(
                    inv, scenario_value,
                ),
            )

        probes["finite-row-input-reordered"] = invocation_only_probe(
            concrete_receipt,
            lambda inv: inv.__setitem__(
                "inputs", [inv["inputs"][1], inv["inputs"][0], *inv["inputs"][2:]],
            ),
        )
        probes["finite-row-input-missing"] = invocation_only_probe(
            concrete_receipt,
            lambda inv: inv.__setitem__("inputs", deepcopy(inv["inputs"][:-1])),
        )
        probes["finite-row-child-missing"] = invocation_only_probe(
            concrete_receipt,
            lambda inv: inv.__setitem__("childReceipts", []),
        )

        false_coverage_operand = self.resolve(
            self.vector["evidence"]["falseCoverageOutcomeOperand"],
        )
        false_coverage_pattern = self.resolve(
            false_coverage_operand["normalizedValue"]["patternResult"],
        )
        bindings_declaration_key = self.vector["evidence"][
            "falseCoverageBindingsDeclaration"
        ]
        false_coverage_closure = read_json(
            self.fixtures
            / "bag16-closure-oracle-execution-pattern-false-coverage.json"
        )

        def false_coverage_bindings(refresh: bool) -> None:
            bad_operand = deepcopy(false_coverage_operand)
            bad_operand["declaration"] = deepcopy(bindings_declaration_key)
            bad_operand["normalizedValue"]["bindingTuples"] = [
                [
                    {
                        "name": binding["name"],
                        "sort": binding["term"]["sort"],
                        "value": deepcopy(binding["term"]),
                    }
                    for binding in witness["bindings"]
                ]
                for witness in false_coverage_pattern["witnesses"]
            ]

            def change(inv: dict[str, Any], _operand_key: dict[str, str]) -> None:
                inv["parameters"]["declaration"] = deepcopy(bindings_declaration_key)
                inv["inputs"][0]["artifact"] = deepcopy(bindings_declaration_key)

            mutated_oracle_graph(
                false_coverage_receipt, refresh, change,
                operand_value=bad_operand, enclosing_closure=false_coverage_closure,
            )

        probes["false-coverage-bindings-projection"] = false_coverage_bindings

        bindings_operand = self.resolve(
            self.vector["evidence"]["patternBindingsOperand"],
        )

        def bindings_tuples_omitted(refresh: bool) -> None:
            bad_operand = deepcopy(bindings_operand)
            bad_operand["normalizedValue"]["bindingTuples"] = []
            mutated_oracle_graph(
                bindings_receipt, refresh,
                lambda _inv, _operand_key: None,
                operand_value=bad_operand,
            )

        probes["bindings-operand-tuples-omitted"] = bindings_tuples_omitted

        def oracle_terminal_operand_drift(refresh: bool) -> None:
            bad = deepcopy(bindings_receipt)
            bad["semanticTerminal"] = deepcopy(concrete_receipt["semanticTerminal"])
            refreshed(bad, "receiptId", DOMAINS["receipt"], refresh)
            self.validate_receipt(bad)

        probes["oracle-receipt-terminal-operand-drift"] = oracle_terminal_operand_drift

        def false_coverage_bindings_inline(refresh: bool) -> None:
            bad = deepcopy(false_coverage_operand)
            bad["declaration"] = deepcopy(bindings_declaration_key)
            bad["normalizedValue"]["bindingTuples"] = [
                [
                    {
                        "name": binding["name"], "sort": binding["term"]["sort"],
                        "value": deepcopy(binding["term"]),
                    }
                    for binding in witness["bindings"]
                ]
                for witness in false_coverage_pattern["witnesses"]
            ]
            refreshed(bad, "operandId", "k-in-k/oracle-operand/v1", refresh)
            bad_key = typed("oracle-operand", bad["operandId"])
            temporarily_register(
                [(bad_key, bad)],
                lambda: self.validate_successor_inline_operand(bad),
            )

        probes["false-coverage-bindings-inline-expectation"] = false_coverage_bindings_inline
        advertised = [item["probe"] for item in self.vector["adversaries"]]
        self.ok(advertised == list(ADVERSARIES) and set(probes) == set(ADVERSARIES), "BAG-16 adversary registry/probe drift")
        for name in ADVERSARIES:
            for mode, refresh in (("unchanged", False), ("fully-refreshed", True)):
                self.expect_rejection(
                    lambda probe=probes[name], refresh_ids=refresh: probe(refresh_ids),
                    f"{name}:{mode}",
                )

    def validate_positive_families(self) -> None:
        evidence = self.vector["evidence"]
        exhaustive_no_match = self.resolve(evidence["exhaustiveNoMatch"])
        self.ok(
            exhaustive_no_match["searchPolicy"] == "exhaustive"
            and exhaustive_no_match["decision"] == {"kind": "no-match", "completeCoverage": True}
            and exhaustive_no_match["witnesses"] == [],
            "BAG-16 exhaustive no-match positive is absent",
        )
        existential_no_match = self.resolve(evidence["existentialExhaustedNoMatch"])
        existential_no_match_collection = self.resolve(existential_no_match["collection"])
        self.ok(
            existential_no_match["searchPolicy"] == "existential-first"
            and existential_no_match["decision"] == {"kind": "no-match", "completeCoverage": True}
            and existential_no_match_collection["stopReason"] == {"kind": "search-exhausted"}
            and existential_no_match_collection["pendingWork"] == {"discoveredCount": 0},
            "BAG-16 existential exhausted no-match positive is absent",
        )
        pending_zero = self.resolve(evidence["existentialPendingZero"])
        pending_zero_collection = self.resolve(pending_zero["collection"])
        pending_positive = self.resolve(evidence["existentialPattern"])
        pending_positive_collection = self.resolve(pending_positive["collection"])
        for expected_pending, result, collection in (
            (0, pending_zero, pending_zero_collection),
            (1, pending_positive, pending_positive_collection),
        ):
            self.ok(
                result["decision"]["kind"] == "match"
                and result["decision"]["completeCoverage"] is False
                and collection["stopReason"] == {"kind": "match-found"}
                and collection["pendingWork"]["discoveredCount"] == expected_pending
                and collection["visited"][-1]["disposition"] == {"kind": "query-satisfied"},
                f"BAG-16 existential prefix positive pending={expected_pending} is absent",
            )
        indeterminate = self.resolve(evidence["indeterminatePattern"])
        mixed = self.resolve(evidence["mixedIndeterminatePattern"])
        self.ok(
            indeterminate["decision"]["kind"] == "unknown"
            and indeterminate["decision"]["reason"]["kind"] == "indeterminate-denotation"
            and indeterminate["pathResults"][0]["evaluation"]["status"] == "unknown",
            "BAG-16 trustworthy side-condition-indeterminate positive is absent",
        )
        self.ok(
            mixed["decision"]["kind"] == "match"
            and mixed["decision"]["completeCoverage"] is False
            and [item["evaluation"]["status"] for item in mixed["pathResults"]] == ["match", "unknown"],
            "BAG-16 mixed match/indeterminate false-coverage positive is absent",
        )
        clean_diagnostic = self.resolve(evidence["cleanDiagnosticCache"])
        backend_cache = self.resolve(evidence["backendAfterBoundedCache"])
        bounded_closure = read_json(self.fixtures / "bag16-closure-bounded-execution.json")
        bounded_cache = self.resolve(bounded_closure["cacheRecords"][0])
        self.ok(
            clean_diagnostic["completion"]["evidenceClass"] == "diagnostic-only"
            and clean_diagnostic["reuseClass"] == "not-reusable"
            and backend_cache["completion"]["evidenceClass"] == "diagnostic-only"
            and backend_cache["reuseClass"] == "not-reusable"
            and bounded_cache["reuseClass"] == "exact-bounded-attempt",
            "BAG-16 cache precedence positives are incomplete",
        )
        backend_result = self.resolve(backend_cache["productionEvidence"]["result"])
        backend_collection = self.resolve(backend_result["branchCollection"])
        self.ok(
            backend_collection["visited"][0]["disposition"]["kind"] == "time-limit"
            and backend_collection["stopReason"]["kind"] == "backend-failure",
            "BAG-16 backend-after-bounded collection positive is absent",
        )
        error_pattern = self.resolve(evidence["errorPattern"])
        error_pattern_receipt = next(
            value for value in self.receipts.values()
            if value["producerStatus"] == "complete"
            and value["invocation"]["operationKind"] == "pattern-evaluation"
            and self.resolve(value["outputs"][0]["artifact"]).get("patternResult")
            == evidence["errorPattern"]
        )
        self.ok(
            error_pattern["decision"]["kind"] == "error"
            and error_pattern_receipt["semanticTerminal"] == error_pattern["decision"]
            and error_pattern_receipt["failure"] is None,
            "BAG-16 completed pattern error/null-operation-failure positive is absent",
        )
        crash_result = self.resolve(evidence["semanticCrashExecution"])
        crash_collection = self.resolve(crash_result["branchCollection"])
        crash_visit = crash_collection["visited"][0]
        crash_key = crash_visit["disposition"]["crash"]
        crash = self.resolve(crash_key)
        self.ok(
            crash_result["producedArtifacts"] == [
                crash["terminalState"], crash_key, crash_visit["trace"],
                crash_result["branchCollection"],
            ],
            "BAG-16 semantic-crash terminal/crash/trace/collection output order positive is absent",
        )
        failure_corpus = self.resolve(evidence["failureCorpusResult"])
        failure_components = [self.resolve(item) for item in failure_corpus["components"]]
        self.ok(
            [item["kind"] for item in failure_components] == ["execution-failure", "pattern-failure"]
            and failure_corpus["decision"]["kind"] == "error"
            and failure_corpus["decision"]["completeCoverage"] is False
            and failure_corpus["decision"]["causeComponent"] == failure_corpus["components"][0],
            "BAG-16 full producer-failure corpus fold positive is absent",
        )
        stop_corpus = self.resolve(evidence["stopAfterMatchCorpusResult"])
        stop_components = [self.resolve(item) for item in stop_corpus["components"]]
        self.ok(
            [item["kind"] for item in stop_components] == ["evaluated", "skipped"]
            and stop_corpus["decision"] == {"kind": "match", "completeCoverage": False}
            and stop_components[1]["schedulingReason"]
            == {"kind": "stop-after-test-match", "stoppedAfterTestOrdinal": 0},
            "BAG-16 stop-after-test-match skipped suffix positive is absent",
        )
        main_corpus_closure = read_json(self.fixtures / "bag16-closure-corpus.json")
        main_corpus_wrapper = self.resolve(main_corpus_closure["result"])
        main_corpus = self.resolve(main_corpus_wrapper["corpusResult"])
        main_components = [self.resolve(item) for item in main_corpus["components"]]
        self.ok(
            len(main_components) == 2
            and main_components[0]["executionAttemptKey"] == main_components[1]["executionAttemptKey"]
            and main_components[0]["componentInvocationId"] != main_components[1]["componentInvocationId"],
            "BAG-16 query-neutral two-slot execution fan-out positive is absent",
        )
        two_execution_closure = read_json(
            self.fixtures / "bag16-closure-corpus-two-execution.json",
        )
        self.ok(
            two_execution_closure["cacheRecords"]
            == [
                typed("cache-record", main_corpus_closure["cacheRecords"][0]["digest"]),
                read_json(self.fixtures / "bag16-closure-empty-execution.json")["cacheRecords"][0],
            ],
            "BAG-16 two-execution traversal-order cache projection positive is absent",
        )
        for key_name, expected_kind in (
            ("patternOperand", "execution-pattern"),
            ("patternBindingsOperand", "execution-pattern"),
            ("falseCoverageOutcomeOperand", "execution-pattern"),
            ("concreteOutputOperand", "concrete-output"),
            ("reachabilityOperand", "reachability"),
            ("predicateOperand", "structured-predicate"),
        ):
            operand = self.resolve(evidence[key_name])
            declaration = self.resolve(operand["declaration"])
            self.ok(declaration["kind"] == expected_kind, f"BAG-16 {expected_kind} operand positive is absent")
        false_coverage_operand = self.resolve(evidence["falseCoverageOutcomeOperand"])
        false_coverage_pattern = self.resolve(
            false_coverage_operand["normalizedValue"]["patternResult"],
        )
        false_coverage_declaration = self.resolve(
            false_coverage_operand["declaration"],
        )
        self.ok(
            false_coverage_pattern["decision"]["kind"] == "match"
            and false_coverage_pattern["decision"]["completeCoverage"] is False
            and [
                path["evaluation"].get("status")
                for path in false_coverage_pattern["pathResults"]
            ] == ["match", "unknown"]
            and false_coverage_declaration["projectionSpec"]["projectionId"]
            == "pattern-outcome-v1"
            and false_coverage_operand["normalizedValue"]["bindingTuples"] == [],
            "BAG-16 false-coverage outcome-only projection positive is absent",
        )
        reach_operand = self.resolve(evidence["reachabilityOperand"])
        reach_table = self.resolve(reach_operand["completionEvidence"]["table"])
        self.ok(
            len(reach_table["rows"][0]["producerTraces"])
            == len(reach_table["rows"][0]["terminalStates"]) == 2,
            "BAG-16 multi-occurrence reachability row positive is absent",
        )
        oracle_closure = read_json(self.fixtures / "bag16-closure-oracle-execution-pattern.json")
        self.ok(
            {("oracle-operand-production", 2), ("pattern-evaluation", 1), ("execution-attempt", 2)}
            <= {(item["operationKind"], item["operationVersion"]) for item in oracle_closure["registry"]["operations"]},
            "BAG-16 oracle closure registry omits reachable operation versions",
        )
        self.validate_inline_expectations()

    def run(self) -> None:
        self.validate_resolver()
        publications: dict[str, dict[str, str]] = {}
        for value in self.receipts.values():
            self.validate_receipt(value)
            if value["producerStatus"] == "complete":
                output = value["outputs"][0]["artifact"]
                previous = publications.setdefault(value["invocationDigest"], output)
                self.ok(previous == output, "BAG-16 one invocation published more than one result")
        for (role, _), value in self.assets.items():
            if role == "pattern-result" and value.get("schemaVersion") == 2:
                self.validate_pattern(value)
            elif role == "cache-record" and value.get("schemaVersion") == 2:
                self.validate_cache(value)
            elif role == "corpus-result" and value.get("schemaVersion") == 2:
                self.validate_corpus(value)
        for name in (
            "bag16-closure-corpus.json", "bag16-closure-empty-execution.json",
            "bag16-closure-existential-execution.json", "bag16-closure-bounded-execution.json",
            "bag16-closure-corpus-failures.json",
            "bag16-closure-corpus-stop-after-match.json",
            "bag16-closure-corpus-two-execution.json",
            "bag16-closure-pattern-evaluation.json",
            "bag16-closure-failed-execution.json",
            "bag16-closure-oracle-execution-pattern.json",
            "bag16-closure-oracle-execution-pattern-bindings.json",
            "bag16-closure-oracle-execution-pattern-false-coverage.json",
            "bag16-closure-oracle-concrete-output.json",
            "bag16-closure-oracle-reachability.json",
            "bag16-closure-oracle-structured-predicate.json",
        ):
            self.validate_closure(read_json(self.fixtures / name))
        collection = self.resolve(self.vector["evidence"]["twoBranchCollection"])
        self.ok(collection["visited"][0]["trace"] == collection["visited"][1]["trace"] and collection["visited"][0]["traceOccurrence"] != collection["visited"][1]["traceOccurrence"], "BAG-16 shared-content trace occurrence evidence missing")
        pattern = self.resolve(self.vector["evidence"]["twoBranchPattern"])
        self.ok(len(pattern["pathResults"]) == len(collection["visited"]) == len(pattern["witnesses"]) == 2, "BAG-16 two-branch denotation evidence incomplete")
        self.validate_positive_families()
        self.adversaries()


def new_official_fixtures(root: Path) -> dict[str, str]:
    result = {
        "bag16-artifact-role-specs.json": "artifact-role-specs-v2.schema.json",
        "bag16-artifact-catalog.json": "artifact-catalog-v2.schema.json",
        "bag16-closure-corpus.json": "portable-closure-root.schema.json",
        "bag16-closure-empty-execution.json": "portable-closure-root.schema.json",
        "bag16-closure-existential-execution.json": "portable-closure-root.schema.json",
        "bag16-closure-bounded-execution.json": "portable-closure-root.schema.json",
        "bag16-closure-corpus-failures.json": "portable-closure-root.schema.json",
        "bag16-closure-corpus-stop-after-match.json": "portable-closure-root.schema.json",
        "bag16-closure-corpus-two-execution.json": "portable-closure-root.schema.json",
        "bag16-closure-pattern-evaluation.json": "portable-closure-root.schema.json",
        "bag16-closure-failed-execution.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-execution-pattern.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-execution-pattern-bindings.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-execution-pattern-false-coverage.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-concrete-output.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-reachability.json": "portable-closure-root.schema.json",
        "bag16-closure-oracle-structured-predicate.json": "portable-closure-root.schema.json",
    }
    role_to_schema = {
        "execution-test-invocation": "execution-test-invocation-v2.schema.json",
        "event-trace": "event-trace-v2.schema.json", "branch-trace-collection": "branch-trace-collection.schema.json",
        "empty-search-decision": "empty-search-decision.schema.json", "execution-attempt-result": "execution-attempt-result-v2.schema.json",
        "operation-receipt": "operation-receipt-v2.schema.json", "cache-record": "cache-semantics-v2.schema.json",
        "pattern-result": "pattern-result-v2.schema.json", "pattern-evaluation-result": "pattern-evaluation-result.schema.json",
        "corpus-manifest": "corpus-manifest-v2.schema.json", "corpus-component-invocation": "corpus-component-invocation.schema.json",
        "corpus-component-result": "corpus-component-result.schema.json", "corpus-result": "corpus-result-v2.schema.json",
        "corpus-derivation-result": "corpus-derivation-result.schema.json", "replay-version-registry": "replay-version-registry-v2.schema.json",
        "oracle-declaration": "oracle-semantics.schema.json",
        "oracle-operand": "oracle-semantics.schema.json",
        "oracle-operand-production-result": "oracle-operand-production-result.schema.json",
        "failure-taxonomy": "failure-taxonomy.schema.json",
        "semantic-output-finite-table": "oracle-semantics.schema.json",
        "reachability-conformance-table": "reachability-semantics.schema.json",
        "predicate-conformance-table": "predicate-semantics.schema.json",
    }
    catalog = read_json(root / "fixtures" / "bag16-artifact-catalog.json")
    for entry in catalog["entries"]:
        name = entry["logicalPath"].rsplit("/", 1)[-1]
        if not name.startswith("bag16-") or name in result:
            continue
        schema = role_to_schema.get(entry["role"])
        if schema is not None:
            result[name] = schema
    return result


def verify_package(root: Path, api: dict[str, Any]) -> None:
    Bag16Verifier(root, api).run()
