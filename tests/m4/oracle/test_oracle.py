"""Fast, tool-independent contracts for the M4 oracle library."""

from __future__ import annotations

import copy
from pathlib import Path
import unittest

import behavior
import proofs
import run_proofs
import source_definition


def sort(name: str) -> dict[str, object]:
    return {"node": "KSort", "name": name, "params": []}


def label(name: str) -> dict[str, object]:
    return {"node": "KLabel", "name": name, "params": []}


def apply(name: str, args: list[object]) -> dict[str, object]:
    return {"node": "KApply", "label": label(name), "args": args, "arity": len(args)}


def token(value: str, sort_name: str) -> dict[str, object]:
    return {"node": "KToken", "token": value, "sort": sort(sort_name)}


def rule(rule_label: str, function_label: str) -> dict[str, object]:
    return {
        "node": "KRule",
        "body": {
            "node": "KRewrite",
            "lhs": apply(function_label, [token("0", "Int")]),
            "rhs": token("0", "Int"),
        },
        "requires": apply("#Top", []),
        "ensures": apply("#Top", []),
        "att": {"node": "KAtt", "att": {"label": rule_label}},
    }


def definition(module: str, sentence: dict[str, object]) -> dict[str, object]:
    return {
        "format": "KAST",
        "version": 4,
        "term": {
            "node": "KDefinition",
            "mainModule": module,
            "modules": [
                {
                    "node": "KFlatModule",
                    "name": module,
                    "imports": [],
                    "localSentences": [sentence],
                    "att": {"node": "KAtt", "att": {}},
                }
            ],
            "att": {"node": "KAtt", "att": {}},
        },
    }


def definition_with_sentences(module: str, sentences: list[dict[str, object]]) -> dict[str, object]:
    value = definition(module, sentences[0])
    value["term"]["modules"][0]["localSentences"] = sentences
    return value


def definition_with_imported_module(
    module: str,
    imported: str,
    imported_sentences: list[dict[str, object]],
) -> dict[str, object]:
    value = definition(module, rule("ACT.rule", "actualFun"))
    value["term"]["modules"][0]["imports"] = [
        {"node": "KImport", "name": imported, "isPublic": True}
    ]
    value["term"]["modules"].append(
        {
            "node": "KFlatModule",
            "name": imported,
            "imports": [],
            "localSentences": imported_sentences,
            "att": {"node": "KAtt", "att": {}},
        }
    )
    return value


def syntax_sort(name: str) -> dict[str, object]:
    return {"node": "KSyntaxSort", "sort": sort(name), "params": [], "att": {"node": "KAtt", "att": {}}}


def priority(groups: list[list[str]]) -> dict[str, object]:
    return {"node": "KSyntaxPriority", "priorities": groups, "att": {"node": "KAtt", "att": {}}}


class SourceDefinitionTests(unittest.TestCase):
    def policies(self) -> tuple[source_definition.ProjectionPolicy, source_definition.ProjectionPolicy]:
        attributes = source_definition.DEFAULT_METADATA_ATTRIBUTES | {"label"}
        baseline = source_definition.ProjectionPolicy(
            module_origins={"REF": "imp"},
            identity_labels=frozenset({"REF.rule", "refFun", "#Top"}),
            identity_sorts=frozenset({"Int"}),
            identity_names=frozenset({"REF"}),
            known_attributes=attributes,
        )
        actual = source_definition.ProjectionPolicy(
            module_origins={"ACT": "imp"},
            label_map={"ACT.rule": "REF.rule", "actualFun": "refFun"},
            identity_labels=frozenset({"#Top"}),
            identity_sorts=frozenset({"Int"}),
            name_map={"ACT": "REF"},
            known_attributes=attributes,
        )
        return baseline, actual

    def test_explicit_name_and_origin_maps_close(self) -> None:
        baseline_policy, actual_policy = self.policies()
        result = source_definition.compare_definitions(
            definition("REF", rule("REF.rule", "refFun")),
            definition("ACT", rule("ACT.rule", "actualFun")),
            baseline_policy,
            actual_policy,
        )
        self.assertEqual(result.baseline_sha256, result.actual_sha256)
        self.assertEqual(result.sentence_count, 1)

    def test_unknown_field_fails_closed(self) -> None:
        baseline_policy, actual_policy = self.policies()
        malformed = definition("ACT", rule("ACT.rule", "actualFun"))
        malformed["term"]["modules"][0]["localSentences"][0]["mystery"] = True
        with self.assertRaisesRegex(source_definition.ProjectionError, "unknown KRule fields"):
            source_definition.compare_definitions(
                definition("REF", rule("REF.rule", "refFun")),
                malformed,
                baseline_policy,
                actual_policy,
            )

    def test_exact_compatible_sentence_pair_is_counted(self) -> None:
        attributes = source_definition.DEFAULT_METADATA_ATTRIBUTES | {"label"}
        baseline = source_definition.ProjectionPolicy(
            module_origins={"REF": "imp"},
            identity_labels=frozenset({"REF.rule", "refFun", "#Top"}),
            identity_sorts=frozenset({"Int"}), identity_names=frozenset({"REF"}),
            known_attributes=attributes,
        )
        actual = source_definition.ProjectionPolicy(
            module_origins={"ACT": "imp"},
            identity_labels=frozenset({"ACT.rule", "actualFun", "#Top"}),
            identity_sorts=frozenset({"Int"}), name_map={"ACT": "REF"},
            known_attributes=attributes,
        )
        reference_definition = definition("REF", rule("REF.rule", "refFun"))
        actual_definition = definition("ACT", rule("ACT.rule", "actualFun"))
        reference_sentence = source_definition.project_definition(
            reference_definition, baseline
        )["origins"][0]["sentences"][0]
        actual_sentence = source_definition.project_definition(
            actual_definition, actual
        )["origins"][0]["sentences"][0]
        pair = [{
            "origin": "imp",
            "reference_sha256": source_definition.digest(reference_sentence),
            "actual_sha256": source_definition.digest(actual_sentence),
            "count": 1,
        }]
        result = source_definition.compare_definitions(
            reference_definition, actual_definition, baseline, actual, pair
        )
        self.assertNotEqual(result.baseline_sha256, result.actual_sha256)
        self.assertEqual(result.sentence_count, 1)
        pair[0]["count"] = 2
        with self.assertRaisesRegex(source_definition.ProjectionError, "exact count-2 witness"):
            source_definition.compare_definitions(
                reference_definition, actual_definition, baseline, actual, pair
            )

    def test_flat_module_requires_sentence_origin(self) -> None:
        _, actual_policy = self.policies()
        actual_policy = source_definition.ProjectionPolicy(
            **{**actual_policy.__dict__, "module_origins": {"ACT": None}}
        )
        with self.assertRaisesRegex(source_definition.ProjectionError, "no explicit semantic origin"):
            source_definition.project_definition(
                definition("ACT", rule("ACT.rule", "actualFun")), actual_policy
            )

    def test_imported_owned_module_cannot_be_omitted_from_projection(self) -> None:
        _, actual = self.policies()
        actual = source_definition.ProjectionPolicy(
            **{
                **actual.__dict__,
                "identity_names": actual.identity_names | {"KRS-FRAMEWORK"},
                "closed_module_prefixes": frozenset({"KRS-"}),
            }
        )
        observed = definition_with_imported_module(
            "ACT", "KRS-FRAMEWORK", [syntax_sort("KResult")]
        )
        with self.assertRaisesRegex(
            source_definition.ProjectionError,
            "unclassified closed-namespace module 'KRS-FRAMEWORK'",
        ):
            source_definition.project_definition(observed, actual)

    def test_supplemental_module_is_exact_attestation_not_false_equality(self) -> None:
        _, actual = self.policies()
        common = {
            **actual.__dict__,
            "identity_names": actual.identity_names | {"KRS-FRAMEWORK"},
            "identity_sorts": actual.identity_sorts | {"KResult"},
            "closed_module_prefixes": frozenset({"KRS-"}),
        }
        framework_sentence = syntax_sort("KResult")
        framework_projection = source_definition.project_definition(
            definition("KRS-FRAMEWORK", framework_sentence),
            source_definition.ProjectionPolicy(
                module_origins={"KRS-FRAMEWORK": "framework"},
                identity_names=frozenset({"KRS-FRAMEWORK"}),
                identity_sorts=frozenset({"KResult"}),
            ),
        )["origins"][0]["sentences"][0]
        supplemental_digest = source_definition.digest(framework_projection)
        actual = source_definition.ProjectionPolicy(
            **{
                **common,
                "supplemental_module_origins": {"KRS-FRAMEWORK": "framework"},
                "supplemental_imports_by_origin": {"framework": ()},
                "supplemental_sentence_sha256": {supplemental_digest: 1},
            }
        )
        observed = definition_with_imported_module(
            "ACT", "KRS-FRAMEWORK", [framework_sentence]
        )
        projection = source_definition.project_definition(observed, actual)
        self.assertEqual(
            projection["supplementalSentenceSha256"], {supplemental_digest: 1}
        )
        mutated = copy.deepcopy(observed)
        mutated["term"]["modules"][1]["localSentences"].append(
            copy.deepcopy(framework_sentence)
        )
        with self.assertRaisesRegex(
            source_definition.ProjectionError, "supplemental sentence multiset differs"
        ):
            source_definition.project_definition(mutated, actual)

    def syntax_policies(self, **actual_changes):
        baseline = source_definition.ProjectionPolicy(
            module_origins={"REF": "syntax"},
            identity_labels=frozenset({"a", "b", "c"}),
            identity_sorts=frozenset({"Expr"}), identity_names=frozenset({"REF"}),
        )
        values = dict(
            module_origins={"ACT": "syntax"},
            identity_labels=frozenset({"a", "b", "c"}),
            identity_sorts=frozenset({"Expr"}), identity_names=frozenset({"ACT"}),
            name_map={"ACT": "REF"},
        )
        values.update(actual_changes)
        return baseline, source_definition.ProjectionPolicy(**values)

    def test_split_priority_edges_equal_one_chain(self) -> None:
        baseline, actual = self.syntax_policies()
        result = source_definition.compare_definitions(
            definition("REF", priority([["a"], ["b"], ["c"]])),
            definition_with_sentences("ACT", [priority([["a"], ["b"]]), priority([["b"], ["c"]])]),
            baseline, actual,
        )
        self.assertEqual(result.sentence_count, 2)

    def test_split_priority_missing_edge_fails_closed(self) -> None:
        baseline, actual = self.syntax_policies()
        with self.assertRaisesRegex(source_definition.ProjectionError, "projection differs"):
            source_definition.compare_definitions(
                definition("REF", priority([["a"], ["b"], ["c"]])),
                definition("ACT", priority([["a"], ["b"]])), baseline, actual,
            )

    def test_one_explicit_redundant_sort_is_exact(self) -> None:
        baseline, actual = self.syntax_policies(
            redundant_sort_declarations=frozenset({"Expr"})
        )
        empty = {"node": "badsentence"}
        result = source_definition.compare_definitions(
            definition("REF", empty),
            definition_with_sentences("ACT", [empty, syntax_sort("Expr")]),
            baseline, actual,
        )
        self.assertEqual(result.sentence_count, 1)

    def test_redundant_sort_count_fails_closed(self) -> None:
        baseline, actual = self.syntax_policies(
            redundant_sort_declarations=frozenset({"Expr"})
        )
        empty = {"node": "badsentence"}
        with self.assertRaisesRegex(source_definition.ProjectionError, "redundant sort declarations differ"):
            source_definition.compare_definitions(
                definition("REF", empty),
                definition_with_sentences("ACT", [empty, syntax_sort("Expr"), syntax_sort("Expr")]),
                baseline, actual,
            )

    def test_strict_context_representation_requires_exact_heat_cool_witnesses(self) -> None:
        context = {
            "node": "KContext", "body": apply("strictFun", [apply("HOLE", [])]),
            "requires": apply("#Top", []), "att": {"node": "KAtt", "att": {}},
        }
        heat = rule("heat", "strictFun")
        cool = rule("cool", "strictFun")
        attributes = source_definition.DEFAULT_METADATA_ATTRIBUTES | {"label"}
        baseline_base = source_definition.ProjectionPolicy(
            module_origins={"REF": "imp"},
            identity_labels=frozenset({"strictFun", "HOLE", "heat", "cool", "#Top"}),
            identity_sorts=frozenset({"Int"}), identity_names=frozenset({"REF"}),
            known_attributes=attributes,
        )
        normalized = source_definition.project_definition(
            definition("REF", context), baseline_base
        )["origins"][0]["sentences"][0]
        baseline = source_definition.ProjectionPolicy(
            **{
                **baseline_base.__dict__,
                "ignored_sentence_sha256": {source_definition.digest(normalized): 1},
            }
        )
        actual = source_definition.ProjectionPolicy(
            module_origins={"ACT": "imp"},
            identity_labels=baseline.identity_labels,
            identity_sorts=baseline.identity_sorts,
            name_map={"ACT": "REF"}, known_attributes=attributes,
        )
        reference = definition_with_sentences("REF", [context, heat, cool])
        observed = definition_with_sentences("ACT", [heat, cool])
        self.assertEqual(
            source_definition.compare_definitions(reference, observed, baseline, actual).sentence_count,
            2,
        )
        mutated = copy.deepcopy(observed)
        mutated["term"]["modules"][0]["localSentences"].pop()
        with self.assertRaisesRegex(source_definition.ProjectionError, "projection differs"):
            source_definition.compare_definitions(reference, mutated, baseline, actual)

    def test_ignored_context_digest_and_count_fail_closed(self) -> None:
        context = {
            "node": "KContext", "body": apply("strictFun", [apply("HOLE", [])]),
            "requires": apply("#Top", []), "att": {"node": "KAtt", "att": {}},
        }
        policy = source_definition.ProjectionPolicy(
            module_origins={"REF": "imp"},
            identity_labels=frozenset({"strictFun", "HOLE", "#Top"}),
            identity_names=frozenset({"REF"}),
            ignored_sentence_sha256={"0" * 64: 1},
        )
        with self.assertRaisesRegex(source_definition.ProjectionError, "ignored sentence multiset differs"):
            source_definition.project_definition(definition("REF", context), policy)


class BehaviorTests(unittest.TestCase):
    def test_search_is_compared_as_a_set(self) -> None:
        policy = behavior.TermPolicy(
            identity_labels=frozenset({"#Or", "a", "b"}),
            identity_sorts=frozenset(),
        )
        first = behavior.normalize_term(apply("#Or", [apply("a", []), apply("b", [])]), policy)
        second = behavior.normalize_term(apply("#Or", [apply("b", []), apply("a", [])]), policy)
        self.assertEqual(behavior._search_set(first), behavior._search_set(second))

    def test_frozen_helpers_are_exact(self) -> None:
        root = Path(__file__).resolve().parents[3]
        self.assertEqual(set(behavior.load_frozen_helpers(root)), {"m3a", "m3b", "m3c", "m3d"})

    def test_hook_abort_precedes_secondary_wrapper_parse_error(self) -> None:
        stderr = (
            "[hook_INT_tdiv]: Division by zero: 1 / 0\n"
            "Could not parse backend result: parse error"
        )
        self.assertEqual(behavior._diagnostic_class(stderr), "hook")

    def test_unrelated_ambiguous_diagnostic_still_fails_closed(self) -> None:
        with self.assertRaisesRegex(behavior.BehaviorError, "ambiguous class"):
            behavior._diagnostic_class("scanner error followed by unexpected token")


def claim_spec(claim_label: str) -> dict[str, object]:
    variable = {"node": "KVariable", "name": "X", "sort": sort("Int")}
    claim = {
        "node": "KClaim",
        "body": {"node": "KRewrite", "lhs": variable, "rhs": copy.deepcopy(variable)},
        "requires": apply("#Top", []),
        "ensures": apply("#Top", []),
        "att": {"node": "KAtt", "att": {"label": claim_label}},
    }
    return {
        "format": "KAST",
        "version": 4,
        "term": {
            "node": "KFlatModuleList",
            "mainModule": "SPEC",
            "term": [
                {
                    "node": "KFlatModule",
                    "name": "SPEC",
                    "imports": [],
                    "localSentences": [claim],
                    "att": {"node": "KAtt", "att": {}},
                }
            ],
        },
    }


class ProofTests(unittest.TestCase):
    def test_actual_spec_imports_verification_only_identifier_syntax(self) -> None:
        source = run_proofs.actual_spec_source(Path("actual-execution.k"), "  claim body\n")
        self.assertEqual(
            source,
            'requires "actual-execution.k"\n'
            'requires "imp-verification.k"\n\n'
            "module KRS-M4-COMPLETE-IMP-SPEC\n"
            "  imports KRS-M4-COMPLETE-IMP\n"
            "  imports IMP-VERIFICATION-SYNTAX\n\n"
            "  claim body\n"
            "endmodule\n",
        )

    def policy(self) -> proofs.ProofPolicy:
        return proofs.ProofPolicy(
            identity_labels=frozenset({"SPEC.claim", "#Top"}),
            identity_sorts=frozenset({"Int"}),
            known_attributes=proofs.DEFAULT_METADATA_ATTRIBUTES | {"label"},
        )

    def test_proved_evidence_is_exact(self) -> None:
        case = proofs.ProofCase(
            "claim", Path("spec.k"), "SPEC", "SPEC.claim", proofs.ProofBounds(100, 64)
        )
        result = {"format": "KAST", "version": 4, "term": apply("#Top", [])}
        evidence = proofs.evidence_from_values(
            case=case,
            result_value=result,
            claim_value=claim_spec("SPEC.claim"),
            returncode=0,
            stderr="",
            user_labels=("step",),
            policy=self.policy(),
        )
        self.assertEqual(evidence.status, "proved")
        self.assertEqual(evidence.frontier_count, 0)

    def test_arbitrary_exit_one_is_not_incomplete(self) -> None:
        with self.assertRaisesRegex(proofs.ProofError, "unclassified proof termination"):
            proofs.classify(1, "someState", "unrelated backend error")

    def test_claim_priority_is_rejected(self) -> None:
        value = claim_spec("SPEC.claim")
        value["term"]["term"][0]["localSentences"][0]["att"]["att"]["priority"] = "50"
        policy = proofs.ProofPolicy(
            identity_labels=frozenset({"SPEC.claim", "#Top"}),
            identity_sorts=frozenset({"Int"}),
            known_attributes=proofs.DEFAULT_METADATA_ATTRIBUTES | {"label", "priority"},
        )
        with self.assertRaisesRegex(proofs.ProofError, "must not carry"):
            proofs.normalize_claim(value, "SPEC.claim", policy)


if __name__ == "__main__":
    unittest.main()
