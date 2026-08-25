"""Fail-closed parsed/compiled KAST projection for complete IMP.

The M4 definition is intentionally flatter than upstream IMP.  Consequently
raw ``parsed.json`` equality is neither expected nor useful.  This module
projects both definitions into explicitly named semantic origins while
refusing to discard an unknown node, field, attribute, label, sort, or module.

The root M4 runner owns the concrete policy.  In particular it must provide
the complete label/sort tables and, for a flattened module, an origin for
every sentence that has no module-wide default.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


class ProjectionError(ValueError):
    """The input cannot be classified under the frozen projection policy."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


# Every supported KAST node has an exact set of allowed field sets.  Optional
# fields are represented as explicit variants, rather than silently accepted.
NODE_FIELDS: Mapping[str, frozenset[frozenset[str]]] = {
    # KAST JSON v4 cannot represent context aliases and emits this exact
    # sentinel.  Retain and count it; native KORE comparison covers its body.
    "badsentence": frozenset({frozenset({"node"})}),
    "KDefinition": frozenset({frozenset({"node", "mainModule", "modules", "att"})}),
    "KFlatModule": frozenset(
        {frozenset({"node", "name", "imports", "localSentences", "att"})}
    ),
    "KImport": frozenset({frozenset({"node", "name", "isPublic"})}),
    "KAtt": frozenset({frozenset({"node", "att"})}),
    "KProduction": frozenset(
        {
            frozenset({"node", "sort", "productionItems", "params", "att"}),
            frozenset({"node", "sort", "productionItems", "params", "klabel", "att"}),
        }
    ),
    "KSyntaxSort": frozenset({frozenset({"node", "sort", "params", "att"})}),
    "KSyntaxAssociativity": frozenset(
        {frozenset({"node", "assoc", "tags", "att"})}
    ),
    "KSyntaxPriority": frozenset(
        {frozenset({"node", "priorities", "att"})}
    ),
    "KNonTerminal": frozenset(
        {
            frozenset({"node", "sort"}),
            frozenset({"node", "name", "sort"}),
        }
    ),
    "KTerminal": frozenset({frozenset({"node", "value"})}),
    "KRegexTerminal": frozenset({frozenset({"node", "regex"})}),
    "KRule": frozenset(
        {frozenset({"node", "body", "requires", "ensures", "att"})}
    ),
    "KClaim": frozenset(
        {frozenset({"node", "body", "requires", "ensures", "att"})}
    ),
    "KContext": frozenset(
        {frozenset({"node", "body", "requires", "att"})}
    ),
    "KRewrite": frozenset({frozenset({"node", "lhs", "rhs"})}),
    "KApply": frozenset({frozenset({"node", "label", "args", "arity"})}),
    "KLabel": frozenset({frozenset({"node", "name", "params"})}),
    "KSort": frozenset({frozenset({"node", "name", "params"})}),
    "KToken": frozenset({frozenset({"node", "token", "sort"})}),
    "KVariable": frozenset(
        {
            frozenset({"node", "name"}),
            frozenset({"node", "name", "sort"}),
        }
    ),
    "KSequence": frozenset({frozenset({"node", "items", "arity"})}),
}


DEFAULT_METADATA_ATTRIBUTES = frozenset(
    {
        "org.kframework.attributes.Source",
        "org.kframework.attributes.Location",
        "org.kframework.definition.Production",
        "contentStartLine",
        "contentStartColumn",
        "digest",
        "productionID",
        "UNIQUE_ID",
        # Selected module/main names are layout.  Every referenced name is
        # still classified explicitly before this attribute is removed.
        "syntaxModule",
    }
)


@dataclass(frozen=True)
class ProjectionPolicy:
    """One side of a source-definition projection.

    ``module_origins`` enumerates every selected input module.  A ``None``
    origin means each sentence must occur in ``sentence_origins``.  Sentence
    keys may be either ``<module>::<identity>`` or the bare identity returned
    by :func:`sentence_identity`.

    All names are fail-closed: a name must occur in its explicit map or in the
    corresponding identity set.  ``imports_by_origin`` is an explicit semantic
    import projection used when layered and flattened source layouts differ.
    """

    module_origins: Mapping[str, str | None]
    sentence_origins: Mapping[str, str] = field(default_factory=dict)
    label_map: Mapping[str, str] = field(default_factory=dict)
    identity_labels: frozenset[str] = frozenset()
    sort_map: Mapping[str, str] = field(default_factory=dict)
    identity_sorts: frozenset[str] = frozenset()
    name_map: Mapping[str, str] = field(default_factory=dict)
    identity_names: frozenset[str] = frozenset()
    attribute_value_map: Mapping[str, Mapping[str, str]] = field(default_factory=dict)
    known_attributes: frozenset[str] = DEFAULT_METADATA_ATTRIBUTES
    metadata_attributes: frozenset[str] = DEFAULT_METADATA_ATTRIBUTES
    imports_by_origin: Mapping[str, tuple[str, ...]] = field(default_factory=dict)
    # Route-local support modules have no honest source-level counterpart on
    # the other route. They are selected and normalized like compared modules,
    # but attested against an exact per-file sentence multiset instead of being
    # mislabeled as equal or silently omitted.
    supplemental_module_origins: Mapping[str, str] = field(default_factory=dict)
    supplemental_imports_by_origin: Mapping[str, tuple[str, ...]] = field(
        default_factory=dict
    )
    supplemental_sentence_sha256: Mapping[str, int] = field(default_factory=dict)
    # Namespaces owned by the definition under test are closed: every module
    # in the KAST, and every import from a selected module, must be selected as
    # compared or supplemental. Toolchain modules outside these prefixes are
    # intentionally outside this source-definition projection.
    closed_module_prefixes: frozenset[str] = frozenset()
    # Rust-authored open sorts are emitted explicitly while the upstream K
    # grammar introduces the same sorts implicitly through productions.  Each
    # named declaration is removed only if it occurs exactly once.
    redundant_sort_declarations: frozenset[str] = frozenset()
    redundant_production_klabels: frozenset[str] = frozenset()
    joined_terminal_productions: frozenset[str] = frozenset()
    # Exact normalized sentence multiset removed on this route.  M4 uses this
    # only for the reference frontend's 27 strict-context declarations after
    # separately retaining and comparing their generated heat/cool rules.
    ignored_sentence_sha256: Mapping[str, int] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not self.module_origins:
            raise ProjectionError("module_origins must not be empty")
        if not self.metadata_attributes <= self.known_attributes:
            raise ProjectionError("every removable metadata attribute must be known")
        origins = {origin for origin in self.module_origins.values() if origin is not None}
        origins.update(self.sentence_origins.values())
        unknown = set(self.imports_by_origin) - origins
        if unknown:
            raise ProjectionError(f"imports declared for unknown origins: {sorted(unknown)}")
        overlap = set(self.module_origins) & set(self.supplemental_module_origins)
        if overlap:
            raise ProjectionError(
                f"modules cannot be both compared and supplemental: {sorted(overlap)}"
            )
        supplemental_origins = set(self.supplemental_module_origins.values())
        unknown = set(self.supplemental_imports_by_origin) - supplemental_origins
        if unknown:
            raise ProjectionError(
                f"supplemental imports declared for unknown origins: {sorted(unknown)}"
            )
        if any(not prefix for prefix in self.closed_module_prefixes):
            raise ProjectionError("closed module prefixes must be nonempty")


@dataclass(frozen=True)
class Comparison:
    baseline_sha256: str
    actual_sha256: str
    sentence_count: int


def _check_node_fields(node: Mapping[str, Any]) -> str:
    kind = node.get("node")
    if not isinstance(kind, str) or kind not in NODE_FIELDS:
        raise ProjectionError(f"unclassified KAST node {kind!r}")
    fields = frozenset(node)
    if fields not in NODE_FIELDS[kind]:
        raise ProjectionError(f"unknown {kind} fields: {sorted(fields)}")
    return kind


def _attribute_map(node: Mapping[str, Any]) -> Mapping[str, Any]:
    if node.get("node") != "KAtt" or set(node) != {"node", "att"}:
        raise ProjectionError("expected exact KAtt object")
    attributes = node["att"]
    if not isinstance(attributes, dict):
        raise ProjectionError("KAtt.att is not an object")
    return attributes


def sentence_identity(sentence: Mapping[str, Any]) -> str:
    """Return the stable lookup key used by explicit sentence-origin maps."""

    kind = _check_node_fields(sentence)
    if kind in {"KRule", "KClaim", "KContext"}:
        attributes = _attribute_map(sentence["att"])
        label = attributes.get("label")
        if isinstance(label, str) and label:
            return f"{kind}:label:{label}"
    if kind == "KProduction":
        klabel = sentence.get("klabel")
        if isinstance(klabel, dict) and klabel.get("node") == "KLabel":
            _check_node_fields(klabel)
            name = klabel.get("name")
            if isinstance(name, str):
                return f"KProduction:klabel:{name}"
    if kind in {"KSyntaxSort", "KProduction"}:
        sort = sentence.get("sort")
        if isinstance(sort, dict) and isinstance(sort.get("name"), str):
            return f"{kind}:sort:{sort['name']}:{digest(sentence)[:16]}"
    # Unlabelled grammar groups and generated rules still get an exact key.
    # Root must pin it when their enclosing module has no default origin.
    return f"{kind}:sha256:{digest(sentence)}"


class _Normalizer:
    def __init__(self, policy: ProjectionPolicy) -> None:
        self.policy = policy
        self.variables: dict[tuple[str, str, str], str] = {}

    @staticmethod
    def _mapped(
        value: str,
        mapping: Mapping[str, str],
        identities: frozenset[str],
        what: str,
    ) -> str:
        if value in mapping:
            return mapping[value]
        if value in identities:
            return value
        raise ProjectionError(f"unknown {what} {value!r}")

    def label(self, value: str) -> str:
        return self._mapped(
            value, self.policy.label_map, self.policy.identity_labels, "label"
        )

    def sort(self, value: str) -> str:
        return self._mapped(value, self.policy.sort_map, self.policy.identity_sorts, "sort")

    def name(self, value: str) -> str:
        return self._mapped(value, self.policy.name_map, self.policy.identity_names, "name")

    def attributes(self, value: Mapping[str, Any]) -> dict[str, Any]:
        unknown = set(value) - self.policy.known_attributes
        if unknown:
            raise ProjectionError(f"unknown attributes: {sorted(unknown)}")
        retained: dict[str, Any] = {}
        for name, child in value.items():
            if name in self.policy.metadata_attributes:
                continue
            # Attribute payloads are semantically retained.  KLabel/KSort
            # payloads are normalized; scalars/lists/maps remain exact.
            mapped_values = self.policy.attribute_value_map.get(name, {})
            if isinstance(child, str) and child in mapped_values:
                retained[name] = mapped_values[child]
            elif name in {"label", "bracketLabel", "element", "unit", "initializer"} and isinstance(child, str):
                retained[name] = self.label(child)
            elif name == "syntaxModule" and isinstance(child, str):
                retained[name] = self.name(child)
            else:
                retained[name] = self.visit(child, attribute_payload=True)
        return retained

    def variable(self, node: Mapping[str, Any]) -> dict[str, Any]:
        name = node["name"]
        if not isinstance(name, str):
            raise ProjectionError("KVariable.name is not a string")
        raw_sort = node.get("sort")
        if raw_sort is None:
            sort = "<unsorted>"
        else:
            if not isinstance(raw_sort, dict) or raw_sort.get("node") != "KSort":
                raise ProjectionError("KVariable.sort is not a KSort")
            sort = self.sort(raw_sort.get("name"))
        variable_kind = (
            "existential"
            if name.startswith("?")
            else "anonymous"
            if name.startswith("_")
            else "ordinary"
        )
        key = (name, variable_kind, sort)
        if key not in self.variables:
            self.variables[key] = f"{variable_kind[0].upper()}{len(self.variables)}"
        result: dict[str, Any] = {"node": "KVariable", "name": self.variables[key]}
        if raw_sort is not None:
            result["sort"] = self.visit(raw_sort)
        return result

    def visit(self, value: Any, *, attribute_payload: bool = False) -> Any:
        if isinstance(value, list):
            return [self.visit(child, attribute_payload=attribute_payload) for child in value]
        if not isinstance(value, dict):
            if isinstance(value, (str, int, bool)) or value is None:
                return value
            raise ProjectionError(f"unsupported scalar {value!r}")
        if "node" not in value:
            if not attribute_payload:
                raise ProjectionError(f"unclassified object fields: {sorted(value)}")
            return {
                key: self.visit(child, attribute_payload=True)
                for key, child in sorted(value.items())
            }

        kind = _check_node_fields(value)
        if kind == "KVariable":
            return self.variable(value)

        result: dict[str, Any] = {}
        for key, child in value.items():
            if kind == "KAtt" and key == "att":
                if not isinstance(child, dict):
                    raise ProjectionError("KAtt.att is not an object")
                result[key] = self.attributes(child)
            elif kind == "KLabel" and key == "name":
                if not isinstance(child, str):
                    raise ProjectionError("KLabel.name is not a string")
                result[key] = self.label(child)
            elif kind == "KSort" and key == "name":
                if not isinstance(child, str):
                    raise ProjectionError("KSort.name is not a string")
                result[key] = self.sort(child)
            elif kind == "KImport" and key == "name":
                if not isinstance(child, str):
                    raise ProjectionError("KImport.name is not a string")
                result[key] = self.name(child)
            else:
                result[key] = self.visit(child, attribute_payload=attribute_payload)

        if kind in {"KApply", "KSequence"}:
            items = result["args"] if kind == "KApply" else result["items"]
            if not isinstance(items, list) or result["arity"] != len(items):
                raise ProjectionError(f"invalid {kind} arity")
        if kind == "KSyntaxAssociativity":
            if not isinstance(result["tags"], list):
                raise ProjectionError("associativity tags are not a list")
            result["tags"] = [self.label(tag) for tag in result["tags"]]
            result["tags"].sort(key=canonical)
        if kind == "KSyntaxPriority":
            priorities = result["priorities"]
            if not isinstance(priorities, list) or not all(
                isinstance(group, list) for group in priorities
            ):
                raise ProjectionError("priority groups are not lists")
            for group in priorities:
                group[:] = [self.label(tag) for tag in group]
                group.sort(key=canonical)
        return result


def _exact_envelope(value: Mapping[str, Any]) -> Mapping[str, Any]:
    if set(value) != {"format", "version", "term"}:
        raise ProjectionError(f"unexpected KAST envelope fields: {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ProjectionError("definition is not exactly KAST v4")
    term = value["term"]
    if not isinstance(term, dict) or term.get("node") != "KDefinition":
        raise ProjectionError("definition envelope does not contain KDefinition")
    _check_node_fields(term)
    return term


def load_definition(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ProjectionError(f"cannot read {path}: {error}") from error
    if not isinstance(value, dict):
        raise ProjectionError(f"{path} does not contain an object")
    _exact_envelope(value)
    return value


def project_definition(
    definition: Mapping[str, Any], policy: ProjectionPolicy
) -> dict[str, Any]:
    """Project one KAST definition according to a complete explicit policy."""

    term = _exact_envelope(definition)
    modules = term["modules"]
    if not isinstance(modules, list):
        raise ProjectionError("KDefinition.modules is not a list")
    selected_modules = set(policy.module_origins) | set(
        policy.supplemental_module_origins
    )
    matches: dict[str, Mapping[str, Any]] = {}
    all_module_names: set[str] = set()
    for module in modules:
        if not isinstance(module, dict) or module.get("node") != "KFlatModule":
            raise ProjectionError("KDefinition contains a non-KFlatModule")
        _check_node_fields(module)
        name = module.get("name")
        if not isinstance(name, str):
            raise ProjectionError("KFlatModule.name is not a string")
        if name in all_module_names:
            raise ProjectionError(f"duplicate definition module {name!r}")
        all_module_names.add(name)
        if name in selected_modules:
            if name in matches:
                raise ProjectionError(f"duplicate selected module {name!r}")
            matches[name] = module
        elif any(name.startswith(prefix) for prefix in policy.closed_module_prefixes):
            raise ProjectionError(
                f"unclassified closed-namespace module {name!r}"
            )
    missing = selected_modules - set(matches)
    if missing:
        raise ProjectionError(f"selected modules are absent: {sorted(missing)}")

    definition_attributes = _Normalizer(policy).visit(copy.deepcopy(term["att"]))["att"]
    # mainModule is layout, not a semantic sentence, but it must still be an
    # explicitly classified name so a renamed/unknown project module cannot
    # disappear through projection.
    _Normalizer(policy).name(term["mainModule"])

    grouped: dict[str, list[Any]] = {}
    redundant_sorts = Counter()
    redundant_klabels = Counter()
    joined_terminals = Counter()
    ignored_sentences = Counter()
    supplemental_sentences = Counter()
    supplemental_evidence: list[dict[str, Any]] = []
    actual_imports: dict[str, set[str]] = {}
    actual_attributes: dict[str, list[dict[str, Any]]] = {}
    for module_name, module in matches.items():
        supplemental = module_name in policy.supplemental_module_origins
        default_origin = (
            policy.supplemental_module_origins[module_name]
            if supplemental
            else policy.module_origins[module_name]
        )
        imports = module["imports"]
        sentences = module["localSentences"]
        if not isinstance(imports, list) or not isinstance(sentences, list):
            raise ProjectionError(f"module {module_name!r} has invalid collections")
        module_attributes = _Normalizer(policy).visit(copy.deepcopy(module["att"]))["att"]
        if module_attributes:
            if supplemental:
                raise ProjectionError(
                    f"supplemental module {module_name!r} has unpinned semantic attributes"
                )
            if default_origin is None:
                raise ProjectionError(
                    f"module {module_name!r} has semantic attributes but no module origin"
                )
            actual_attributes.setdefault(default_origin, []).append(module_attributes)

        for sentence in sentences:
            if not isinstance(sentence, dict):
                raise ProjectionError(f"module {module_name!r} contains a non-object sentence")
            identity = sentence_identity(sentence)
            origin = policy.sentence_origins.get(
                f"{module_name}::{identity}", policy.sentence_origins.get(identity, default_origin)
            )
            if origin is None:
                raise ProjectionError(
                    f"sentence {module_name}::{identity} has no explicit semantic origin"
                )
            sentence = copy.deepcopy(sentence)
            if sentence.get("node") == "KSyntaxSort":
                sort = sentence.get("sort", {}).get("name")
                if sort in policy.redundant_sort_declarations:
                    redundant_sorts[sort] += 1
                    continue
            if sentence.get("node") == "KProduction" and "klabel" in sentence:
                klabel = sentence["klabel"].get("name")
                if klabel in policy.joined_terminal_productions:
                    items = sentence.get("productionItems")
                    expected = [
                        {"node": "KTerminal", "value": "#"},
                        {"node": "KTerminal", "value": klabel},
                    ]
                    if not isinstance(items, list) or items[:2] != expected:
                        raise ProjectionError(
                            f"joined-terminal production shape differs: {klabel!r}"
                        )
                    sentence["productionItems"] = [
                        {"node": "KTerminal", "value": f"#{klabel}"}, *items[2:]
                    ]
                    joined_terminals[klabel] += 1
                if klabel in policy.redundant_production_klabels:
                    redundant_klabels[klabel] += 1
                    del sentence["klabel"]
            normalizer = _Normalizer(policy)
            normalized_sentence = normalizer.visit(sentence)
            normalized_digest = digest(normalized_sentence)
            if supplemental:
                supplemental_sentences[normalized_digest] += 1
                continue
            if ignored_sentences[normalized_digest] < policy.ignored_sentence_sha256.get(
                normalized_digest, 0
            ):
                ignored_sentences[normalized_digest] += 1
                continue
            if normalized_sentence.get("node") == "KSyntaxPriority":
                priorities = normalized_sentence["priorities"]
                # K accepts one long chain or multiple adjacent two-group
                # sentences.  Compare the exact directed adjacent edges.
                for higher, lower in zip(priorities, priorities[1:]):
                    grouped.setdefault(origin, []).append(
                        {
                            "node": "KRS-M4-SyntaxPriorityEdge",
                            "higher": higher,
                            "lower": lower,
                            "att": normalized_sentence["att"],
                        }
                    )
            else:
                grouped.setdefault(origin, []).append(normalized_sentence)

        normalized_module_imports: set[str] = set()
        for imported in imports:
            imported_name = imported.get("name") if isinstance(imported, dict) else None
            if (
                isinstance(imported_name, str)
                and any(
                    imported_name.startswith(prefix)
                    for prefix in policy.closed_module_prefixes
                )
                and imported_name not in selected_modules
            ):
                raise ProjectionError(
                    f"module {module_name!r} imports unclassified "
                    f"closed-namespace module {imported_name!r}"
                )
            normalized = _Normalizer(policy).visit(copy.deepcopy(imported))
            visibility = "public" if normalized["isPublic"] else "private"
            normalized_module_imports.add(f"{normalized['name']}:{visibility}")
        if supplemental:
            expected_imports = set(
                policy.supplemental_imports_by_origin.get(default_origin, ())
            )
            if normalized_module_imports != expected_imports:
                raise ProjectionError(
                    f"supplemental module {module_name!r} imports differ: "
                    f"expected={sorted(expected_imports)}, "
                    f"actual={sorted(normalized_module_imports)}"
                )
            supplemental_evidence.append(
                {
                    "module": module_name,
                    "origin": default_origin,
                    "imports": sorted(normalized_module_imports),
                }
            )
        elif default_origin is not None:
            actual_imports.setdefault(default_origin, set()).update(
                normalized_module_imports
            )
        elif normalized_module_imports and not policy.imports_by_origin:
            raise ProjectionError(
                f"module {module_name!r} has imports but no origin/import projection"
            )

    expected_redundant = Counter({name: 1 for name in policy.redundant_sort_declarations})
    if redundant_sorts != expected_redundant:
        raise ProjectionError(
            f"redundant sort declarations differ: expected={expected_redundant}, actual={redundant_sorts}"
        )
    expected_klabels = Counter({name: 1 for name in policy.redundant_production_klabels})
    if redundant_klabels != expected_klabels:
        raise ProjectionError(
            f"redundant production klabels differ: expected={expected_klabels}, actual={redundant_klabels}"
        )
    expected_joined = Counter({name: 1 for name in policy.joined_terminal_productions})
    if joined_terminals != expected_joined:
        raise ProjectionError(
            f"joined terminal productions differ: expected={expected_joined}, actual={joined_terminals}"
        )
    expected_ignored = Counter(policy.ignored_sentence_sha256)
    if ignored_sentences != expected_ignored:
        raise ProjectionError(
            f"ignored sentence multiset differs: expected={expected_ignored}, actual={ignored_sentences}"
        )
    expected_supplemental = Counter(policy.supplemental_sentence_sha256)
    if supplemental_sentences != expected_supplemental:
        raise ProjectionError(
            "supplemental sentence multiset differs: "
            f"expected={expected_supplemental}, actual={supplemental_sentences}"
        )

    origins = set(grouped)
    origins.update(policy.imports_by_origin)
    projected: list[dict[str, Any]] = []
    for origin in sorted(origins):
        sentences = sorted(grouped.get(origin, []), key=canonical)
        if origin in policy.imports_by_origin:
            imports = sorted(set(policy.imports_by_origin[origin]))
        else:
            imports = sorted(actual_imports.get(origin, set()))
        projected.append(
            {
                "origin": origin,
                "attributes": sorted(actual_attributes.get(origin, []), key=canonical),
                "imports": imports,
                "sentences": sentences,
            }
        )
    return {
        "format": "KRS-M4-KAST-PROJECTION",
        "version": 1,
        "definitionAttributes": definition_attributes,
        "origins": projected,
        "supplementalModules": sorted(supplemental_evidence, key=canonical),
        "supplementalSentenceSha256": dict(sorted(supplemental_sentences.items())),
    }


def _multiset_difference(
    baseline: Mapping[str, Any], actual: Mapping[str, Any]
) -> str:
    expected = Counter(
        (origin["origin"], canonical(sentence))
        for origin in baseline["origins"]
        for sentence in origin["sentences"]
    )
    observed = Counter(
        (origin["origin"], canonical(sentence))
        for origin in actual["origins"]
        for sentence in origin["sentences"]
    )
    missing = expected - observed
    extra = observed - expected
    summary = {
        "missing": [
            {"origin": origin, "count": count, "sentence": json.loads(sentence)}
            for (origin, sentence), count in list(missing.items())[:3]
        ],
        "extra": [
            {"origin": origin, "count": count, "sentence": json.loads(sentence)}
            for (origin, sentence), count in list(extra.items())[:3]
        ],
    }
    return canonical(summary)


def compare_definitions(
    baseline: Mapping[str, Any],
    actual: Mapping[str, Any],
    baseline_policy: ProjectionPolicy,
    actual_policy: ProjectionPolicy,
    compatible_sentence_pairs: list[Mapping[str, Any]] | None = None,
) -> Comparison:
    expected = project_definition(baseline, baseline_policy)
    observed = project_definition(actual, actual_policy)
    pairs = compatible_sentence_pairs or []
    expected_layout = copy.deepcopy(expected)
    observed_layout = copy.deepcopy(observed)
    for projection in (expected_layout, observed_layout):
        # Route-local supplemental modules are independently exact-attested by
        # their policy and intentionally have no cross-route counterpart.
        projection.pop("supplementalModules")
        projection.pop("supplementalSentenceSha256")
        for origin in projection["origins"]:
            origin["sentences"] = []
    if expected_layout != observed_layout:
        raise ProjectionError("source-definition non-sentence projection differs")

    expected_sentences = Counter(
        (origin["origin"], canonical(sentence))
        for origin in expected["origins"]
        for sentence in origin["sentences"]
    )
    observed_sentences = Counter(
        (origin["origin"], canonical(sentence))
        for origin in observed["origins"]
        for sentence in origin["sentences"]
    )
    for index, pair in enumerate(pairs):
        if set(pair) != {"origin", "reference_sha256", "actual_sha256", "count"}:
            raise ProjectionError(f"compatible sentence pair {index} has unknown fields")
        origin = pair["origin"]
        reference_digest = pair["reference_sha256"]
        actual_digest = pair["actual_sha256"]
        count = pair["count"]
        if (
            not isinstance(origin, str)
            or not isinstance(reference_digest, str)
            or len(reference_digest) != 64
            or not isinstance(actual_digest, str)
            or len(actual_digest) != 64
            or not isinstance(count, int)
            or isinstance(count, bool)
            or count <= 0
        ):
            raise ProjectionError(f"compatible sentence pair {index} is malformed")

        def exact_key(counter: Counter[tuple[str, str]], wanted: str) -> tuple[str, str]:
            matches = [
                key for key, available in counter.items()
                if available and key[0] == origin and digest(json.loads(key[1])) == wanted
            ]
            if len(matches) != 1 or counter[matches[0]] < count:
                raise ProjectionError(
                    f"compatible sentence pair {index} has no exact count-{count} witness"
                )
            return matches[0]

        expected_sentences[exact_key(expected_sentences, reference_digest)] -= count
        observed_sentences[exact_key(observed_sentences, actual_digest)] -= count

    expected_sentences += Counter()
    observed_sentences += Counter()
    if expected_sentences != observed_sentences:
        raise ProjectionError(
            "source-definition projection differs: "
            + _multiset_difference(expected, observed)
        )
    count = sum(len(origin["sentences"]) for origin in expected["origins"])
    return Comparison(digest(expected), digest(observed), count)


def compare_parsed_and_compiled(
    baseline_directory: Path,
    actual_directory: Path,
    baseline_policy: ProjectionPolicy,
    actual_policy: ProjectionPolicy,
) -> Mapping[str, Comparison]:
    """Compare both required K frontend boundaries, failing at the first one."""

    result: dict[str, Comparison] = {}
    for filename in ("parsed.json", "compiled.json"):
        result[filename] = compare_definitions(
            load_definition(baseline_directory / filename),
            load_definition(actual_directory / filename),
            baseline_policy,
            actual_policy,
        )
    return result
