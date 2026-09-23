#!/usr/bin/env python3
"""Validate the KRS language-tour curriculum ledger."""

from __future__ import annotations

import sys
import tomllib
import hashlib
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs-plan" / "tour.toml"


def fail(message: str) -> None:
    print(f"tour ledger: {message}", file=sys.stderr)
    raise SystemExit(1)


def duplicates(values: list[object]) -> list[object]:
    counts = Counter(values)
    return sorted(value for value, count in counts.items() if count > 1)


def main() -> None:
    with LEDGER.open("rb") as source:
        ledger = tomllib.load(source)

    if ledger.get("schema") != 1:
        fail("schema must be 1")

    chapters = ledger.get("chapter", [])
    concepts = ledger.get("concept", [])
    if not chapters or not concepts:
        fail("at least one chapter and concept are required")

    chapter_ids = [chapter.get("id") for chapter in chapters]
    chapter_orders = [chapter.get("order") for chapter in chapters]
    chapter_routes = [chapter.get("route") for chapter in chapters]
    concept_ids = [concept.get("id") for concept in concepts]
    for label, values in (
        ("chapter IDs", chapter_ids),
        ("chapter orders", chapter_orders),
        ("chapter routes", chapter_routes),
        ("concept IDs", concept_ids),
    ):
        repeated = duplicates(values)
        if repeated:
            fail(f"duplicate {label}: {repeated}")
    for route in chapter_routes:
        if not isinstance(route, str) or not route.startswith("/"):
            fail(f"chapter route must be an absolute site path: {route!r}")

    chapter_order = {
        chapter_id: order
        for chapter_id, order in zip(chapter_ids, chapter_orders, strict=True)
    }
    chapter_owners = {chapter["id"]: chapter.get("owner") for chapter in chapters}
    known_concepts = set(concept_ids)
    concept_by_id = {concept["id"]: concept for concept in concepts}
    statuses = set(ledger.get("status", {}))
    coverage_classes = set(ledger.get("coverage", {}))

    evidence_count = 0
    for concept in concepts:
        concept_id = concept.get("id")
        chapter_id = concept.get("chapter")
        if chapter_id not in chapter_order:
            fail(f"{concept_id}: unknown chapter {chapter_id!r}")
        if concept.get("status") not in statuses:
            fail(f"{concept_id}: unknown status {concept.get('status')!r}")
        if concept.get("coverage") not in coverage_classes:
            fail(f"{concept_id}: unknown coverage {concept.get('coverage')!r}")
        if concept.get("status") in {"current", "qualified"} and not chapter_owners.get(
            chapter_id
        ):
            fail(f"{concept_id}: current/qualified concept has no chapter owner")

        for prerequisite in concept.get("prerequisites", []):
            if prerequisite not in known_concepts:
                fail(f"{concept_id}: unknown prerequisite {prerequisite!r}")
            prerequisite_concept = concept_by_id[prerequisite]
            prerequisite_order = chapter_order[prerequisite_concept["chapter"]]
            if prerequisite_order > chapter_order[chapter_id]:
                fail(
                    f"{concept_id}: prerequisite {prerequisite!r} is taught "
                    "in a later chapter"
                )

        evidence = concept.get("evidence", [])
        if not evidence:
            fail(f"{concept_id}: at least one evidence path is required")
        for relative_path in evidence:
            evidence_count += 1
            if not (ROOT / relative_path).exists():
                fail(f"{concept_id}: missing evidence path {relative_path!r}")

    visiting: list[str] = []
    visited: set[str] = set()

    def visit(concept_id: str) -> None:
        if concept_id in visiting:
            start = visiting.index(concept_id)
            fail(f"prerequisite cycle: {' -> '.join(visiting[start:] + [concept_id])}")
        if concept_id in visited:
            return
        visiting.append(concept_id)
        for prerequisite in concept_by_id[concept_id].get("prerequisites", []):
            visit(prerequisite)
        visiting.pop()
        visited.add(concept_id)

    for concept_id in concept_ids:
        visit(concept_id)

    review = ledger.get("surface_review", {})
    status_payload = "".join(
        f"{concept['id']}={concept['status']}\n"
        for concept in sorted(concepts, key=lambda item: item["id"])
    )
    status_digest = hashlib.sha256(status_payload.encode()).hexdigest()
    if review.get("concept_status_sha256") != status_digest:
        fail(
            "concept statuses changed without refreshing the surface review; "
            f"expected concept_status_sha256 = {status_digest!r}"
        )

    for synthesis in ledger.get("synthesis", []):
        synthesis_id = synthesis.get("id")
        if synthesis.get("status") not in {"deferred", "published"}:
            fail(f"{synthesis_id}: synthesis status must be deferred or published")
        for concept_id in synthesis.get("requires", []):
            if concept_id not in known_concepts:
                fail(f"{synthesis_id}: unknown synthesis requirement {concept_id!r}")
            gloss = concept_by_id[concept_id].get("gloss")
            if not isinstance(gloss, str) or not gloss.strip():
                fail(f"{synthesis_id}: requirement {concept_id!r} needs a gloss")

    lessons = ledger.get("lesson", [])
    repeated = duplicates([lesson.get("id") for lesson in lessons])
    if repeated:
        fail(f"duplicate lesson IDs: {repeated}")
    for lesson in lessons:
        lesson_id = lesson.get("id")
        if lesson.get("status") not in {"deferred", "published"}:
            fail(f"{lesson_id}: lesson status must be deferred or published")
        route = lesson.get("route")
        if not isinstance(route, str) or not route.startswith("/"):
            fail(f"{lesson_id}: lesson route must be an absolute site path: {route!r}")
        fixture = ROOT / lesson.get("fixture", "")
        seed = ROOT / lesson.get("seed", "")
        if not fixture.is_file():
            fail(f"{lesson_id}: missing fixture {lesson.get('fixture')!r}")
        if not seed.is_file():
            fail(f"{lesson_id}: missing seed {lesson.get('seed')!r}")
        if seed.read_bytes() != fixture.read_bytes():
            fail(f"{lesson_id}: seed differs from its fixture; run `bun run sync:snippets`")

    print(
        f"tour ledger passed: {len(chapters)} chapters, "
        f"{len(concepts)} concepts, {len(lessons)} lessons, {evidence_count} evidence paths"
    )


if __name__ == "__main__":
    main()
