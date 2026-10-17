#!/usr/bin/env python3
"""Validate the tour curriculum ledger."""

from __future__ import annotations

import hashlib
import sys
from collections import Counter

from ledger import KRS, LESSON_STATUSES, Ledger


PAGE_DISPOSITIONS = ("split", "merged", "keep")


def fail(message: str) -> None:
    print(f"tour ledger: {message}", file=sys.stderr)
    raise SystemExit(1)


def duplicates(values: list[object]) -> list[object]:
    counts = Counter(values)
    return sorted(value for value, count in counts.items() if count > 1)


def require_unique(label: str, values: list[object]) -> None:
    repeated = duplicates(values)
    if repeated:
        fail(f"duplicate {label}: {repeated}")


def main() -> None:
    ledger = Ledger.load()
    if ledger.raw.get("schema") != 2:
        fail("schema must be 2")

    parts = ledger.rows("part")
    lessons = ledger.rows("lesson")
    concepts = ledger.rows("concept")
    pages = ledger.rows("page")
    topics = ledger.rows("topic")
    if not parts or not lessons or not concepts or not topics:
        fail("parts, lessons, concepts, and topics are required")

    require_unique("part IDs", [part.get("id") for part in parts])
    require_unique("part orders", [part.get("order") for part in parts])
    part_order = {part["id"]: part["order"] for part in parts}

    # Lessons: unique, in Part order, each K concept taught by exactly one lesson.
    require_unique("lesson IDs", [lesson.get("id") for lesson in lessons])
    require_unique("lesson orders", [lesson.get("order") for lesson in lessons])
    require_unique("lesson routes", [lesson.get("route") for lesson in lessons])
    concept_ids = [concept.get("id") for concept in concepts]
    require_unique("concept IDs", concept_ids)
    taught: list[str] = []
    previous_part = -1
    for lesson in sorted(lessons, key=lambda row: row["order"]):
        lesson_id = lesson["id"]
        if lesson.get("part") not in part_order:
            fail(f"{lesson_id}: unknown part {lesson.get('part')!r}")
        if part_order[lesson["part"]] < previous_part:
            fail(f"{lesson_id}: lesson order leaves its part's order")
        previous_part = part_order[lesson["part"]]
        if lesson.get("status") not in LESSON_STATUSES:
            fail(f"{lesson_id}: unknown status {lesson.get('status')!r}")
        route = lesson.get("route")
        if not isinstance(route, str) or not route.startswith("/"):
            fail(f"{lesson_id}: route must be an absolute site path: {route!r}")
        for concept_id in lesson.get("concepts", []):
            if concept_id not in concept_ids:
                fail(f"{lesson_id}: unknown concept {concept_id!r}")
        if (lesson["part"] == "krs") == bool(lesson.get("concepts")):
            fail(f"{lesson_id}: a K lesson teaches concepts and a side-track lesson teaches none")
        taught.extend(lesson.get("concepts", []))
    require_unique("concepts taught by more than one lesson", taught)
    untaught = sorted(set(concept_ids) - set(taught))
    if untaught:
        fail(f"concepts taught by no lesson: {untaught}")
    lesson_by_id = {lesson["id"]: lesson for lesson in lessons}

    # Pages that predate the spine: each stays until its replacing lessons are accepted.
    require_unique("page IDs", [page.get("id") for page in pages])
    require_unique("page orders", [page.get("order") for page in pages])
    page_routes = [page.get("route") for page in pages]
    require_unique("page routes", page_routes)
    collisions = sorted(set(page_routes) & {lesson["route"] for lesson in lessons})
    if collisions:
        fail(f"page routes reused by lessons: {collisions}")
    page_by_route = {page["route"]: page for page in pages}
    for page in pages:
        page_id = page["id"]
        disposition = page.get("disposition")
        replaced_by = page.get("replaced_by", [])
        if disposition not in PAGE_DISPOSITIONS:
            fail(f"{page_id}: unknown disposition {disposition!r}")
        if (disposition == "keep") == bool(replaced_by):
            fail(f"{page_id}: a kept page has no replacements and a split or merged page has some")
        for lesson_id in replaced_by:
            if lesson_id not in lesson_by_id:
                fail(f"{page_id}: unknown replacing lesson {lesson_id!r}")
        if not isinstance(page.get("retired"), bool):
            fail(f"{page_id}: retired must be true or false")
        if page["retired"]:
            pending = [lesson_id for lesson_id in replaced_by if lesson_by_id[lesson_id]["status"] != "accepted"]
            if disposition == "keep" or pending:
                fail(f"{page_id}: retired before its replacements were accepted: {pending}")

    # Topics: each belongs to a K concept, a side-track lesson, or a reference page.
    statuses = set(ledger.raw.get("status", {}))
    coverage_classes = set(ledger.raw.get("coverage", {}))
    topic_ids = [topic.get("id") for topic in topics]
    require_unique("topic IDs", topic_ids)
    topic_by_id = {topic["id"]: topic for topic in topics}
    evidence_count = 0
    for topic in topics:
        topic_id = topic["id"]
        coverage = topic.get("coverage")
        if topic.get("status") not in statuses:
            fail(f"{topic_id}: unknown status {topic.get('status')!r}")
        if coverage not in coverage_classes:
            fail(f"{topic_id}: unknown coverage {coverage!r}")
        page = page_by_route.get(topic.get("page"))
        if page is None:
            fail(f"{topic_id}: unknown page {topic.get('page')!r}")
        if coverage == "tour":
            if topic.get("concept") not in concept_ids or "lesson" in topic:
                fail(f"{topic_id}: a tour topic names one known concept and no lesson")
        elif coverage == "krs":
            lesson = lesson_by_id.get(topic.get("lesson"))
            if lesson is None or lesson["part"] != "krs" or "concept" in topic:
                fail(f"{topic_id}: a krs topic names one side-track lesson and no concept")
        elif "concept" in topic or "lesson" in topic or page["disposition"] != "keep":
            fail(f"{topic_id}: a {coverage} topic lives on a kept page and names no concept or lesson")
        if ledger.destination(topic) == page["route"] and page["retired"]:
            fail(f"{topic_id}: its page is retired but its lesson is not accepted")
        if topic.get("status") in {"current", "qualified"} and not page.get("owner"):
            fail(f"{topic_id}: current/qualified topic has no page owner")

        lesson = ledger.topic_lesson(topic)
        for prerequisite in topic.get("prerequisites", []):
            if prerequisite not in topic_by_id:
                fail(f"{topic_id}: unknown prerequisite {prerequisite!r}")
            required = topic_by_id[prerequisite]
            required_lesson = ledger.topic_lesson(required)
            if (
                coverage == "tour"
                and required.get("coverage") == "tour"
                and required_lesson["order"] > lesson["order"]
            ):
                fail(
                    f"{topic_id}: prerequisite {prerequisite!r} is taught in {required_lesson['id']}, "
                    f"after {lesson['id']}"
                )

        evidence = topic.get("evidence", [])
        if not evidence:
            fail(f"{topic_id}: at least one evidence path is required")
        for relative_path in evidence:
            evidence_count += 1
            if not (KRS / relative_path).exists():
                fail(f"{topic_id}: missing evidence path {relative_path!r}")

    visiting: list[str] = []
    visited: set[str] = set()

    def visit(topic_id: str) -> None:
        if topic_id in visiting:
            start = visiting.index(topic_id)
            fail(f"prerequisite cycle: {' -> '.join(visiting[start:] + [topic_id])}")
        if topic_id in visited:
            return
        visiting.append(topic_id)
        for prerequisite in topic_by_id[topic_id].get("prerequisites", []):
            visit(prerequisite)
        visiting.pop()
        visited.add(topic_id)

    for topic_id in topic_ids:
        visit(topic_id)

    review = ledger.raw.get("surface_review", {})
    status_payload = "".join(
        f"{topic['id']}={topic['status']}\n" for topic in sorted(topics, key=lambda item: item["id"])
    )
    status_digest = hashlib.sha256(status_payload.encode()).hexdigest()
    if review.get("topic_status_sha256") != status_digest:
        fail(
            "topic statuses changed without refreshing the surface review; "
            f"expected topic_status_sha256 = {status_digest!r}"
        )

    browser_lessons = ledger.rows("browser_lesson")
    require_unique("browser lesson IDs", [lesson.get("id") for lesson in browser_lessons])
    for lesson in browser_lessons:
        lesson_id = lesson.get("id")
        if lesson.get("status") not in {"deferred", "published"}:
            fail(f"{lesson_id}: browser lesson status must be deferred or published")
        route = lesson.get("route")
        if not isinstance(route, str) or not route.startswith("/"):
            fail(f"{lesson_id}: browser lesson route must be an absolute site path: {route!r}")
        fixture = KRS / lesson.get("fixture", "")
        seed = KRS / lesson.get("seed", "")
        if not fixture.is_file():
            fail(f"{lesson_id}: missing fixture {lesson.get('fixture')!r}")
        if not seed.is_file():
            fail(f"{lesson_id}: missing seed {lesson.get('seed')!r}")
        if seed.read_bytes() != fixture.read_bytes():
            fail(f"{lesson_id}: seed differs from its fixture; run `bun run sync:snippets`")

    accepted = sum(lesson["status"] == "accepted" for lesson in lessons)
    print(
        f"tour ledger passed: {len(parts)} parts, {len(lessons)} lessons ({accepted} accepted), "
        f"{len(concepts)} concepts, {len(topics)} topics, {len(pages)} pages, "
        f"{len(browser_lessons)} browser lessons, {evidence_count} evidence paths"
    )


if __name__ == "__main__":
    main()
