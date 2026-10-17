"""Load the tour ledger and answer where each topic is taught today."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass
from pathlib import Path


PLAN = Path(__file__).resolve().parent
LEDGER = PLAN / "tour.toml"
# Evidence, fixture, and seed paths in the ledger are relative to the KRS directory.
KRS = PLAN.parents[1] / "krs"
LESSON_STATUSES = ("planned", "drafting", "in-review", "accepted")


@dataclass(frozen=True)
class Ledger:
    raw: dict

    @classmethod
    def load(cls) -> Ledger:
        with LEDGER.open("rb") as source:
            return cls(tomllib.load(source))

    def rows(self, table: str) -> list[dict]:
        return self.raw.get(table, [])

    def lesson(self, lesson_id: str) -> dict | None:
        return next((row for row in self.rows("lesson") if row["id"] == lesson_id), None)

    def concept_lesson(self, concept_id: str) -> dict | None:
        return next((row for row in self.rows("lesson") if concept_id in row.get("concepts", [])), None)

    def topic_lesson(self, topic: dict) -> dict | None:
        """The lesson that teaches a topic, or None for a reference or limitation topic."""

        if "concept" in topic:
            return self.concept_lesson(topic["concept"])
        if "lesson" in topic:
            return self.lesson(topic["lesson"])
        return None

    def destination(self, topic: dict) -> str:
        """Where a link to the topic goes: its lesson once accepted, otherwise its page."""

        lesson = self.topic_lesson(topic)
        if lesson is not None and lesson.get("status") == "accepted":
            return lesson["route"]
        return topic["page"]
