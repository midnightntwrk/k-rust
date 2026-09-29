"""Contract tests for the Python K vocabulary hygiene rule."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from verify import PROTOCOL_CLIENT, k_vocabulary_problems, k_vocabulary_sites


class VocabularyTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def write(self, relative: str, source: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_comparison_and_kore_text_sites_outside_allowlist_fail(self) -> None:
        relative = "tests/example/verify.py"
        self.write(relative, 'if term.get("node") == "KApply":\n    pass\nvalue = "Lbl\'Unds\'"\n')
        problems = k_vocabulary_problems([relative], root=self.root, allowlist={})
        self.assertEqual(len(problems), 2)
        self.assertTrue(all("remove the K interpretation" in problem for problem in problems))

    def test_f_string_parts_and_whole_json_tags_are_inspected(self) -> None:
        source = 'value = f"Lbl\'Unds\'{name}"\nif node == "App":\n    pass\nprose = "String contents"\n'
        self.assertEqual(len(k_vocabulary_sites(source)), 2)

    def test_protocol_client_is_ignored(self) -> None:
        self.write(PROTOCOL_CLIENT, 'value = "KApply"\npattern = "Lbl\'Unds\'"\n')
        self.assertEqual(k_vocabulary_problems([PROTOCOL_CLIENT], root=self.root, allowlist={}), [])

    def test_allowlist_count_must_match_in_both_directions(self) -> None:
        relative = "tests/example/verify.py"
        self.write(relative, 'value = "KApply"\n')
        self.assertEqual(
            k_vocabulary_problems([relative], root=self.root, allowlist={relative: (1, "test fixture")}),
            [],
        )
        increased = k_vocabulary_problems([relative], root=self.root, allowlist={relative: (0, "test fixture")})
        reduced = k_vocabulary_problems([relative], root=self.root, allowlist={relative: (2, "test fixture")})
        self.assertIn("remove the added K interpretation", increased[0])
        self.assertIn("lower the allowlist count", reduced[0])

    def test_allowlisted_path_must_exist(self) -> None:
        relative = "tests/example/verify.py"
        allowlist = {relative: (1, "test fixture")}
        self.assertIn("no longer exists", k_vocabulary_problems([relative], root=self.root, allowlist=allowlist)[0])


if __name__ == "__main__":
    unittest.main()
