"""Contract tests for the committed reference-K output hygiene rule."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from verify import reference_output_problems


class ReferenceOutputTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def write(self, relative: str, text: str) -> str:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return relative

    def test_a_gate_reference_directory_is_rejected(self) -> None:
        relative = self.write("tests/imp-state/reference/oracle/kompile/definition.stdout", "")
        (problem,) = reference_output_problems([relative], root=self.root)
        self.assertIn("committed reference-K output", problem)

    def test_a_snapshot_manifest_is_rejected_anywhere(self) -> None:
        relative = self.write(
            "tests/example/stored/manifest.toml",
            'schema = 1\n\n[key]\nk_version = "7.1.337"\ntools = ["kast"]\n\n'
            '[[invocation]]\nlabel = "kast/x"\n',
        )
        (problem,) = reference_output_problems([relative], root=self.root)
        self.assertIn("committed reference snapshot manifest", problem)

    def test_other_reference_named_files_and_manifests_pass(self) -> None:
        files = [
            self.write("tests/imp/proof-pins/reference/pins.json", "{}\n"),
            self.write("browser/release/manifest.toml", 'schema = 1\n[key]\nname = "x"\n'),
            self.write("crates/krs/src/reference.rs", ""),
        ]
        self.assertEqual(reference_output_problems(files, root=self.root), [])


if __name__ == "__main__":
    unittest.main()
