"""Tests of scripts/repo_hygiene.py on seeded trees."""
import tempfile
import unittest
from pathlib import Path

import repo_hygiene

SLASH = "/"
DRAFT = "draft" + SLASH
PERSONAL = "draft-personal" + SLASH


class RepoHygieneTest(unittest.TestCase):
    def tree(self, files):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for relative, content in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content if isinstance(content, bytes) else content.encode())
        return root

    def run_check(self, files, allowed=None):
        root = self.tree(files)
        return repo_hygiene.problems(sorted(files), root=root, allowed=allowed or {}, exempt={})

    def test_a_tracked_file_in_a_scratchpad_directory_is_refused(self):
        found = self.run_check({DRAFT + "notes.md": "x\n", "krs/" + DRAFT + "a.md": "x\n",
                                PERSONAL + "b.toml": "x\n"})
        self.assertEqual(len(found), 3, found)
        self.assertTrue(all("tracked file under a draft" in problem for problem in found), found)

    def test_a_reference_to_a_scratchpad_path_is_refused(self):
        found = self.run_check({
            "a.md": f"see `{DRAFT}tasks/README.md`\n",
            "b.rs": f"// {PERSONAL}perf/measure.md\n",
            "c.toml": f'origin = "{DRAFT}x"\n',
            "d.md": f"krs/{DRAFT}notes\n",
            "e.rs": 'root.join("draft").join("x");\n',
            "f.rs": "main.join('draft-personal')\n",
        })
        self.assertEqual([problem.split(":")[0] for problem in found],
                         ["a.md", "b.rs", "c.toml", "d.md", "e.rs", "f.rs"])
        self.assertIn("a.md:1: names a scratchpad path", found[0])

    def test_names_that_only_contain_the_word_are_not_references(self):
        found = self.run_check({
            "bun.lock": '"@open-draft/deferred-promise": ["@open-draft/x"]\n',
            "a.md": "ajv-draft-04/schema, my_draft/x, .draft/x, a draft of the plan\n",
            "docs/drafting/notes.md": "x\n",
            "binary.bin": b"\0" + DRAFT.encode(),
        })
        self.assertEqual(found, [])

    def test_an_allowed_line_passes_and_a_stale_allowance_is_a_finding(self):
        allowed = {(".gitignore", SLASH + DRAFT): "ignore rule",
                   (".gitignore", SLASH + PERSONAL): "ignore rule"}
        found = self.run_check({".gitignore": f"target/\n{SLASH}{DRAFT}\n"}, allowed)
        self.assertEqual(len(found), 1, found)
        self.assertIn("no longer occurs", found[0])

    def test_an_exempt_file_may_name_a_path_but_not_lie_in_a_scratchpad(self):
        files = {"check.py": f"PATTERN = '{DRAFT}'\n", DRAFT + "check.py": "x\n"}
        root = self.tree(files)
        exempt = {"check.py": "spells the pattern", DRAFT + "check.py": "never applies",
                  "gone.py": "removed"}
        found = repo_hygiene.problems(sorted(files), root=root, allowed={}, exempt=exempt)
        self.assertEqual(len(found), 2, found)
        self.assertIn("tracked file under a draft directory", found[0])
        self.assertIn("gone.py: exempt file is not tracked", found[1])


if __name__ == "__main__":
    unittest.main()
