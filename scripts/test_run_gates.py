import contextlib
import io
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import run_gates

REGISTRY = """
[path-set]
krust = ['^crates/k-rust/src/']

[[gate]]
name = "compile"
run = "certification"
command = "scripts/compile.sh a"
paths = ["@krust", '^scripts/compile\\.sh$']

[[gate]]
name = "real"
run = "heavy"
host = "human-uid"
command = "scripts/real.sh"
paths = ["@krust"]

[[gate]]
name = "units"
run = "ci"
command = "scripts/units.sh"
paths = ['\\.py$']

[[gate]]
name = "weekly"
run = "weekly"
command = "scripts/compile.sh"

[[gate]]
name = "tool"
run = "on-demand"
command = "scripts/tool.sh"
"""


def names(selected):
    return [gate.name for gate, _ in selected]


class SelectionTest(unittest.TestCase):
    def setUp(self):
        self.gates = run_gates.parse(REGISTRY)

    def test_a_touched_path_selects_every_entry_whose_pattern_matches_it(self):
        self.assertEqual(names(run_gates.select(self.gates, touched=["crates/k-rust/src/a.rs"])),
                         ["compile", "real"])
        self.assertEqual(names(run_gates.select(self.gates, touched=["scripts/compile.sh"])),
                         ["compile"])
        self.assertEqual(names(run_gates.select(self.gates, touched=["README.md"])), [])

    def test_kinds_restrict_a_change_selection_and_alone_select_the_whole_kind(self):
        touched = ["crates/k-rust/src/a.rs", "scripts/x.py"]
        self.assertEqual(names(run_gates.select(self.gates, kinds=["heavy"], touched=touched)),
                         ["real"])
        self.assertEqual(names(run_gates.select(self.gates, kinds=["weekly", "on-demand"])),
                         ["weekly", "tool"])

    def test_a_named_entry_is_always_selected_and_an_unknown_name_fails(self):
        self.assertEqual(names(run_gates.select(self.gates, names=["tool"], touched=["README.md"])),
                         ["tool"])
        with self.assertRaises(KeyError) as raised:
            run_gates.select(self.gates, names=["tool", "kast-real"])
        self.assertEqual(raised.exception.args[0], ["kast-real"])

    def test_a_changed_registry_table_owes_its_entry(self):
        selected = run_gates.select(self.gates, touched=[], changed_entries={"weekly"})
        self.assertEqual(names(selected), ["weekly"])
        self.assertEqual(selected[0][1], "its registry entry changed")


class HostTest(unittest.TestCase):
    def test_a_host_uid_entry_is_recorded_as_not_run_in_a_sandbox_and_the_run_exits_3(self):
        real = next(gate for gate in run_gates.parse(REGISTRY) if gate.name == "real")
        with tempfile.TemporaryDirectory() as directory:
            with contextlib.redirect_stdout(io.StringIO()) as output:
                status = run_gates.run([(real, "named")], Path(directory), [], sandbox=True)
            summary = (Path(directory) / "summary.toml").read_text()
        self.assertEqual(status, 3)
        self.assertIn("real: not run: needs a host-UID run", output.getvalue())
        self.assertIn('status = "not-run"', summary)


class RegistryTest(unittest.TestCase):
    def problems(self, text):
        with self.assertRaises(run_gates.RegistryError) as raised:
            run_gates.parse(text)
        return str(raised.exception)

    def test_an_owed_entry_needs_paths_and_an_unowed_entry_has_none(self):
        self.assertIn("a certification entry needs `paths`",
                      self.problems('[[gate]]\nname = "a"\nrun = "certification"\ncommand = "x"\n'))
        self.assertIn("a weekly entry is not owed by a change",
                      self.problems('[[gate]]\nname = "a"\nrun = "weekly"\ncommand = "x"\npaths = ["y"]\n'))

    def test_every_malformed_part_is_reported(self):
        text = ('[[gate]]\nname = "A"\nrun = "nightly"\ncommand = "x"\nhost = "ci"\nwhen = 1\n'
                '[[gate]]\nname = "b"\nrun = "heavy"\ncommand = "x"\npaths = ["@none", "("]\n'
                '[[gate]]\nname = "b"\nrun = "ci"\ncommand = ""\n')
        problems = self.problems(text)
        for expected in ["name must be lowercase", "run `nightly`", "host `ci`", "unknown keys ['when']",
                         "no path-set `none`", "pattern '('", "gate b: name is not unique",
                         "`command` must be a non-empty string"]:
            self.assertIn(expected, problems)


class ChangedPathsTest(unittest.TestCase):
    """--changed compares the merge base with HEAD, in a scratch repository."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.repo = Path(self.directory.name)
        self.saved = run_gates.WORKSPACE
        run_gates.WORKSPACE = self.repo
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "test")
        self.write("scripts/gates.toml", REGISTRY)
        self.write("crates/k-rust/src/a.rs", "")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")

    def tearDown(self):
        run_gates.WORKSPACE = self.saved
        self.directory.cleanup()

    def git(self, *args):
        subprocess.run(["git", "-C", str(self.repo), *args], check=True, capture_output=True,
                       env={**os.environ, "GIT_CONFIG_GLOBAL": os.devnull})

    def write(self, path, text):
        (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / path).write_text(text)

    def test_deleted_renamed_and_registry_changes_are_seen_from_the_merge_base(self):
        self.git("checkout", "-q", "-b", "change")
        self.git("mv", "crates/k-rust/src/a.rs", "crates/k-rust/b.rs")
        self.write("scripts/gates.toml", REGISTRY.replace('command = "scripts/tool.sh"',
                                                         'command = "scripts/tool.sh --all"'))
        self.git("commit", "-qam", "change")
        self.git("checkout", "-q", "main")
        self.write("README.md", "later on main")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "main moves on")
        paths, entries = run_gates.changed_paths("main", "change")
        self.assertEqual(sorted(paths), ["crates/k-rust/b.rs", "crates/k-rust/src/a.rs",
                                         "scripts/gates.toml"])
        self.assertEqual(entries, {"tool"})


if __name__ == "__main__":
    unittest.main()
