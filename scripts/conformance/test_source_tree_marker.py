"""The work-tree marker reads the K checkout it names, whatever repository the caller exports."""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import source_tree_marker


def commit_repository(path):
    environment = {
        **os.environ,
        "GIT_AUTHOR_NAME": "test",
        "GIT_AUTHOR_EMAIL": "test@example.invalid",
        "GIT_COMMITTER_NAME": "test",
        "GIT_COMMITTER_EMAIL": "test@example.invalid",
    }
    for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR"):
        environment.pop(name, None)
    path.mkdir(parents=True)
    subprocess.run(["git", "init", "-q", str(path)], check=True, env=environment)
    subprocess.run(
        ["git", "-C", str(path), "commit", "-q", "--allow-empty", "-m", path.name],
        check=True,
        env=environment,
    )
    return subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
        env=environment,
    ).stdout.strip()


class SourceTreeMarkerTests(unittest.TestCase):
    def test_exported_git_dir_does_not_replace_the_named_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            k_revision = commit_repository(root / "k")
            commit_repository(root / "caller")
            (root / "k" / "k-distribution").mkdir()
            exported = {"GIT_DIR": str(root / "caller" / ".git"), "GIT_WORK_TREE": str(root / "caller")}
            with mock.patch.dict(os.environ, exported):
                marker = source_tree_marker(root / "k" / "k-distribution")
            self.assertEqual(marker["revision"], k_revision)


if __name__ == "__main__":
    unittest.main()
