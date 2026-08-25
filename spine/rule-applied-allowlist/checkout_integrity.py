#!/usr/bin/env python3
"""Exact clean implementation-checkout gate for the final R3-G-05 cycle."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import tempfile
from pathlib import Path


COMMIT_ID = re.compile(r"[0-9a-f]{40}")


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def git(repository: Path, *arguments: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", *arguments], cwd=repository, check=check,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )


def verify_checkout(repository: Path, requested_head: str, activation: str) -> str:
    repository = repository.resolve(strict=True)
    if COMMIT_ID.fullmatch(requested_head) is None:
        fail("implementation head must be an exact lowercase 40-hex commit ID")
    if COMMIT_ID.fullmatch(activation) is None:
        fail("repair activation must be an exact lowercase 40-hex commit ID")
    try:
        current_head = git(repository, "rev-parse", "HEAD").stdout.decode("ascii").strip()
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError) as error:
        fail(f"cannot resolve implementation checkout HEAD: {error}")
    if current_head != requested_head:
        fail("requested implementation head does not equal checkout HEAD")
    if git(repository, "cat-file", "-e", f"{requested_head}^{{commit}}", check=False).returncode:
        fail("implementation head does not name an existing commit object")
    if git(repository, "merge-base", "--is-ancestor", activation, requested_head,
           check=False).returncode:
        fail("required R3-G-05 activation is not an ancestor of the implementation head")
    if git(repository, "diff", "--cached", "--quiet", "--", check=False).returncode:
        fail("implementation checkout has staged changes")
    if git(repository, "diff", "--quiet", "--", check=False).returncode:
        fail("implementation checkout has tracked worktree changes")
    untracked = git(
        repository, "ls-files", "-z", "--others", "--exclude-standard").stdout
    if untracked:
        first = os.fsdecode(untracked.split(b"\0", 1)[0])
        fail(f"implementation checkout has an untracked non-ignored path: {first}")
    return requested_head


def initialize_repository(path: Path) -> str:
    git(path, "init", "--quiet")
    git(path, "config", "user.name", "R3-G-05N self-test")
    git(path, "config", "user.email", "r3-g-05m@example.invalid")
    (path / ".gitignore").write_text("ignored/\n", encoding="utf-8")
    (path / "tracked.txt").write_text("clean\n", encoding="utf-8")
    git(path, "add", ".gitignore", "tracked.txt")
    git(path, "commit", "--quiet", "-m", "synthetic activation")
    return git(path, "rev-parse", "HEAD").stdout.decode("ascii").strip()


def require_refusal(repository: Path, head: str, activation: str, witness: str) -> None:
    try:
        verify_checkout(repository, head, activation)
    except SystemExit as error:
        if witness not in str(error):
            raise AssertionError(
                f"checkout refusal lacked {witness!r}: {error}") from error
    else:
        raise AssertionError(f"dirty checkout was accepted: {witness}")
    if (repository / "cycle-5-r3-g-05n").exists():
        raise AssertionError("checkout refusal reserved the cycle-5 output")


def self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="r3-g-05m-checkout-") as directory:
        repository = Path(directory)
        head = initialize_repository(repository)
        if verify_checkout(repository, head, head) != head:
            raise AssertionError("clean exact implementation checkout was rejected")

        require_refusal(repository, "0" * 40, head, "does not equal checkout HEAD")

        tracked = repository / "tracked.txt"
        tracked.write_text("dirty\n", encoding="utf-8")
        require_refusal(repository, head, head, "tracked worktree changes")
        tracked.write_text("clean\n", encoding="utf-8")

        tracked.write_text("staged\n", encoding="utf-8")
        git(repository, "add", "tracked.txt")
        tracked.write_text("staged\n", encoding="utf-8")
        require_refusal(repository, head, head, "staged changes")
        git(repository, "reset", "--quiet", "HEAD", "--", "tracked.txt")
        tracked.write_text("clean\n", encoding="utf-8")

        untracked = repository / "untracked.txt"
        untracked.write_text("untracked\n", encoding="utf-8")
        require_refusal(repository, head, head, "untracked non-ignored path")
        untracked.unlink()

        ignored = repository / "ignored" / "raw-output"
        ignored.parent.mkdir()
        ignored.write_text("provenance\n", encoding="utf-8")
        if verify_checkout(repository, head, head) != head:
            raise AssertionError("ignored raw/build output made the checkout dirty")
    print("R3-G-05N exact clean implementation checkout self-test: pass")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("verify", "self-test"))
    parser.add_argument("repository", nargs="?", type=Path)
    parser.add_argument("requested_head", nargs="?")
    parser.add_argument("activation", nargs="?")
    args = parser.parse_args()
    if args.action == "self-test":
        self_test()
        return
    if args.repository is None or args.requested_head is None or args.activation is None:
        fail("usage: checkout_integrity.py verify REPOSITORY IMPLEMENTATION_HEAD ACTIVATION")
    print(verify_checkout(args.repository, args.requested_head, args.activation))


if __name__ == "__main__":
    main()
