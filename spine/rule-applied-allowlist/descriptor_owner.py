#!/usr/bin/env python3
"""Generation- and inode-bound paths for nested R3-G-05 subprocesses."""

from __future__ import annotations

import argparse
import os
import stat
from pathlib import Path
from typing import Callable, NamedTuple


class DescriptorOwnerError(RuntimeError):
    pass


class ProcessGeneration(NamedTuple):
    start_time: int
    state: str


class DescriptorProof(NamedTuple):
    owner_path: Path
    device: int
    inode: int


GenerationReader = Callable[[int], ProcessGeneration | None]


def process_generation(pid: int) -> ProcessGeneration | None:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        fields = raw[raw.rfind(")") + 2:].split()
        return ProcessGeneration(start_time=int(fields[19]), state=fields[0])
    except (FileNotFoundError, PermissionError, IndexError, ValueError, ProcessLookupError):
        return None


def owner_descriptor_path(owner_pid: int, owner_fd: int) -> Path:
    if type(owner_pid) is not int or owner_pid <= 0:
        raise DescriptorOwnerError("descriptor owner PID is invalid")
    if type(owner_fd) is not int or owner_fd < 0:
        raise DescriptorOwnerError("descriptor owner FD is invalid")
    return Path(f"/proc/{owner_pid}/fd/{owner_fd}")


def immediate_descriptor_path(immediate_fd: int) -> Path:
    if type(immediate_fd) is not int or immediate_fd < 0:
        raise DescriptorOwnerError("immediate output FD is invalid")
    return Path(f"/proc/self/fd/{immediate_fd}")


def descriptor_is_open(fd: int) -> bool:
    try:
        os.fstat(fd)
        return True
    except OSError:
        return False


def verify_owner_descriptor(
    owner_pid: int,
    owner_start_time: int,
    owner_fd: int,
    immediate_fd: int,
    expected_device: int,
    expected_inode: int,
    *,
    generation_reader: GenerationReader = process_generation,
) -> DescriptorProof:
    """Double-check one live owner generation and both descriptor spellings."""
    if type(owner_start_time) is not int or owner_start_time <= 0:
        raise DescriptorOwnerError("descriptor owner generation is invalid")
    if (type(expected_device) is not int or expected_device < 0
            or type(expected_inode) is not int or expected_inode <= 0):
        raise DescriptorOwnerError("expected output identity is invalid")
    owner_path = owner_descriptor_path(owner_pid, owner_fd)
    immediate_path = immediate_descriptor_path(immediate_fd)
    before = generation_reader(owner_pid)
    if (before is None or before.start_time != owner_start_time
            or before.state in ("Z", "T", "t")):
        raise DescriptorOwnerError("descriptor owner generation is not live")
    try:
        opened = os.fstat(immediate_fd)
        immediate = os.stat(immediate_path, follow_symlinks=True)
        owner_before = os.stat(owner_path, follow_symlinks=True)
    except OSError as error:
        raise DescriptorOwnerError("descriptor path is unavailable") from error
    after = generation_reader(owner_pid)
    if (after is None or after.start_time != before.start_time
            or after.start_time != owner_start_time
            or after.state in ("Z", "T", "t")):
        raise DescriptorOwnerError("descriptor owner generation changed during verification")
    try:
        owner_after = os.stat(owner_path, follow_symlinks=True)
    except OSError as error:
        raise DescriptorOwnerError("descriptor owner path disappeared during verification") from error
    identities = {
        (opened.st_dev, opened.st_ino),
        (immediate.st_dev, immediate.st_ino),
        (owner_before.st_dev, owner_before.st_ino),
        (owner_after.st_dev, owner_after.st_ino),
        (expected_device, expected_inode),
    }
    if len(identities) != 1 or not stat.S_ISDIR(opened.st_mode):
        raise DescriptorOwnerError("descriptor owner path identity mismatch")
    return DescriptorProof(owner_path, opened.st_dev, opened.st_ino)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="action", required=True)
    generation = subparsers.add_parser("generation")
    generation.add_argument("pid", type=int)
    verify = subparsers.add_parser("verify")
    verify.add_argument("owner_pid", type=int)
    verify.add_argument("owner_start_time", type=int)
    verify.add_argument("owner_fd", type=int)
    verify.add_argument("immediate_fd", type=int)
    verify.add_argument("expected_device", type=int)
    verify.add_argument("expected_inode", type=int)
    args = parser.parse_args()
    if args.action == "generation":
        value = process_generation(args.pid)
        if value is None or value.state in ("Z", "T", "t"):
            raise SystemExit("process generation is not live")
        print(value.start_time)
        return
    try:
        proof = verify_owner_descriptor(
            args.owner_pid, args.owner_start_time, args.owner_fd,
            args.immediate_fd, args.expected_device, args.expected_inode)
    except DescriptorOwnerError as error:
        raise SystemExit(str(error)) from error
    print(proof.owner_path)


if __name__ == "__main__":
    main()
