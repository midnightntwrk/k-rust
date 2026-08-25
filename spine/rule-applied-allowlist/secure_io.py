#!/usr/bin/env python3
"""Descriptor-relative, no-follow filesystem primitives for R3-G-05."""

from __future__ import annotations

import json
import os
import secrets
import stat
from pathlib import Path
from typing import Any


DIRECTORY_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW


class SecureIOError(RuntimeError):
    pass


def _parts(path: Path) -> tuple[str, ...]:
    if not path.is_absolute() or ".." in path.parts:
        raise SecureIOError(f"path must be absolute without traversal: {path}")
    return tuple(part for part in path.parts if part not in (path.anchor, "/", ""))


def open_directory(path: Path) -> int:
    """Open an absolute directory without following any path-component symlink."""
    parts = path.parts
    if len(parts) >= 5 and parts[1:4] == ("proc", "self", "fd") and parts[4].isdigit():
        descriptor = os.dup(int(parts[4]))
        if not stat.S_ISDIR(os.fstat(descriptor).st_mode):
            os.close(descriptor)
            raise SecureIOError("inherited output descriptor is not a directory")
        remaining = parts[5:]
    else:
        descriptor = os.open(path.anchor, DIRECTORY_FLAGS)
        remaining = _parts(path)
    try:
        for part in remaining:
            following = os.open(part, DIRECTORY_FLAGS, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = following
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def ensure_directory(path: Path) -> None:
    """Create one absent directory beneath an already safe parent."""
    parent_fd = open_directory(path.parent)
    try:
        try:
            os.mkdir(path.name, 0o700, dir_fd=parent_fd)
            os.fsync(parent_fd)
        except FileExistsError:
            pass
        child_fd = os.open(path.name, DIRECTORY_FLAGS, dir_fd=parent_fd)
        os.close(child_fd)
    finally:
        os.close(parent_fd)


def reserve_output(task_build: Path, supplied: Path, *, initial_journal: bool = False) -> tuple[Path, int, int]:
    """Atomically reserve an absent output leaf and verify its descriptor identity."""
    task_build = task_build.absolute()
    supplied = supplied.absolute()
    if ".." in supplied.parts:
        raise SecureIOError("output traversal is forbidden")
    try:
        relative = supplied.relative_to(task_build)
    except ValueError as error:
        raise SecureIOError("output escapes the task build directory") from error
    if not relative.parts:
        raise SecureIOError("output must be a strict task-build child")

    parent_fd = open_directory(task_build)
    try:
        for part in relative.parts[:-1]:
            following = os.open(part, DIRECTORY_FLAGS, dir_fd=parent_fd)
            os.close(parent_fd)
            parent_fd = following
        leaf = relative.parts[-1]
        os.mkdir(leaf, 0o700, dir_fd=parent_fd)
        os.fsync(parent_fd)
        output_fd = os.open(leaf, DIRECTORY_FLAGS, dir_fd=parent_fd)
        try:
            opened = os.fstat(output_fd)
            named = os.stat(leaf, dir_fd=parent_fd, follow_symlinks=False)
            if (opened.st_dev, opened.st_ino) != (named.st_dev, named.st_ino):
                raise SecureIOError("reserved output identity changed during verification")
            canonical = Path(os.readlink(f"/proc/self/fd/{output_fd}"))
            if canonical != supplied:
                raise SecureIOError(f"reserved output is not canonical: {canonical}")
            if initial_journal:
                publish_initial_journal(Path(f"/proc/self/fd/{output_fd}"), {
                    "schema": "R3-G-05-raw-stage-v1",
                    "stage": "outer-session-active",
                    "active": True,
                })
            return canonical, opened.st_dev, opened.st_ino
        finally:
            os.close(output_fd)
    finally:
        os.close(parent_fd)


def verify_directory(path: Path, device: int | None = None, inode: int | None = None) -> int:
    descriptor = open_directory(path.absolute())
    opened = os.fstat(descriptor)
    if device is not None and inode is not None and (opened.st_dev, opened.st_ino) != (device, inode):
        os.close(descriptor)
        raise SecureIOError("reserved output descriptor identity mismatch")
    return descriptor


def _target_state(directory_fd: int, name: str) -> os.stat_result | None:
    try:
        value = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return None
    if stat.S_ISLNK(value.st_mode):
        raise SecureIOError(f"refusing symlink marker target: {name}")
    if not stat.S_ISREG(value.st_mode):
        raise SecureIOError(f"refusing non-regular marker target: {name}")
    return value


def atomic_write(path: Path, content: bytes, *, require_absent: bool = False) -> None:
    """Write/fsync a marker without following or racing directory entries."""
    directory_fd = open_directory(path.absolute().parent)
    temporary = f".{path.name}.{secrets.token_hex(16)}.tmp"
    temporary_fd: int | None = None
    temporary_exists = False
    try:
        target = _target_state(directory_fd, path.name)
        if require_absent and target is not None:
            raise SecureIOError(f"marker already exists: {path.name}")
        temporary_fd = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
            dir_fd=directory_fd,
        )
        temporary_exists = True
        view = memoryview(content)
        while view:
            written = os.write(temporary_fd, view)
            view = view[written:]
        os.fsync(temporary_fd)
        os.close(temporary_fd)
        temporary_fd = None

        if require_absent:
            # link(2) is the atomic commit point: unlike replace, it refuses every
            # concurrently created destination entry without changing that entry.
            try:
                os.link(
                    temporary, path.name,
                    src_dir_fd=directory_fd, dst_dir_fd=directory_fd,
                    follow_symlinks=False,
                )
            except FileExistsError as error:
                # Preserve the stronger diagnostics for hostile entry types while
                # treating even a transient regular entry as a lost first-writer race.
                concurrent = _target_state(directory_fd, path.name)
                if concurrent is not None:
                    raise SecureIOError(f"marker already exists: {path.name}") from error
                raise SecureIOError(
                    f"marker appeared during absent-only commit: {path.name}") from error
            os.unlink(temporary, dir_fd=directory_fd)
            temporary_exists = False
        else:
            # Re-check for a concurrent symlink swap. os.replace replaces the
            # directory entry itself and never follows a later swap.
            _target_state(directory_fd, path.name)
            os.replace(
                temporary, path.name,
                src_dir_fd=directory_fd, dst_dir_fd=directory_fd,
            )
            temporary_exists = False
        os.fsync(directory_fd)
    finally:
        if temporary_fd is not None:
            os.close(temporary_fd)
        if temporary_exists:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
            else:
                os.fsync(directory_fd)
        os.close(directory_fd)


def atomic_write_json(path: Path, value: Any, *, require_absent: bool = False) -> None:
    encoded = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
    atomic_write(path, encoded, require_absent=require_absent)


def publish_terminal_bytes(path: Path, content: bytes) -> None:
    """Publish one terminal byte record with an unconditionally absent-only commit."""
    atomic_write(path, content, require_absent=True)


def publish_terminal_json(path: Path, value: Any) -> None:
    """Publish one terminal JSON record with an unconditionally absent-only commit."""
    encoded = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
    publish_terminal_bytes(path, encoded)


def replace_progress_json(path: Path, value: Any) -> None:
    """Durably replace an ordinary nonterminal progress record."""
    atomic_write_json(path, value, require_absent=False)


# These semantic publishers are intentionally separate from replace mode.  A
# production call site cannot accidentally omit an absent-only option.
def publish_initial_journal(output: Path, value: Any) -> None:
    publish_terminal_json(output / "raw-stage.json", value)


def publish_raw_success(output: Path, value: Any) -> None:
    publish_terminal_json(output / "raw-success.json", value)


def _valid_raw_failure(value: Any) -> bool:
    return (isinstance(value, dict)
            and set(value) == {"schema", "stage", "exitStatus"}
            and value.get("schema") == "R3-G-05-raw-failure-v1"
            and isinstance(value.get("stage"), str)
            and bool(value["stage"])
            and type(value.get("exitStatus")) is int)


def _existing_valid_raw_failure(path: Path) -> bool:
    """Validate an existing failure marker through one no-follow directory binding."""
    directory_fd = open_directory(path.absolute().parent)
    marker_fd: int | None = None
    try:
        target = _target_state(directory_fd, path.name)
        if target is None:
            return False
        try:
            marker_fd = os.open(
                path.name, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
                dir_fd=directory_fd,
            )
        except OSError as error:
            raise SecureIOError(f"could not open existing failure marker: {path.name}") from error
        opened = os.fstat(marker_fd)
        if (opened.st_dev, opened.st_ino) != (target.st_dev, target.st_ino):
            raise SecureIOError(f"existing failure marker identity changed: {path.name}")
        chunks: list[bytes] = []
        size = 0
        while True:
            chunk = os.read(marker_fd, 65537 - size)
            if not chunk:
                break
            chunks.append(chunk)
            size += len(chunk)
            if size > 65536:
                raise SecureIOError(f"existing failure marker is too large: {path.name}")
        current = _target_state(directory_fd, path.name)
        if (current is None
                or (current.st_dev, current.st_ino) != (opened.st_dev, opened.st_ino)):
            raise SecureIOError(f"existing failure marker identity changed: {path.name}")
        try:
            existing = json.loads(b"".join(chunks).decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise SecureIOError(f"existing failure marker is malformed: {path.name}") from error
        if not _valid_raw_failure(existing):
            raise SecureIOError(f"existing failure marker is invalid: {path.name}")
        final = _target_state(directory_fd, path.name)
        if (final is None
                or (final.st_dev, final.st_ino) != (opened.st_dev, opened.st_ino)):
            raise SecureIOError(f"existing failure marker identity changed: {path.name}")
        return True
    finally:
        if marker_fd is not None:
            os.close(marker_fd)
        os.close(directory_fd)


def publish_raw_failure(output: Path, value: Any) -> None:
    if not _valid_raw_failure(value):
        raise SecureIOError("refusing invalid raw failure record")
    path = output / "raw-failure.json"
    if _existing_valid_raw_failure(path):
        return
    try:
        publish_terminal_json(path, value)
    except SecureIOError:
        # A racing recovery writer may have won after the absence check. Only
        # one already-valid regular first writer makes that race idempotent.
        if _existing_valid_raw_failure(path):
            return
        raise


def publish_integrity_manifest(output: Path, value: Any) -> None:
    publish_terminal_json(output / "integrity-manifest.json", value)


def publish_outer_session(output: Path, value: Any) -> None:
    publish_terminal_json(output / "outer-session.json", value)


def publish_outer_success(output: Path, value: Any) -> None:
    publish_terminal_json(output / "outer-success.json", value)


def publish_watchdog_ready(records: Path, value: Any) -> None:
    publish_terminal_json(records / "watchdog.ready.json", value)


def publish_watchdog_done(records: Path, content: bytes) -> None:
    publish_terminal_bytes(records / "watchdog.done", content)


def durable_unlink(path: Path, *, missing_ok: bool = False) -> None:
    directory_fd = open_directory(path.absolute().parent)
    try:
        target = _target_state(directory_fd, path.name)
        if target is None:
            if missing_ok:
                return
            raise SecureIOError(f"marker is absent: {path.name}")
        os.unlink(path.name, dir_fd=directory_fd)
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)
