"""Test of measure.py's wait: the timeout kills the process group, and the wall time is not quantized.

Run: python3 -m unittest discover -s scripts/conformance -p 'test_*.py'

Each case runs measure.py as a subprocess, as algo-receipt.sh does, and reads PREFIX.meta.toml.
The quantization case bounds the smallest overshoot over a few runs of `sleep 0.12`: a wait that
polls with a delay growing to 50 ms overshoots it by about 44 ms on every run, while a wait that
returns at the exit overshoots it by the process start and exit only.
"""
import os
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from pathlib import Path

MEASURE = Path(__file__).resolve().parent / "measure.py"


def measure(directory, name, options, command):
    prefix = str(Path(directory, name))
    subprocess.run([sys.executable, str(MEASURE), "--log", prefix, *options, "--", *command],
                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                   timeout=60)
    with open(prefix + ".meta.toml", "rb") as f:
        return tomllib.load(f)


def gone(pid, seconds=5.0):
    """Whether pid has exited (absent or a zombie awaiting its new parent) within `seconds`."""
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        try:
            state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
        except (FileNotFoundError, ProcessLookupError):
            return True
        if state in ("Z", "X"):
            return True
        time.sleep(0.01)
    return False


class MeasureWaitTest(unittest.TestCase):
    def test_timeout_kills_the_process_group(self):
        for streamed in ([], ["--stdout-keep-bytes", "1000"]):
            with tempfile.TemporaryDirectory() as directory:
                pid_file = Path(directory, "pid")
                # The background sleep is in the command's process group but is not its child.
                script = f"sleep 30 & echo $! > {pid_file}; head -c 100000 /dev/zero; sleep 30; wait"
                start = time.monotonic()
                meta = measure(directory, "run", ["--timeout", "0.5", *streamed], ["bash", "-c", script])
                elapsed = time.monotonic() - start
                self.assertTrue(meta["timed_out"], streamed)
                self.assertEqual(meta["exit_code"], -9, streamed)
                self.assertGreaterEqual(meta["wall_seconds"], 0.5, streamed)
                self.assertLess(elapsed, 10, streamed)
                self.assertTrue(gone(int(pid_file.read_text())), streamed)
                if streamed:
                    self.assertEqual(meta["stdout_bytes"], 100000)

    def test_exit_status_without_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            for options in ([], ["--timeout", "10"]):
                meta = measure(directory, "exit", options, ["bash", "-c", "exit 3"])
                self.assertEqual((meta["exit_code"], meta["timed_out"]), (3, False), options)
                meta = measure(directory, "signal", options, ["bash", "-c", "kill -TERM $$"])
                self.assertEqual((meta["exit_code"], meta["timed_out"]), (-15, False), options)

    def test_peak_rss_is_the_commands(self):
        allocate = "b = bytearray(200 << 20); b[::4096] = b'x' * len(b[::4096])"
        with tempfile.TemporaryDirectory() as directory:
            for options in ([], ["--timeout", "30"], ["--timeout", "30", "--stdout-keep-bytes", "10"]):
                meta = measure(directory, "rss", options, [sys.executable, "-c", allocate])
                self.assertGreaterEqual(meta["peak_rss_kib"], 200 << 10, options)
                self.assertLess(meta["peak_rss_kib"], 400 << 10, options)

    def test_wall_time_under_timeout_is_not_quantized(self):
        with tempfile.TemporaryDirectory() as directory:
            overshoots = []
            for _ in range(5):
                meta = measure(directory, "sleep", ["--timeout", "10"], ["sleep", "0.12"])
                overshoots.append(meta["wall_seconds"] - 0.12)
            self.assertLess(min(overshoots), 0.025, overshoots)


if __name__ == "__main__":
    unittest.main()
