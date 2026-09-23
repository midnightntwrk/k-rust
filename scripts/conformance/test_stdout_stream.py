"""Unit test of stdout_stream: the streamed predicates, size, digest and head equal a whole-file read.

Run: python3 -m unittest discover -s scripts/conformance -p 'test_*.py'

The oracle is the whole-file evaluation: Path.read_text(errors="replace"), re.sub(r"\\s+", "", ...)
and Python's `in`. Each case feeds the same bytes through randomly sized raw reads, with and
without the ASCII fast path, so needles, whitespace runs, CR LF pairs and multi-byte sequences
fall across block boundaries and blocks alternate between the fast path and the decoder.
"""
import hashlib
import io
import os
import random
import re
import tempfile
import unittest
from pathlib import Path

import stdout_stream


class ChoppedReader(io.RawIOBase):
    """A raw stream that returns data in randomly sized reads."""

    def __init__(self, data, rng, largest):
        self.data = data
        self.position = 0
        self.rng = rng
        self.largest = largest

    def readable(self):
        return True

    def readinto(self, buffer):
        count = min(len(buffer), self.rng.randint(1, self.largest), len(self.data) - self.position)
        buffer[:count] = self.data[self.position:self.position + count]
        self.position += count
        return count


def whole_file_results(path, check):
    stdout = Path(path).read_text(errors="replace")
    squeezed = re.sub(r"\s+", "", stdout)
    results = []
    for text in check.get("stdout", []):
        results.append({"kind": "stdout contains", "detail": text, "passed": text in stdout})
    for text in check.get("stdout_squeezed", []):
        results.append({"kind": "stdout contains, whitespace removed", "detail": text,
                        "passed": re.sub(r"\s+", "", text) in squeezed})
    for text in check.get("stdout_absent", []):
        results.append({"kind": "stdout lacks", "detail": text, "passed": text not in stdout})
    return results


PIECES = ["\\equals{", "SortK{}", "(", ")", ",", "\\or{", " ", "  ", "\n", "\r\n", "\r", "\t",
          "\x0b", "\x0c", "\x1c", "\x1f", "\u00a0", "\u2003", "\u3000", "\u0085", "\u00e9", "\u2200", "\U0001d538",
          "dv", "\"42\"", "inj", "x", "y"]
BYTE_PIECES = [b"\xff", b"\xc3", b"\xe2\x88", b"\xf0\x9d", b"\x80"]


ASCII_PIECES = [piece for piece in PIECES if piece.isascii() and "\r" not in piece]


def random_bytes(rng, length, special):
    """Random pieces; a proportion `special` of them may be non-ASCII, invalid UTF-8 or CR."""
    parts = []
    for _ in range(length):
        roll = rng.random()
        if roll >= special:
            parts.append(rng.choice(ASCII_PIECES).encode())
        elif roll < special * 0.1:
            parts.append(rng.choice(BYTE_PIECES))
        else:
            parts.append(rng.choice(PIECES).encode())
    return b"".join(parts)


def random_needle(rng, data, rng_len=12):
    text = data.decode(errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    if text and rng.random() < 0.7:
        start = rng.randrange(len(text))
        return text[start:start + rng.randint(1, rng_len * 4)]
    return "".join(rng.choice(PIECES) for _ in range(rng.randint(0, rng_len)))


class StreamTest(unittest.TestCase):
    def run_case(self, data, check, rng, keep_bytes, head_bytes, directory, fast=True):
        whole = Path(directory, "whole.stdout")
        whole.write_bytes(data)
        expected = whole_file_results(whole, check)
        prefix = str(Path(directory, "streamed.stdout"))
        for path in (prefix, prefix + ".head"):
            if os.path.exists(path):
                os.remove(path)
        sink = stdout_stream.ByteSink(prefix, keep_bytes, head_bytes)
        predicates = stdout_stream.StdoutPredicates(check, ascii_fast_path=fast)
        source = ChoppedReader(data, rng, rng.choice([1, 2, 3, 7, 64, 4096]))
        stdout_stream.consume(source, sink, predicates)
        self.assertEqual(predicates.results(), expected, (data, check))
        summary = sink.summary()
        self.assertEqual(summary["bytes"], len(data))
        self.assertEqual(summary["sha256"], hashlib.sha256(data).hexdigest())
        self.assertEqual(summary["kept"], len(data) <= keep_bytes)
        if len(data) <= keep_bytes:
            self.assertEqual(Path(prefix).read_bytes(), data)
            self.assertFalse(os.path.exists(prefix + ".head"))
        else:
            self.assertEqual(Path(prefix + ".head").read_bytes(), data[:head_bytes])
            self.assertFalse(os.path.exists(prefix))

    def test_random_chunkings(self):
        rng = random.Random(20260924)
        with tempfile.TemporaryDirectory() as directory:
            for _ in range(3000):
                data = random_bytes(rng, rng.randint(0, rng.choice([80, 80, 80, 3000])),
                                    rng.choice([0.0, 0.01, 0.05, 0.3]))
                check = {
                    "stdout": [random_needle(rng, data) for _ in range(rng.randint(0, 3))],
                    "stdout_squeezed": [random_needle(rng, data) for _ in range(rng.randint(0, 3))],
                    "stdout_absent": [random_needle(rng, data) for _ in range(rng.randint(0, 3))],
                }
                keep_bytes = rng.choice([0, 1, 10, 40, 1000, 100000])
                head_bytes = rng.choice([0, 1, 5, 64])
                self.run_case(data, check, rng, keep_bytes, head_bytes, directory, rng.random() < 0.8)

    def test_found_needles_are_the_whole_file_answer(self):
        # A fixed case whose needles and whitespace runs cross every boundary of one-byte reads.
        rng = random.Random(1)
        data = b"a \r\n b\tc\xc3\xa9\xff d\r\n\\or{ x"
        check = {"stdout": ["\n b", "\xe9\ufffd d", "\r"], "stdout_squeezed": ["abc\xe9\ufffdd", "b c"],
                 "stdout_absent": ["\\or{", "zz"]}
        with tempfile.TemporaryDirectory() as directory:
            for fast in (True, False):
                self.run_case(data, check, rng, 1 << 20, 65536, directory, fast)

    def test_ascii_whitespace_is_str_whitespace(self):
        self.assertEqual(stdout_stream.ASCII_WHITESPACE,
                         bytes(code for code in range(128) if re.match(r"\s", chr(code))))

    def test_squeeze_matches_re(self):
        for code in range(0x110000):
            if 0xD800 <= code <= 0xDFFF:
                continue
            text = "a" + chr(code) + "b"
            self.assertEqual(stdout_stream.squeeze(text), re.sub(r"\s+", "", text), hex(code))


if __name__ == "__main__":
    unittest.main()
