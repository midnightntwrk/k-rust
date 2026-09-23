"""Consume a measured command's standard output as a stream, in bounded memory and disk.

One pass over the byte stream computes its size and SHA-256, keeps it whole in a file while it
is at most keep_bytes long (otherwise only its first head_bytes, in a separate file), and
evaluates the stdout predicates of an algo-receipt check.json:

  stdout          every needle occurs in the text
  stdout_squeezed every needle, with its whitespace removed, occurs in the text with its
                  whitespace removed
  stdout_absent   no needle occurs in the text

"The text" is the stream decoded as Path.read_text(errors="replace") decodes a file: the
encoding TextIOWrapper chooses by default, undecodable bytes replaced by U+FFFD, and universal
newlines. TextIOWrapper decodes with IncrementalNewlineDecoder(the codec's incremental decoder,
translate=True); this module feeds the same decoder block by block, and an incremental decoder
returns, over any split of its input, the concatenation of what one call on the whole input
returns. "Whitespace" is the set of characters re's \\s matches in a str pattern, which is the
set str.isspace accepts and str.split() splits at.

Each predicate kind scans its own stream (the text, or the text with whitespace removed) with a
carry of the last L - 1 characters, L the longest needle: an occurrence that ends in a block
starts at most L - 1 characters before the block, so it lies in carry + block, and every
occurrence in carry + block is an occurrence in the stream. Removing whitespace deletes each
whitespace character independently, so the squeezed stream is the concatenation of the blocks'
squeezed forms, whatever the block boundaries.

ASCII fast path, for a UTF-8 decoder: a block of ASCII bytes without CR, decoded from the
decoder's initial state, is its own text (one character per byte) and leaves the decoder in its
initial state. Such a block is scanned as bytes, without decoding: a needle that is not ASCII
cannot occur within an ASCII block, an ASCII needle occurs in the block's text exactly where its
bytes occur in its bytes (an occurrence across the carry is searched in the carry's own
form), and the text's whitespace characters in such a block are the
ASCII bytes that str.isspace accepts, which bytes.translate deletes. Any other block goes through
the decoder, and the fast path resumes once the decoder is back in its initial state.
"""
import codecs
import hashlib
import io
import json
import os
import queue
import threading

HEAD_BYTES = 65536
READ_BYTES = 1 << 20
QUEUED_READS = 64

ASCII_WHITESPACE = bytes(code for code in range(128) if chr(code).isspace())


def squeeze(text):
    """text with every character that re's \\s matches removed."""
    return "".join(text.split())


def default_text_decoder():
    """The decoder a default TextIOWrapper(errors="replace") reads with, and its encoding."""
    encoding = io.TextIOWrapper(io.BytesIO(), errors="replace").encoding
    inner = codecs.getincrementaldecoder(encoding)(errors="replace")
    return io.IncrementalNewlineDecoder(inner, translate=True), codecs.lookup(encoding).name


class SubstringScanner:
    """Whether each needle occurs in a stream fed as text chunks or ASCII byte blocks.

    The carry holds the stream's last L - 1 characters: as bytes when they all come from ASCII
    blocks fed since the last text chunk, as text otherwise.
    """

    def __init__(self, needles):
        self.needles = list(needles)
        self.ascii_needles = [needle.encode("ascii") if needle.isascii() else None
                              for needle in self.needles]
        self.found = [needle in "" for needle in self.needles]
        self.overlap = max((len(needle) for needle in self.needles), default=1) - 1
        self.carry = b""

    def done(self):
        return all(self.found)

    def feed_ascii(self, block):
        # An occurrence that ends in the block lies in the block, or starts in the carry and
        # then ends within the block's first L - 1 characters.
        if self.done() or not block:
            return
        text_carry = isinstance(self.carry, str)
        head = block[:self.overlap]
        boundary = self.carry + (head.decode("ascii") if text_carry else head)
        for index, needle in enumerate(self.needles):
            ascii_needle = self.ascii_needles[index]
            if self.found[index]:
                continue
            if ascii_needle is not None and ascii_needle in block:
                self.found[index] = True
            elif text_carry and needle in boundary:
                self.found[index] = True
            elif not text_carry and ascii_needle is not None and ascii_needle in boundary:
                self.found[index] = True
        if not self.overlap:
            self.carry = b""
        elif len(block) >= self.overlap:
            self.carry = block[-self.overlap:]
        else:
            self.carry = (self.carry + (block.decode("ascii") if text_carry else block))[-self.overlap:]

    def feed_text(self, chunk):
        if isinstance(self.carry, bytes):
            self.carry = self.carry.decode("ascii")
        if self.done() or not chunk:
            return
        window = self.carry + chunk
        for index, needle in enumerate(self.needles):
            if not self.found[index] and needle in window:
                self.found[index] = True
        self.carry = window[-self.overlap:] if self.overlap else ""


class StdoutPredicates:
    """The stdout predicates of a check.json, evaluated over the byte blocks of the stream."""

    def __init__(self, check, ascii_fast_path=True):
        self.contains = check.get("stdout", [])
        self.squeezed = check.get("stdout_squeezed", [])
        self.absent = check.get("stdout_absent", [])
        self.plain = SubstringScanner(self.contains + self.absent)
        self.squeezed_scanner = SubstringScanner([squeeze(text) for text in self.squeezed])
        self.decoder, encoding = default_text_decoder()
        self.initial_state = self.decoder.getstate()
        self.ascii_fast_path = ascii_fast_path and encoding == "utf-8"

    @property
    def empty(self):
        return not (self.contains or self.squeezed or self.absent)

    def _done(self):
        return self.plain.done() and self.squeezed_scanner.done()

    def feed(self, block, final=False):
        if self._done():
            return
        if (self.ascii_fast_path and not final and block.isascii() and b"\r" not in block
                and self.decoder.getstate() == self.initial_state):
            self.plain.feed_ascii(block)
            if not self.squeezed_scanner.done():
                self.squeezed_scanner.feed_ascii(block.translate(None, ASCII_WHITESPACE))
            return
        text = self.decoder.decode(block, final)
        self.plain.feed_text(text)
        if not self.squeezed_scanner.done():
            self.squeezed_scanner.feed_text(squeeze(text))

    def finish(self):
        self.feed(b"", final=True)

    def results(self):
        found = self.plain.found
        records = [{"kind": "stdout contains", "detail": text, "passed": found[index]}
                   for index, text in enumerate(self.contains)]
        records += [{"kind": "stdout contains, whitespace removed", "detail": text,
                     "passed": self.squeezed_scanner.found[index]}
                    for index, text in enumerate(self.squeezed)]
        records += [{"kind": "stdout lacks", "detail": text,
                     "passed": not found[len(self.contains) + index]}
                    for index, text in enumerate(self.absent)]
        return records


class ByteSink:
    """Size, SHA-256, and the kept file or head of a byte stream."""

    def __init__(self, path, keep_bytes, head_bytes=HEAD_BYTES):
        self.path = path
        self.keep_bytes = keep_bytes
        self.head_bytes = head_bytes
        self.size = 0
        self.digest = hashlib.sha256()
        self.file = open(path, "wb")
        self.kept = True

    def write(self, data):
        self.digest.update(data)
        before = self.size
        self.size += len(data)
        if self.file is None:
            return
        if self.kept and self.size <= self.keep_bytes:
            self.file.write(data)
            return
        if self.kept:
            # The stream outgrew keep_bytes: keep only its first head_bytes, as NAME.stdout.head.
            self.kept = False
            self.file.truncate(min(self.head_bytes, before))
            self.file.seek(0, os.SEEK_END)
            os.replace(self.path, self.path + ".head")
        if before < self.head_bytes:
            self.file.write(data[:self.head_bytes - before])
        if self.size >= self.head_bytes:
            self.file.close()
            self.file = None

    def close(self):
        if self.file is not None:
            self.file.close()
            self.file = None

    def summary(self):
        return {"bytes": self.size, "sha256": self.digest.hexdigest(), "kept": self.kept}


def consume(source, sink, predicates=None):
    """Read the raw binary stream source to its end into sink, feeding predicates its blocks.

    This thread only reads the pipe and queues its blocks, so that the writer is held up as
    little as possible; a second thread hashes and writes them (hashlib releases the GIL on
    large blocks) and feeds the predicates. The queue holds at most QUEUED_READS blocks of at
    most READ_BYTES, which bounds the memory.
    """
    blocks = queue.Queue(QUEUED_READS)
    failure = []
    active = predicates is not None and not predicates.empty

    def work():
        try:
            while (block := blocks.get()) is not None:
                sink.write(block)
                if active:
                    predicates.feed(block)
            if active:
                predicates.finish()
        except BaseException as error:
            failure.append(error)
            # Keep draining so that the reading side never blocks on a full queue.
            while blocks.get() is not None:
                pass

    worker = threading.Thread(target=work)
    worker.start()
    try:
        while block := source.read(READ_BYTES):
            blocks.put(block)
    finally:
        blocks.put(None)
        worker.join()
        sink.close()
    if failure:
        raise failure[0]


def load_predicates(check_path):
    with open(check_path) as check:
        return StdoutPredicates(json.load(check))
