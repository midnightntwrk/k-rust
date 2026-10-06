"""Source scanning for scripts/coverage.sh: which lines are test code, and where items are.

Both scanners work on Rust source whose comments, strings and character literals have been
blanked out, so braces inside them do not count. They match braces; they do not parse Rust.
"""

import functools
import os
import re


def is_test_file(rel):
    """True for a workspace-relative path whose whole content is test code."""
    parts = rel.split("/")
    if len(parts) > 2 and parts[2] in ("tests", "benches", "examples"):
        return True
    if "/src/" in rel and "/tests/" in rel.split("/src/", 1)[1]:
        return True
    if "/src/tests/" in rel:
        return True
    base = os.path.basename(rel)
    return base == "tests.rs" or base.endswith("_tests.rs") or base == "test_support.rs"


def blank(source):
    """Replace comment, string and character-literal contents with spaces, keeping newlines."""
    out = []
    i = 0
    n = len(source)
    while i < n:
        c = source[i]
        if source.startswith("//", i):
            j = source.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if source.startswith("/*", i):
            depth = 0
            j = i
            while j < n:
                if source.startswith("/*", j):
                    depth += 1
                    j += 2
                    continue
                if source.startswith("*/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                    continue
                j += 1
            out.append(re.sub(r"[^\n]", " ", source[i:j]))
            i = j
            continue
        raw = re.match(r'b?r(#*)"', source[i : i + 300])
        if raw and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_")):
            close = '"' + raw.group(1)
            j = source.find(close, i + raw.end())
            j = n if j < 0 else j + len(close)
            out.append(re.sub(r"[^\n]", " ", source[i:j]))
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n and source[j] != '"':
                j += 2 if source[j] == "\\" else 1
            j += 1
            out.append(re.sub(r"[^\n]", " ", source[i:j]))
            i = j
            continue
        if c == "'":
            char = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'])'", source[i : i + 16])
            if char:
                out.append(" " * char.end())
                i += char.end()
                continue
        out.append(c)
        i += 1
    return "".join(out)


def _line(text, offset):
    return text.count("\n", 0, offset) + 1


def _matching_brace(text, start):
    depth = 0
    for j in range(start, len(text)):
        if text[j] == "{":
            depth += 1
        elif text[j] == "}":
            depth -= 1
            if depth == 0:
                return j
    return len(text) - 1


@functools.lru_cache(maxsize=None)
def _blanked(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        return blank(handle.read())


def cfg_test_lines(path):
    """1-based lines inside `#[cfg(test)]` items, from the attribute to the closing brace or `;`."""
    text = _blanked(path)
    lines = set()
    for match in re.finditer(r"#\[cfg\(\s*test\s*\)\]", text):
        j = match.end()
        depth = 0
        end = None
        while j < len(text):
            ch = text[j]
            if ch == ";" and depth == 0:
                end = j
                break
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = j
                    break
            j += 1
        if end is None:
            end = len(text) - 1
        lines.update(range(_line(text, match.start()), _line(text, end) + 1))
    return lines


class Workspace:
    def __init__(self, root):
        self.root = root
        self._masks = {}

    def test_mask(self, rel):
        """None when the whole file is test code, else the set of its test lines."""
        if rel not in self._masks:
            if is_test_file(rel):
                self._masks[rel] = None
            else:
                try:
                    self._masks[rel] = frozenset(cfg_test_lines(os.path.join(self.root, rel)))
                except FileNotFoundError:
                    self._masks[rel] = None
        return self._masks[rel]

    @functools.lru_cache(maxsize=None)
    def items(self, rel):
        """(kind, qualified name, first line, last line) of the `fn` and `impl` items of a file.

        A method is qualified by the self type of the innermost `impl` or `trait` block around
        it, as `Type::method`.
        """
        text = _blanked(os.path.join(self.root, rel))
        out = []
        blocks = []
        for match in re.finditer(r"(?<![\w])(impl|trait)\b", text):
            j = match.end()
            while j < len(text) and text[j] not in "{;":
                j += 1
            if j >= len(text) or text[j] == ";":
                continue
            header = text[match.end() : j]
            if match.group(1) == "trait":
                name = re.match(r"\s*(\w+)", header)
                self_type = name.group(1) if name else None
            else:
                # `impl Trait` in argument or return position is not an item.
                before = text[max(0, match.start() - 40) : match.start()]
                if re.search(r"(->|:|\(|,|<|&|=)\s*$", before):
                    continue
                head = re.sub(r"\bwhere\b.*", "", header, flags=re.S).strip()
                if head.startswith("<"):
                    depth = 0
                    for k, ch in enumerate(head):
                        if ch == "<":
                            depth += 1
                        elif ch == ">":
                            depth -= 1
                            if depth == 0:
                                head = head[k + 1 :]
                                break
                if re.search(r"\bfor\b", head):
                    head = re.split(r"\bfor\b", head)[-1]
                head = re.sub(r"<.*", "", head, flags=re.S).strip()
                self_type = head.split("::")[-1].strip(" &") if head else None
            end = _matching_brace(text, j)
            blocks.append((j, end, self_type))
            out.append(("impl", self_type, _line(text, match.start()), _line(text, end)))
        for match in re.finditer(r"(?<![\w])fn\s+(\w+)", text):
            j = match.end()
            depth = 0
            while j < len(text):
                ch = text[j]
                if ch in "([":
                    depth += 1
                elif ch in ")]":
                    depth -= 1
                elif depth == 0 and ch in "{;":
                    break
                j += 1
            if j >= len(text) or text[j] == ";":
                continue
            end = _matching_brace(text, j)
            owner = None
            for start, stop, self_type in blocks:
                if start < match.start() < stop:
                    owner = self_type
            name = match.group(1)
            out.append(("fn", f"{owner}::{name}" if owner else name, _line(text, match.start()), _line(text, end)))
        return tuple(out)

    def site_spans(self, rel, symbol):
        """Line spans of the item a card site names: a `fn`, a `Type::method`, or a type's `impl`
        blocks. A bare name that matches no free function falls back to methods of that name."""
        items = self.items(rel)
        spans = [(a, b) for kind, name, a, b in items if name == symbol and kind in ("fn", "impl")]
        if not spans and "::" not in symbol:
            spans = [(a, b) for kind, name, a, b in items if kind == "fn" and name and name.split("::")[-1] == symbol]
        if not spans and "::" in symbol:
            # A path-qualified free function, as `module::function`.
            last = symbol.split("::")[-1]
            spans = [(a, b) for kind, name, a, b in items if kind == "fn" and name == last]
        return spans
