"""Tests of the source scanners of scripts/coverage.sh.

Run with `python3 -m unittest discover -s scripts/coverage`.
"""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from source import blank, unmeasured_lines  # noqa: E402


def unmeasured(source):
    return sorted(unmeasured_lines(blank(source)))


class UnmeasuredLinesTests(unittest.TestCase):
    def test_the_argument_lines_of_a_multi_line_call_are_unmeasured(self):
        source = (
            "fn f(x: u32) -> SmallVec<[u32; 4]> {\n"  # 1
            "    smallvec![\n"  # 2: names the macro, carries the call's count
            "        x + 1,\n"  # 3
            "        if x > 1 { x } else { 0 },\n"  # 4
            "    ]\n"  # 5: no argument text
            "}\n"
        )
        self.assertEqual(unmeasured(source), [3, 4])

    def test_a_call_on_one_line_is_measured(self):
        source = 'fn f() { ("Top", smallvec![("sort", Leaf(sort))]) }\n'
        self.assertEqual(unmeasured(source), [])

    def test_the_repeat_form_expands_its_operands_once(self):
        source = "fn f() {\n    smallvec![\n        0u8;\n        4\n    ]\n}\n"
        self.assertEqual(unmeasured(source), [])

    def test_the_closing_line_is_unmeasured_when_it_ends_an_argument(self):
        source = (
            "let mut stack: SmallVec<[Frame; 4]> = smallvec::smallvec![Frame {\n"  # 1
            "    name,\n"  # 2
            "    built: Vec::new(),\n"  # 3
            "}];\n"  # 4: the end of the argument, then closing punctuation
        )
        self.assertEqual(unmeasured(source), [2, 3, 4])

    def test_code_after_the_call_keeps_its_line_measured(self):
        source = "let v = smallvec![\n    a,\n    b].into_iter().count();\n"
        self.assertEqual(unmeasured(source), [2])

    def test_nested_calls_and_brackets_end_at_the_matching_delimiter(self):
        source = (
            "smallvec![\n"  # 1
            "    (\"a\", f([1, 2])),\n"  # 2
            "    (\"b\", smallvec![\n"  # 3
            "        c,\n"  # 4
            "    ]),\n"  # 5
            "]\n"  # 6
            "after();\n"  # 7
        )
        self.assertEqual(unmeasured(source), [2, 3, 4, 5])

    def test_text_in_comments_and_strings_is_not_a_call(self):
        source = '// smallvec![\nlet s = "smallvec![";\nlet t = 1;\n/* smallvec![ */\n'
        self.assertEqual(unmeasured(source), [])


if __name__ == "__main__":
    unittest.main()
