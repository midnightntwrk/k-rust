"""Variable-name coverage for C7's execution-text comparison."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import decoded_generated_name, execution_text_diff, rename_existentials


class VariableNameTests(unittest.TestCase):
    def test_encoded_marker_and_counter_are_generated(self):
        self.assertEqual(decoded_generated_name("Ex-hFrame-b0"), "Ex#Frame!0")
        self.assertEqual(decoded_generated_name("Rule-hX"), "Rule#X")
        self.assertIsNone(decoded_generated_name("ExFrame0"))
        self.assertIsNone(decoded_generated_name("a-x"))
        self.assertIsNone(decoded_generated_name("a-u2e-"))

    def test_c7_renames_complete_encoded_names_and_preserves_sharing(self):
        self.assertEqual(
            rename_existentials("?Ex-hFrame-b0:SortS ?Ex-hFrame-b0:SortS ?Ex-hFrame-b1:SortS"),
            "?'KDiff0:SortS ?'KDiff0:SortS ?'KDiff1:SortS",
        )
        self.assertIsNone(
            execution_text_diff("?Var'Ques'X1:SortS", "?Ex-hFrame-b0:SortS")[0]
        )


if __name__ == "__main__":
    unittest.main()
