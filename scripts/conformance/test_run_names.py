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

    def test_c7_renames_mints_as_the_pinned_kprint_prints_them(self):
        # kprint drops the first three characters of a KORE variable name: `Ex-hVar'Ques'Tx-b6`
        # prints as `hVar?Tx-b6` (measured with the pinned K 7.1.337 kprint).
        self.assertEqual(
            rename_existentials("hVar?Tx-b6:Type -> ( hVar?Tx-b6:Type -> hFrame-b0:Map )"),
            "?'KDiff0:Type -> ( ?'KDiff0:Type -> ?'KDiff1:Map )",
        )
        self.assertIsNone(
            execution_text_diff(
                "( ?Tx:Type -> ?Ty:Type ) -> ?Tx:Type",
                "( hVar?Tx-b6:Type -> hVar?Ty-b7:Type ) -> hVar?Tx-b6:Type",
            )[0]
        )
        # Two mints stay two variables, and one reference variable is not two mints.
        self.assertIsNotNone(
            execution_text_diff("?A:Type -> ?A:Type", "hVar?T-b1:Type -> hVar?T-b2:Type")[0]
        )
        # A string literal is never renamed.
        self.assertEqual(rename_existentials('"x-b1:Int"'), '"x-b1:Int"')
        # A declared pattern name stays literal; a mint beside it is renamed.
        self.assertEqual(
            rename_existentials("?T:Type hVar?T-b3:Type", fixed=frozenset({"T"})),
            "?T:Type ?'KDiff0:Type",
        )


if __name__ == "__main__":
    unittest.main()
