"""C10's reading of the structural comparator's N15 summary line."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import kore_output_implication_pairs


class ImplicationSummaryTests(unittest.TestCase):
    def test_a_structural_pass_rests_on_no_implication_pair(self):
        self.assertEqual(kore_output_implication_pairs(""), 0)
        self.assertEqual(kore_output_implication_pairs("\nrunning 1 test\n.\ntest result: ok.\n"), 0)

    def test_the_summary_line_counts_the_implication_pairs(self):
        output = (
            "running 1 test\n"
            "N15: constraints of paired disjunct t{}() equal only by krust kore-implies in both directions\n"
            "  reference: c\n  actual: d\n"
            "N15 summary: 2 paired disjunct(s) equal only by krust kore-implies (supplementary evidence)\n"
            "test result: ok.\n"
        )
        self.assertEqual(kore_output_implication_pairs(output), 2)

    def test_only_a_line_that_starts_with_the_summary_counts(self):
        self.assertEqual(kore_output_implication_pairs("x N15 summary: 3 pairs\n"), 0)


if __name__ == "__main__":
    unittest.main()
