"""Tests for the expansion round trip's K normalization (`support.k_round_trip`)."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from support.k_round_trip import differences, normalized, sentences


class NormalizationTests(unittest.TestCase):
    def test_a_named_continuation_used_only_as_the_rest_is_the_anonymous_one(self) -> None:
        self.assertEqual(
            normalized("rule <k> f ( X:Int ) ~> Tail:K => g ( X:Int ) ~> Tail:K </k>"),
            normalized("rule <k> f ( Y:Int ) => g ( Y:Int ) ... </k>"),
        )
        # A continuation the rule uses again is no anonymous rest.
        self.assertNotEqual(
            normalized("rule <k> f ( T:K ) ~> T:K => g ~> T:K </k>"),
            normalized("rule <k> f ( T:K ) => g ... </k>"),
        )

    def test_a_rest_matched_once_in_a_cell_without_a_rewrite_is_the_anonymous_one(self) -> None:
        self.assertEqual(
            normalized("rule <env> N |-> V:Int Rest0:Map </env>"),
            normalized("rule <env> N |-> W:Int ... </env>"),
        )
        # A variable after a rewrite in the cell stands on its right-hand side.
        self.assertNotEqual(
            normalized("rule <env> M:Map => N:Map R:Map </env>"),
            normalized("rule <env> M:Map => N:Map ... </env>"),
        )
        # One used elsewhere in the sentence is no anonymous rest.
        self.assertNotEqual(
            normalized("rule <env> R:Map </env> <k> R:Map </k>"),
            normalized("rule <env> ... </env> <k> R:Map </k>"),
        )

    def test_a_raw_k_comment_is_read_without_its_position(self) -> None:
        self.assertEqual(
            sentences("rule a\n// raw_k! src/lib.rs:38:1 (opaque to KRS)\nrule b"),
            sentences("rule a\n// raw_k! src/lib.rs:43:1 (opaque to KRS)\nrule b"),
        )

    def test_a_missing_sentence_is_a_difference_at_any_position(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            authored, printed = Path(temporary, "a"), Path(temporary, "b")
            authored.mkdir()
            printed.mkdir()
            (authored / "definition.k").write_text("rule a\nrule b\n", encoding="utf-8")
            (printed / "definition.k").write_text("rule a\n", encoding="utf-8")
            self.assertTrue(differences(authored, printed))
            (printed / "definition.k").write_text("rule a\nrule b\n", encoding="utf-8")
            self.assertEqual(differences(authored, printed), [])
            (printed / "spec.k").write_text("claim c\n", encoding="utf-8")
            self.assertTrue(differences(authored, printed))


if __name__ == "__main__":
    unittest.main()
