"""Tests for the expansion round trip's K normalization (`support.k_round_trip`)."""

from __future__ import annotations

from pathlib import Path
import json
import tempfile
import unittest

from support.k_round_trip import computation_cells, differences, normalized, sentences


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

    def test_a_named_continuation_in_any_computation_cell_is_the_anonymous_one(self) -> None:
        cells = computation_cells([
            "module M\n  configuration\n    <instrs maincell=\"\"> $PGM:K </instrs>\n"
            "    <todo> .K </todo>\n    <valstack> $STACK:ValStack </valstack>\n"
            "    <env> .Map </env>\n    <trace> .List </trace>\n\nendmodule\n",
        ])
        self.assertEqual(cells, {"instrs", "todo"})
        for cell in ("instrs", "todo"):
            self.assertEqual(
                normalized(f"rule <{cell}> f ( X:Int ) ~> T:K => g ( X:Int ) ~> T:K </{cell}>", cells),
                normalized(f"rule <{cell}> f ( Y:Int ) => g ( Y:Int ) ... </{cell}>", cells),
            )
        # The main cell's content is the computation whatever its initializer's sort: marked
        # `maincell`, or `<k>` (the main cell when none is marked).
        self.assertEqual(
            computation_cells(["configuration <instrs maincell=\"\"> $PGM:Instrs </instrs> <stack> .List </stack>"]),
            {"instrs"},
        )
        self.assertEqual(
            computation_cells(["configuration <k color=\"green\"> $PGM:Stmt </k> <env> $ENV:Map </env>"]),
            {"k"},
        )
        # `<k>` is a computation cell only when the configuration declares it.
        self.assertNotEqual(
            normalized("rule <k> f ( X:Int ) ~> T:K => g ( X:Int ) ~> T:K </k>", cells),
            normalized("rule <k> f ( Y:Int ) => g ( Y:Int ) ... </k>", cells),
        )
        # A definition that declares no configuration has K's default one, `<k> $PGM:K </k>`.
        self.assertEqual(computation_cells(["module M\n  rule a => b\nendmodule\n"]), {"k"})

    def test_a_cell_of_another_sort_gets_no_continuation_rule(self) -> None:
        cells = computation_cells([
            "configuration <k> $PGM:K </k> <env> .Map </env> <trace> .List </trace> <seen> $SEEN:Set </seen>"
        ])
        self.assertEqual(cells, {"k"})
        for cell in ("env", "trace", "seen"):
            self.assertNotEqual(
                normalized(f"rule <{cell}> f ( X:Int ) ~> T:K => g ( X:Int ) ~> T:K </{cell}>", cells),
                normalized(f"rule <{cell}> f ( Y:Int ) => g ( Y:Int ) ... </{cell}>", cells),
            )
        # Nor does a continuation whose two tails stand in different cells: it is read as written.
        split = "rule <env> A ~> T:K => .Map </env> <k> B ~> T:K </k>"
        self.assertEqual(normalized(split, cells), normalized(split, frozenset()))

    def test_differences_read_the_computation_cells_from_the_authored_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            authored, printed = Path(temporary, "a"), Path(temporary, "b")
            authored.mkdir()
            printed.mkdir()
            configuration = "module M\n  configuration\n    <instrs> $PGM:K </instrs>\n    <env> .Map </env>\n\n"
            (authored / "definition.k").write_text(
                configuration + "  rule <instrs> a => b ... </instrs>\nendmodule\n", encoding="utf-8",
            )
            (printed / "definition.k").write_text(
                configuration + "  rule <instrs> a ~> T:K => b ~> T:K </instrs>\nendmodule\n", encoding="utf-8",
            )
            self.assertEqual(differences(authored, printed), [])
            (printed / "definition.k").write_text(
                configuration + "  rule <instrs> a ~> T:K => c ~> T:K </instrs>\nendmodule\n", encoding="utf-8",
            )
            self.assertTrue(differences(authored, printed))

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

    def test_the_header_and_the_source_lines_are_left_out(self) -> None:
        self.assertEqual(
            sentences(
                "// Generated by `krs emit-k` from p. Do not edit; edit the Rust sources and emit again.\n"
                "\nmodule M\n  // KRS p/src/lib.rs: F, branch 2\n  rule a\n  // KRS p/src/lib.rs: g\n  rule b\n"
            ),
            sentences("\nmodule M\n  // KRS p/src/lib.rs: f_2\n  rule a\n  rule b\n"),
        )
        self.assertEqual(sentences("module M\n  rule a\n  rule b\n"), ["module M", "rule a", "rule b"])
        # Only the comment lines that open the text are the header: a later unindented comment,
        # such as one in a `raw_k!` sentence, is compared.
        self.assertEqual(
            sentences("// header\n\nmodule M\n  rule a\n// raw\n  rule b\n"),
            ["module M", "rule a // raw", "rule b"],
        )
        # A capability line and a production's rustdoc are not source lines: they stay.
        self.assertEqual(
            sentences("rule a\n  // krs-capability: AnywhereRule b\n  rule b"),
            ["rule a // krs-capability: AnywhereRule b", "rule b"],
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


    def test_the_symbol_tables_are_compared_by_identity(self) -> None:
        def table(*entries: tuple[str, str]) -> str:
            return json.dumps({"schema_version": 4, "entries": [
                {"identity": {"identity_kind": "label", "identity": identity}, "emitted_name": name,
                 "source_map_key": f"def.rule.{identity}"}
                for identity, name in entries
            ]})

        with tempfile.TemporaryDirectory() as temporary:
            authored, printed = Path(temporary, "a"), Path(temporary, "b")
            authored.mkdir()
            printed.mkdir()
            for directory in (authored, printed):
                (directory / "definition.k").write_text("rule a\n", encoding="utf-8")
            (authored / "symbols.json").write_text(table(("r1", "while"), ("r2", "if")), encoding="utf-8")
            # The same entries in another order are the same table.
            (printed / "symbols.json").write_text(table(("r2", "if"), ("r1", "while")), encoding="utf-8")
            self.assertEqual(differences(authored, printed), [])
            # The same K under another rule identity is another rule to the table's readers.
            (printed / "symbols.json").write_text(table(("r2", "if"), ("r3", "while")), encoding="utf-8")
            self.assertEqual(len(differences(authored, printed)), 2)
            (printed / "symbols.json").write_text(table(("r2", "if"), ("r1", "loop")), encoding="utf-8")
            self.assertTrue(differences(authored, printed))
            (printed / "symbols.json").unlink()
            self.assertEqual(differences(authored, printed), ["symbols.json: emitted by one side only"])

if __name__ == "__main__":
    unittest.main()
