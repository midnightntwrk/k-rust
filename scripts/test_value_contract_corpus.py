import tomllib
import unittest
from pathlib import Path

MANIFEST = Path(__file__).with_name("value-contract-corpus.toml")


class ManifestTest(unittest.TestCase):
    """The critical-pair corpus gate pins the check where it matters: on definitions that
    withdraw claims. A manifest whose definitions all join pins counts, but never the warnings a
    user sees, nor a change that withdraws claims from the definition that has them."""

    def setUp(self):
        with open(MANIFEST, "rb") as manifest:
            self.cases = tomllib.load(manifest)["case"]

    def test_some_recorded_case_has_a_relevant_pair_that_does_not_join(self):
        withdrawing = [case["name"] for case in self.cases
                       if case.get("expected", {}).get("relevant", 0) > 0
                       and case["expected"]["unjoined"] > 0]
        self.assertTrue(withdrawing, "no case of the manifest withdraws a claim")

    def test_every_case_names_a_definition_the_script_can_obtain(self):
        names = [case["name"] for case in self.cases]
        self.assertEqual(len(names), len(set(names)), names)
        for case in self.cases:
            definition = case["definition"]
            self.assertTrue(definition in ("wasm", "kevm") or (
                definition.startswith("conformance:tests/regression-new/")
                and definition.endswith("/krust-kompiled/definition.kore")), definition)


if __name__ == "__main__":
    unittest.main()
