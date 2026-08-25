from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import unittest


HERE = Path(__file__).resolve().parent


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class StableNameProbeTests(unittest.TestCase):
    def test_current_capability_report_names_exact_blockers(self) -> None:
        module = load(HERE / "stable-names/probe.py", "stable_name_probe")
        report = module.capability_report()
        self.assertTrue(all(report["fixtures"].values()))
        self.assertTrue(report["stable_id_has_module_path"])
        if all(report[key] for key in (
            "descriptor_has_visibility", "symbol_macro_exported", "explicit_symbol_lowered",
        )):
            module.verify(report)
        else:
            with self.assertRaises(module.StableNameError):
                module.verify(report)


class DiagnosticProbeTests(unittest.TestCase):
    def test_aggregate_report_does_not_hide_missing_cli_translation(self) -> None:
        module = load(HERE / "diagnostics/probe.py", "diagnostic_probe")
        report = module.report()
        self.assertTrue(report["rust_expansion_fixture"])
        self.assertTrue(report["rust_analyzer_exact_range_wired"])
        self.assertTrue(report["krs_analysis_cross_item_fixture"])
        self.assertTrue(report["k_frontend_exact_sidecar_probe"])
        self.assertTrue(report["backend"]["adapter_structured_diagnostic"])
        repaired = (
            report["krs_cli_structured_analysis_range"]
            and report["backend"]["cli_structured_diagnostic_envelope"]
            and report["backend"]["cli_authored_origin_translation"]
            and report["backend"]["cli_structured_diagnostic_rendering"]
        )
        if repaired:
            module.verify(report)
        else:
            with self.assertRaisesRegex(RuntimeError, "diagnostic release boundaries incomplete"):
                module.verify(report)

    def test_k_frontend_mapping_requires_exact_content_identity(self) -> None:
        module = load(HERE / "diagnostics/k-frontend/probe.py", "frontend_probe")
        authored = b"before ExactToken after\n"
        definition = b"module M\n  rule exact\nendmodule\n"
        source_start = authored.index(b"ExactToken")
        generated_start = definition.index(b"exact")
        entry = {
            "origin": [{
                "frame_type": "ranged",
                "kind": "authored",
                "range": {
                    "file": {
                        "package_relative_path": "src/lib.rs",
                        "content_sha256": hashlib.sha256(authored).hexdigest(),
                    },
                    "start_byte": source_start,
                    "end_byte": source_start + len(b"ExactToken"),
                },
            }],
            "generated": {
                "artifact": "definition.k",
                "start_byte": generated_start,
                "end_byte": generated_start + len(b"exact"),
            },
        }
        origin, generated = module.exact_mapping(
            definition, {"entries": [entry]}, authored, "src/lib.rs", "ExactToken"
        )
        self.assertEqual(origin["start_byte"], source_start)
        self.assertEqual(generated["start_byte"], generated_start)

        entry["origin"][0]["range"]["file"]["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(module.FrontendProbeError, "expected one exact sidecar mapping"):
            module.exact_mapping(
                definition, {"entries": [entry]}, authored, "src/lib.rs", "ExactToken"
            )


if __name__ == "__main__":
    unittest.main()
