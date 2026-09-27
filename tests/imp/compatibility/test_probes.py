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
            with self.assertRaises(module.GateError):
                module.verify(report)


class DiagnosticProbeTests(unittest.TestCase):
    def test_k_frontend_mapping_requires_exact_content_identity(self) -> None:
        module = load(HERE / "diagnostics/k-frontend/probe.py", "frontend_probe")
        authored = b"before ExactToken after\n"
        spec = b"module M-SPEC\n  claim exact\nendmodule\n"
        source_start = authored.index(b"ExactToken")
        generated_start = spec.index(b"exact")
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
                "artifact": "spec.k",
                "start_byte": generated_start,
                "end_byte": generated_start + len(b"exact"),
            },
        }
        origin, generated = module.exact_mapping(
            spec, {"entries": [entry]}, authored, "src/lib.rs", "ExactToken"
        )
        self.assertEqual(origin["start_byte"], source_start)
        self.assertEqual(generated["start_byte"], generated_start)

        entry["origin"][0]["range"]["file"]["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(module.GateError, "expected one exact sidecar mapping"):
            module.exact_mapping(
                spec, {"entries": [entry]}, authored, "src/lib.rs", "ExactToken"
            )


if __name__ == "__main__":
    unittest.main()
