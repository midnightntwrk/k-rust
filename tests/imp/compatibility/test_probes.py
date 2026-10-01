from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest
from unittest import mock


HERE = Path(__file__).resolve().parent


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class DiagnosticProbeTests(unittest.TestCase):
    def test_k_frontend_mapping_delegates_exact_content_selection(self) -> None:
        module = load(HERE / "diagnostics/k-frontend/probe.py", "frontend_probe")
        result = {"authored_range": {"start_byte": 7}, "generated": {"start_byte": 6}}
        with mock.patch.object(module.krs_gate, "ir_query", return_value=result) as query, mock.patch.object(module, "z3_environment", return_value={}):
            self.assertEqual(module.exact_mapping(Path("gate"), Path("emitted"), Path("authored.rs"), "src/lib.rs", "ExactToken"), (result["authored_range"], result["generated"]))
            query.assert_called_once_with(Path("gate"), Path("emitted"), {
                "kind": "source_token", "artifact": "spec.k", "authored": "authored.rs",
                "package_relative_path": "src/lib.rs", "token": "ExactToken",
            }, environment={})
        with mock.patch.object(module.krs_gate, "ir_query", side_effect=module.GateError("expected one exact sidecar mapping")):
            with self.assertRaisesRegex(module.GateError, "expected one exact sidecar mapping"):
                module.exact_mapping(Path("gate"), Path("emitted"), Path("authored.rs"), "src/lib.rs", "ExactToken")


if __name__ == "__main__":
    unittest.main()
