"""Exercise the Python entry points with compiler calls replaced by fixtures."""
import contextlib
import fcntl
import gzip
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import audit_exported_proofs
import export_dependencies
import verify


class FinalAuditBindingTests(unittest.TestCase):
    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.root = Path(tmp).resolve()
        self.audits = self.root / ".lake/build/verification"
        self.result = self.audits / "result.json"
        self.receipt = verify.module_receipt_path(self.audits, "Example")
        self.index = self.root / "audit/source-index.json.gz"
        self.source = self.root / "Sources/Example.lean"
        scripts = self.root / "scripts"
        scripts.mkdir()
        here = Path(verify.__file__).parent
        for name in ("verify.py", "export_dependencies.py"):
            shutil.copyfile(here / name, scripts / name)
        shutil.copyfile(here / "export_dependencies.lean", scripts / "ExportDependencies.lean")
        (scripts / "ParseImports.lean").touch()
        self.source.parent.mkdir()
        self.source.write_text("theorem fixture : True := True.intro\n")
        self.index.parent.mkdir()
        self.index_data = json.dumps({"roots": ["Example"], "entries": [{
            "module": "Example", "imports": [], "source_sha256": verify.hash_file(self.source),
        }]}).encode()
        self.index.write_bytes(gzip.compress(self.index_data))
        self.lean = self.root / "lean"
        self.lean.touch()
        self.prefix = self.root / "prefix"
        self.compiles = 0
        self.audit_hook = lambda: None
        self.reader_hook = lambda: None
        self.library_dir = self.root / "library"
        self.library_dir.mkdir()
        self.enterContext(contextlib.redirect_stdout(io.StringIO()))
        for target, name, value in (
            (verify, "run", lambda *cmd: verify.LEAN_COMMIT if cmd[1] == "--githash" else "fixture version"),
            (verify, "library_environment", lambda *_: (
                [self.library_dir], [], {}, self.prefix, {})),
            (verify, "closure_axiom_audit", self.closure_audit),
            (verify.subprocess, "run", self.compiler_call),
            (verify.shutil, "which", lambda _: str(self.lean)),
            (verify.LeanMemoryBudget, "run", lambda _, *args: self.reader_call(*args)),
            (export_dependencies, "__file__", str(scripts / "export_dependencies.py")),
            (export_dependencies.importlib.util, "spec_from_file_location",
             lambda *_: SimpleNamespace(loader=SimpleNamespace(exec_module=lambda _: None))),
            (export_dependencies.importlib.util, "module_from_spec", lambda _: verify),
            (audit_exported_proofs, "load", lambda path, _: {
                "verify.py": verify, "export_dependencies.py": export_dependencies}[path.name]),
        ):
            self.enterContext(patch.object(target, name, value))

    def closure_audit(self, roots, modules, *args):
        self.assertFalse(self.result.exists(), "A build attempt left previous success visible")
        self.audit_hook()
        return {"passed": True, "covered_modules": list(modules)}

    def compiler_call(self, command, **kwargs):
        if "--run" in command:
            row = {"path": str(self.source), "errors": [], "imports": []}
            if "source-imports" in command:
                row.update(module="Example", explicit_imports=[], effective_imports=[], is_module=False)
                Path(command[-1]).write_text(json.dumps(row) + "\n")
            return SimpleNamespace(returncode=0, stdout=json.dumps(row), stderr="")
        self.compiles += 1
        Path(command[command.index("-o") + 1]).write_bytes(b"fixture artifact")
        if "-c" in command:
            Path(command[command.index("-c") + 1]).write_bytes(b"fixture C")
        return SimpleNamespace(returncode=0)

    def reader_call(self, command, env, log, timeout):
        log.touch()
        if "-o" in command:
            Path(command[command.index("-o") + 1]).touch()
        else:
            mode, module, _ = Path(command[-2]).read_text().strip().split("\t")
            Path(command[-1]).write_text(json.dumps({
                "record": "module", "module": module, "mode": mode,
                "imports": [], "is_module": False, "declarations": 0,
            }) + "\n")
            self.reader_hook()
        return command, 0

    def run_entry(self, entry, *args):
        with patch.object(sys, "argv", [entry.__name__, "--project", str(self.root), *map(str, args)]):
            return entry()

    def build(self, *args):
        return self.run_entry(verify.main, "--jobs", 1, *args)

    def export(self, *args):
        return self.run_entry(export_dependencies.main, "--output", self.root / "export", *args)

    def supplement(self):
        return self.run_entry(audit_exported_proofs.main, "--export", self.root / "export",
                              "--output", self.root / "supplement")

    def test_full_export_and_supplement_accept_reused_receipt(self):
        self.assertEqual(self.build(), 0)
        before = self.receipt.read_bytes()
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.receipt.read_bytes(), before)
        # Addition of an unrelated cache artifact permits a compatible rebase.
        (self.library_dir / "Unrelated.olean").touch()
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.compiles, 1)
        self.assertIn("revalidated_from_key", verify.read_json(self.receipt))
        self.assertEqual(self.export(), 0)
        self.supplement()
        self.assertTrue(verify.read_json(self.root / "supplement/proof-body-audit.json")["passed"])

    def test_interruption_keeps_receipts_and_revokes_success(self):
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.build("--plan"), 0)
        self.assertTrue(self.result.exists())
        with (self.audits / "build.lock").open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            with self.assertRaisesRegex(RuntimeError, "Another verifier"):
                self.build()
            self.assertTrue(self.result.exists())
        def interrupt():
            raise KeyboardInterrupt
        self.audit_hook = interrupt
        with self.assertRaises(KeyboardInterrupt):
            self.build()
        self.assertTrue(self.receipt.is_file())
        self.assertFalse(self.result.exists())
        with self.assertRaises(FileNotFoundError):
            self.export()

    def test_changed_receipt_at_closeout_revokes_success(self):
        def update_receipt():
            self.receipt.write_bytes(self.receipt.read_bytes() + b"\n")
        self.audit_hook = update_receipt
        self.assertEqual(self.build(), 1)
        result = verify.read_json(self.result)
        self.assertFalse(result["passed"])
        self.assertNotIn("verification_binding", result)

    def test_bad_cached_fingerprint_is_rebuilt(self):
        self.assertEqual(self.build(), 0)
        receipt = verify.read_json(self.receipt)
        receipt["key"] = "stale fingerprint"
        verify.write_json(self.receipt, receipt)
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.compiles, 2)

    def test_unrecorded_artifact_facet_is_not_reused(self):
        self.assertEqual(self.build(), 0)
        extra = self.root / ".lake/build/lib/lean/Example.olean.private"
        extra.touch()
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.compiles, 2)
        self.assertFalse(extra.exists())

    def test_export_rejects_different_receipt_bytes_or_index(self):
        self.assertEqual(self.build(), 0)
        before = self.receipt.read_bytes()
        self.receipt.write_bytes(before + b"\n")
        with self.assertRaisesRegex(RuntimeError, "receipts differ"):
            self.export()
        self.receipt.write_bytes(before)
        self.index.write_bytes(gzip.compress(self.index_data + b"\n"))
        with self.assertRaisesRegex(RuntimeError, "bound to this source index"):
            self.export()

    def test_export_rejects_legacy_result_or_different_policy(self):
        self.assertEqual(self.build(), 0)
        result = verify.read_json(self.result)
        binding = result.pop("verification_binding")
        verify.write_json(self.result, result)
        with self.assertRaisesRegex(RuntimeError, "requires a fresh closure audit"):
            self.export()
        result["verification_binding"] = binding
        result["verification_binding"]["axiom_policy_sha256"] = "different-policy"
        verify.write_json(self.result, result)
        with self.assertRaisesRegex(RuntimeError, "requires a fresh closure audit"):
            self.export()

    def test_supplement_rejects_previous_result_and_missing_receipt(self):
        self.assertEqual(self.build(), 0)
        self.assertEqual(self.export(), 0)
        before = self.result.read_bytes()
        self.result.write_bytes(before + b"\n")
        with self.assertRaisesRegex(RuntimeError, "different successful closure axiom audit"):
            self.supplement()
        self.result.write_bytes(before)
        bundle = self.root / "export"
        inputs = bundle / "verified-inputs.jsonl.gz"
        manifest_path = bundle / "extraction-manifest.json"
        manifest = verify.read_json(manifest_path)
        with gzip.open(inputs, "rt") as stream:
            rows = [json.loads(line) for line in stream]

        def replace_input_rows(values):
            with gzip.open(inputs, "wt") as stream:
                stream.writelines(json.dumps(row) + "\n" for row in values)
            manifest["files"][inputs.name] = verify.hash_file(inputs)
            verify.write_json(manifest_path, manifest)

        replace_input_rows(row for row in rows if row.get("path") != str(self.receipt))
        with self.assertRaisesRegex(RuntimeError, "missing the audited receipt"):
            self.supplement()
        project_row = next(row for row in rows if row.get("scope") == "project")
        project_row["receipt_sha256"] = "different receipt"
        replace_input_rows(rows)
        with self.assertRaisesRegex(RuntimeError, "project receipt rows differ"):
            self.supplement()

    def test_native_alias_checked_at_both_export_and_supplement_boundaries(self):
        for name in ("bin", "lib", "include"):
            (self.prefix / name).mkdir(parents=True)
        for name in ("leanc", "clang", "ld.lld"):
            (self.prefix / "bin" / name).touch()
        lib = self.prefix / "lib"
        (lib / "first.so").write_bytes(b"original native input")
        (lib / "second.so").write_bytes(b"other native input")
        alias = lib / "selected.so"
        alias.symlink_to("first.so")

        def retarget():
            alias.unlink()
            alias.symlink_to("second.so")

        def native_command(command, cwd, env, log, timeout):
            log.touch()
            Path(command[command.index("-o") + 1]).write_bytes(b"fixture native artifact")
            return 0

        self.enterContext(patch.object(verify, "NATIVE_PRODUCERS", {"Example": "initialize_Example"}))
        self.enterContext(patch.object(verify, "run_native_command", native_command))
        self.assertEqual(self.build(), 0)
        self.reader_hook = retarget
        with self.assertRaisesRegex(RuntimeError, "toolchain inventory changed"):
            self.export()
        bundle = self.root / "export"
        self.assertFalse((bundle / "extraction-manifest.json").exists())
        shutil.rmtree(bundle)
        alias.unlink()
        alias.symlink_to("first.so")
        self.reader_hook = lambda: None
        self.assertEqual(self.export(), 0)

        retarget()
        with self.assertRaisesRegex(RuntimeError, "toolchain inventory changed"):
            self.supplement()
        self.assertFalse((self.root / "supplement").exists())
        alias.unlink()
        alias.symlink_to("first.so")

        def before_supplement_closeout(*args):
            retarget()
            return iter(())

        with patch.object(verify, "bounded_parallel_map", before_supplement_closeout):
            with self.assertRaisesRegex(RuntimeError, "toolchain inventory changed"):
                self.supplement()
        self.assertFalse((self.root / "supplement/proof-body-audit.json").exists())


if __name__ == "__main__":
    unittest.main()
