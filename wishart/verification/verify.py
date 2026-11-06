#!/usr/bin/env python3
"""Build Wishart and bind its kernel audit to the exact source and dependencies.

The normal reader command is ``lake build``. This optional publication command
also writes a durable receipt. A failed or interrupted run never records success.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent.parent
REPORTS = ROOT / ".lake/reports"
RECEIPT = REPORTS / "build-result.json"
AUDIT = REPORTS / "audit/kernel-dependencies.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def snapshot() -> dict[str, str]:
    paths = list((ROOT / "source").rglob("*.lean"))
    paths += [ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
              ROOT / "paper.pdf", ROOT / "verification/required-endpoints.json",
              ROOT / "verification/endpoint-modules.json", ROOT / "verification/generate_audit.py",
              Path(__file__).resolve()]
    return {p.relative_to(ROOT).as_posix(): sha256(p) for p in sorted(paths)}


def capture(argv: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(argv, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def compiler_identity() -> dict[str, object]:
    # Resolve the compiler selected by Lake, not an ambient elan launcher.
    prefix = Path(capture(["lake", "env", "lean", "--print-prefix"])).resolve(strict=True)
    executable = (prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")).resolve(
        strict=True
    )
    # These locations follow Lake.Config.InstallPath. Windows splits the core
    # runtime across DLLs; the other release platforms also ship these names.
    library_directory = prefix / "bin" if os.name == "nt" else prefix / "lib/lean"
    extension = ".dll" if os.name == "nt" else ".dylib" if sys.platform == "darwin" else ".so"
    shared_library = (library_directory / ("libleanshared" + extension)).resolve(strict=True)
    core_libraries = []
    for name in ("libleanshared", "libleanshared_2", "libleanshared_1", "libInit_shared"):
        path = library_directory / (name + extension)
        if path.is_file():
            resolved = path.resolve(strict=True)
            core_libraries.append({"path": str(resolved), "sha256": sha256(resolved)})
    return {
        "lean_prefix": str(prefix),
        "lean_executable": str(executable),
        "lean_executable_sha256": sha256(executable),
        "lean_shared_library": str(shared_library),
        "lean_shared_library_sha256": sha256(shared_library),
        "lean_core_shared_libraries": core_libraries,
    }


def dependencies() -> list[dict[str, object]]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    result = []
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        actual = capture(["git", "rev-parse", "HEAD"], path)
        changes = capture(["git", "status", "--porcelain", "--untracked-files=no"], path)
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        if changes:
            raise RuntimeError(f"Tracked dependency source changed: {package['name']}")
        result.append({"name": package["name"], "url": package["url"],
                       "expected_revision": package["rev"], "actual_revision": actual,
                       "tracked_source_clean": True})
    return result


def main() -> int:
    REPORTS.mkdir(parents=True, exist_ok=True)
    record: dict[str, object] = {
        "format": "wishart-build-receipt-v1",
        "status": "running",
        "passed": False,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "command": ["lake", "build"],
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    }
    write_json(RECEIPT, record)
    try:
        before = snapshot()
        record["input_sha256"] = before
        record["lean_version"] = capture(["lake", "env", "lean", "--version"])
        expected_version = str(record["toolchain"]).split(":v")[-1]
        if not str(record["lean_version"]).startswith("Lean (version " + expected_version + ","):
            raise RuntimeError("Installed Lean does not match lean-toolchain")
        record["dependencies_before"] = dependencies()
        record.update(compiler_identity())
        record["runtime_preload_present"] = bool(os.environ.get("LD_PRELOAD"))
        record["runtime_preload_sha256"] = {
            Path(path).name: sha256(Path(path))
            for path in os.environ.get("LD_PRELOAD", "").replace(":", " ").split()
            if Path(path).is_file()
        }
        write_json(RECEIPT, record)

        # Rerun the audit once, even when the mathematical build is up to date.
        # Only this project's generated audit artifact and report are removed.
        AUDIT.unlink(missing_ok=True)
        audit_object = ROOT / ".lake/build/lib/lean/verification/complete.olean"
        audit_object.unlink(missing_ok=True)
        log_path = REPORTS / "build.log"
        with log_path.open("wb") as stream:
            exit_code = subprocess.call(["lake", "build"], cwd=ROOT, stdout=stream,
                                        stderr=subprocess.STDOUT)
        record["build_exit_code"] = exit_code
        record["build_log_sha256"] = sha256(log_path)
        if exit_code != 0:
            raise RuntimeError(f"Lake build failed with exit status {exit_code}")
        if not AUDIT.is_file():
            raise RuntimeError("Build did not produce a fresh kernel audit")
        audit = json.loads(AUDIT.read_text())
        expected_roots = json.loads((ROOT / "verification/required-endpoints.json").read_text())
        actual_roots = [root["name"] for root in audit["roots"]]
        if actual_roots != expected_roots:
            raise RuntimeError("Kernel audit endpoint list does not match the fixed request")
        if not audit["kernel_checking_enabled_for_audit"]:
            raise RuntimeError("Kernel audit did not run with checking enabled")
        if set(audit["allowed_axioms"]) != ALLOWED:
            raise RuntimeError("Kernel audit uses an unexpected axiom policy")
        if not audit["project_theorem_count"] or not audit["project_declaration_count"]:
            raise RuntimeError("Kernel audit checked no local mathematics")
        for endpoint in audit["roots"]:
            if endpoint["declaration_kind"] != "theorem" or not endpoint["proof_body_present"]:
                raise RuntimeError("An endpoint is not a theorem with a checked proof")
            if not set(endpoint["axioms"]).issubset(ALLOWED):
                raise RuntimeError("An endpoint depends on an unexpected axiom")
        after = snapshot()
        if before != after:
            raise RuntimeError("Source or configuration changed during verification")
        after_dependencies = dependencies()
        if record["dependencies_before"] != after_dependencies:
            raise RuntimeError("Dependency revisions changed during verification")
        record.update({
            "status": "passed",
            "passed": True,
            "inputs_unchanged": True,
            "dependencies_after": after_dependencies,
            "kernel_audit_sha256": sha256(AUDIT),
            "project_module_count": len(audit["project_modules"]),
            "project_declaration_count": audit["project_declaration_count"],
            "project_theorem_count": audit["project_theorem_count"],
            "selected_endpoint_count": len(actual_roots),
            "selected_dependency_count": audit["selected_dependency_count"],
            "allowed_axioms": sorted(ALLOWED),
            "library_boundary_policy": audit["local_axiom_analysis"],
            "selected_endpoints": audit["roots"],
        })
        print(f"Verified {len(actual_roots)} endpoints; "
              f"{audit['project_theorem_count']} local theorems; source unchanged.")
        return 0
    except BaseException as error:
        record["status"] = "failed" if not isinstance(error, KeyboardInterrupt) else "interrupted"
        record["passed"] = False
        record["error"] = str(error)
        print(f"Verification did not pass: {error}", file=sys.stderr)
        return 130 if isinstance(error, KeyboardInterrupt) else 1
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(RECEIPT, record)


if __name__ == "__main__":
    raise SystemExit(main())
