#!/usr/bin/env python3
"""Fetch only the locked library cache required by this project's imports.

Run through `lake env` so Lake materialises the pinned dependency manifest.
No project proof artifacts are fetched or accepted by this script.
"""
from pathlib import Path
import gzip
import json
import subprocess

root = Path(__file__).resolve().parents[1]
index = root / "audit/source-index.json"
if index.exists():
    manifest = json.loads(index.read_text())
else:
    with gzip.open(index.with_suffix(".json.gz"), "rt") as stream:
        manifest = json.load(stream)

imports = sorted({name for entry in manifest["entries"] for name in entry["imports"]
                  if name.startswith("Mathlib.") or name == "Mathlib"})
if not imports:
    raise RuntimeError("No Mathlib imports were found in the source manifest")
print(f"Fetching the pinned library cache for {len(imports)} direct Mathlib imports.", flush=True)
subprocess.run(["lake", "exe", "cache", "get", *imports], cwd=root, check=True)
