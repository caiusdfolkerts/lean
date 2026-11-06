#!/usr/bin/env python3
"""Refresh explicit audit imports and ownership from the fixed endpoint manifest.

This writes source configuration; it does not prove or certify anything. The
resulting Lean audit must be built. Endpoint names and expected owner modules
are reviewed data, not inferred theorem types.
"""
from __future__ import annotations

import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "source/verification/complete.lean"


def replace_region(text: str, begin: str, end: str, contents: str) -> str:
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError(f"Expected exactly one generated region: {begin}")
    before, rest = text.split(begin)
    _, after = rest.split(end)
    return before + begin + "\n" + contents + "\n" + end + after


def main() -> None:
    endpoints = json.loads((ROOT / "verification/required-endpoints.json").read_text())
    owners = json.loads((ROOT / "verification/endpoint-modules.json").read_text())
    if len(endpoints) != len(set(endpoints)) or set(endpoints) != set(owners):
        raise ValueError("Endpoint selection and module ownership do not match")
    modules = sorted(".".join(path.relative_to(ROOT / "source").with_suffix("").parts)
                     for path in (ROOT / "source").rglob("*.lean") if path != AUDIT)
    for endpoint in endpoints:
        if owners[endpoint] not in modules:
            raise ValueError(f"Missing owner module for {endpoint}")
    text = AUDIT.read_text()
    text = replace_region(text, "/- BEGIN GENERATED LOCAL IMPORTS -/",
                          "/- END GENERATED LOCAL IMPORTS -/",
                          "\n".join("import all " + module for module in modules))
    text = replace_region(text, "  -- BEGIN GENERATED OWNED MODULES",
                          "  -- END GENERATED OWNED MODULES",
                          "  let projectModules : Array Name := #[\n" +
                          ",\n".join("    `" + module for module in modules) + "]")
    text = replace_region(text, "  -- BEGIN SELECTED THEOREM ROOTS",
                          "  -- END SELECTED THEOREM ROOTS",
                          "  let roots : Array (String × Name × Name) := #[\n" +
                          ",\n".join(f'    ("{name}", `{name}, `{owners[name]})'
                                      for name in endpoints) + "]")
    text = re.sub(r"The mathematical source and all \d+ endpoint\nselections",
                  "The mathematical source and the fixed endpoint\nselections", text)
    text = text.replace("# Checked kernel audit of the principal theorem closure",
                        "# Checked kernel audit of the complete Wishart development")
    AUDIT.write_text(text)
    print(f"Generated {len(modules)} local module imports and {len(endpoints)} endpoint roots.")


if __name__ == "__main__":
    main()
