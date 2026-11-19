#!/usr/bin/env python3
"""Refresh authenticated sources and imports without elaborating case proofs.

The existing eight public verification roots are retained verbatim. Changed
headers are parsed by the pinned Lean executable, not by a regular-expression
approximation to Lean's import syntax. This is a preparation utility; it does
not claim that any source has been proved or that verification has completed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


HELPERS = {
    'CliqueExclusion': 'source/geometry/clique_exclusion.lean',
    'FacetCliqueRaw': 'source/geometry/facet_clique_raw.lean',
    'FacetSat': 'source/geometry/facet_sat.lean',
    'FacetSatCoverage': 'source/geometry/facet_sat_coverage.lean',
    'FacetSatEdges': 'source/geometry/facet_sat_edges.lean',
    'FacetSatGroups': 'source/geometry/facet_sat_groups.lean',
    'FacetSatRaw': 'source/geometry/facet_sat_raw.lean',
    'GraphDirectCore': 'source/geometry/graph_direct_core.lean',
    'GraphDirectCoverage': 'source/geometry/graph_direct_coverage.lean',
    'GraphFacetClique': 'source/geometry/graph_facet_clique.lean',
    'SparseNatLiteral': 'source/geometry/sparse_nat_literal.lean',
    'FacetSatFacts': 'source/pure_rup/facet_sat_facts.lean',
    'FacetSatInitials': 'source/pure_rup/facet_sat_initials.lean',
    'RupProofTerm': 'source/pure_rup/rup_proof_term.lean',
    'SequentialCounter': 'source/pure_rup/sequential_counter.lean',
}


def digest(path: Path) -> str:
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--lean', type=Path, required=True, help='the project-pinned Lean executable')
    p.add_argument('--write', action='store_true')
    p.add_argument('--report', type=Path)
    args = p.parse_args()
    project = args.project.resolve()
    index_path = project / 'verification/source_index.json'
    original = json.loads(index_path.read_text())
    entries = {row['module']: dict(row) for row in original['entries']}
    if len(entries) != len(original['entries']):
        raise ValueError('duplicate original module identity')
    additions = dict(HELPERS)
    for path in sorted((project / 'source/finite/graph_structural').glob('*.lean')):
        match = re.fullmatch(r'graph_inputs_(row\d+|six0)_part(\d+)_structural(\d+)\.lean', path.name)
        if match is None:
            raise ValueError('unknown generated structural module filename: ' + path.name)
        family, part, chunk = match.groups()
        name = 'GraphInputs' + ('Row' + family[3:] if family.startswith('row') else 'Six0')
        additions[name + 'Part' + part + 'Structural' + chunk] = str(path.relative_to(project))
    for name, path in additions.items():
        if name in entries and entries[name]['path'] != path:
            raise ValueError('attempted module identity reassignment: ' + name)
        entries.setdefault(name, dict(module=name, path=path, source_sha256=None, imports=[]))
    changed = []
    by_path = {}
    for name, entry in entries.items():
        path = (project / entry['path']).resolve()
        if not path.is_relative_to(project / 'source') or not path.is_file():
            raise ValueError('missing or out-of-tree source for ' + name)
        if path in by_path:
            raise ValueError('multiple module identities for one source')
        by_path[path] = name
        source_hash = digest(path)
        if source_hash != entry['source_sha256']:
            changed.append(path)
            entry['source_sha256'] = source_hash
    with tempfile.TemporaryDirectory(prefix='lean-source-headers-') as temporary:
        paths_file = Path(temporary) / 'paths.txt'
        paths_file.write_text(''.join(str(path) + '\n' for path in changed))
        process = subprocess.run([str(args.lean.resolve()), '--run',
                                  str(project / 'verification/parse_imports.lean'), str(paths_file)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
        parsed = set()
        for line in process.stdout.splitlines():
            row = json.loads(line)
            path = Path(row['path'])
            if path not in by_path or path in parsed or row['errors']:
                raise ValueError('Lean header parser returned unexpected or invalid source')
            parsed.add(path)
            entries[by_path[path]]['imports'] = row['imports']
        if parsed != set(changed):
            raise ValueError('Lean did not parse every changed source header')
    reachable = set()
    pending = list(original['roots'])
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        if name not in entries:
            raise ValueError('missing public verification root ' + name)
        reachable.add(name)
        pending.extend(dependency for dependency in entries[name]['imports']
                       if dependency in entries and dependency not in reachable)
    removed = sorted(set(entries) - reachable)
    # Every unknown project import is an error; only the pinned external Lean,
    # Std and Mathlib namespaces may be absent from this project-owned index.
    external = ('Init', 'Lean', 'Std', 'Mathlib', 'Batteries', 'Qq', 'Aesop',
                'ProofWidgets', 'ImportGraph', 'Plausible', 'Cli')
    for name in reachable:
        for dependency in entries[name]['imports']:
            if dependency not in entries and not any(
                    dependency == prefix or dependency.startswith(prefix + '.') for prefix in external):
                raise ValueError(f'unindexed project dependency {name} -> {dependency}')
    result = {**original, 'entries': [entries[name] for name in sorted(reachable)]}
    report = dict(roots=original['roots'], modules=len(reachable), parsed_headers=len(changed),
                  added_modules=sorted(reachable - {row['module'] for row in original['entries']}),
                  unreachable_modules=removed, written=args.write)
    if args.write:
        temporary = index_path.with_suffix('.tmp')
        temporary.write_text(json.dumps(result, indent=2) + '\n')
        temporary.replace(index_path)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
