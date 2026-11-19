#!/usr/bin/env python3
"""Find cheaper certificates for an explicitly bounded set of graph cases.

This command does not run any existing Lean growth verification. It reads
closed certificate data, tries a bounded clique proof, and optionally asks a
SAT solver for a terminal coverage certificate. Outputs are untrusted until
the emitted Lean source is checked by the ordinary kernel.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import time

from generate_clique_certificates import QUOTAS, adjacency, search
from generate_facet_sat_certificates import PROJECT, solve, universe
from read_graph_records import Records, entries, fields, leaf_orbits, natural


def case_keys(project: Path) -> list[dict]:
    pattern = re.compile(r'\(\.leaf ⟨\((\d+), (\d+)\), ([\w.]+)_result⟩\)')
    cases = []
    for path in sorted((project / 'source/finite/graph_compact_block').rglob('*.lean')):
        cases.extend(dict(row=int(row), complement=int(mask), record=name)
                     for row, mask, name in pattern.findall(path.read_text()))
    if len(cases) != len({case['record'] for case in cases}):
        raise ValueError('a compact route names the same raw record more than once')
    return sorted(cases, key=lambda case: case['record'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=PROJECT)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--max-cases', type=int, default=1)
    p.add_argument('--minimum-nodes', type=int, default=64)
    p.add_argument('--maximum-clique-ratio', type=float, default=0.35)
    p.add_argument('--clique-seconds', type=float, default=0.1)
    p.add_argument('--solver', type=Path)
    p.add_argument('--solver-seconds', type=int, default=1)
    p.add_argument('--counter', choices=['totalizer', 'grouped'], default='grouped')
    p.add_argument('--edge-cover', action='store_true', help='include the original required-edge conditions')
    p.add_argument('--refinement-rounds', type=int, default=0)
    p.add_argument('--selection-manifest', type=Path,
                   help='reuse original case sizes after retiring stored growth searches')
    p.add_argument('--row', type=int, action='append', choices=sorted(QUOTAS))
    p.add_argument('--skip', type=int, default=0)
    args = p.parse_args()
    if args.max_cases <= 0 or args.minimum_nodes < 0 or args.skip < 0 or args.refinement_rounds < 0:
        p.error('the case budget must be positive and other counts nonnegative')
    if not 0 < args.maximum_clique_ratio <= 2 or args.clique_seconds <= 0:
        p.error('invalid clique search budget')
    args.output.mkdir(parents=True, exist_ok=True)
    records = Records(args.project)
    pool = universe(args.project, six=args.row is None or 32 in args.row)
    report = []
    selection = ({entry['record']: entry for entry in json.loads(args.selection_manifest.read_text())}
                 if args.selection_manifest else None)
    eligible = 0
    started = time.monotonic()
    for case in case_keys(args.project):
        if args.row is not None and case['row'] not in args.row:
            continue
        if selection is not None and case['record'] not in selection:
            continue
        raw = records.get(case['record'])
        old_nodes = (selection[case['record']]['old_nodes'] if selection is not None
                     else natural(raw['nodePred']) + 1)
        if selection is not None and any(selection[case['record']][key] != case[key]
                                         for key in ('row', 'complement')):
            raise ValueError('the selected original route does not match the source')
        if old_nodes < args.minimum_nodes:
            continue
        eligible += 1
        if eligible <= args.skip:
            continue
        if len(report) >= args.max_cases:
            break
        n = natural(raw['cellPred']) + 1
        ids = entries(fields(raw['embedding']), n)
        cells = [pool[i] for i in ids]
        if entries(fields(raw['cells']), n) != [cell.cell_code for cell in cells]:
            raise ValueError(f'cell alignment failed for {case["record"]}')
        quota = QUOTAS[case['row']]
        if tuple(entries(fields(raw['quota']), len(quota))) != quota:
            raise ValueError(f'quota mismatch for {case["record"]}')
        summary = {**case, 'old_nodes': old_nodes, 'candidates': n}
        best = None
        for kinds in ((2,), (2, 3), (1, 2, 3, 4)):
            subset = [cell for cell in cells if cell.kind in kinds]
            required = tuple(q if key in kinds else 0 for key, q in enumerate(quota))
            if not any(required):
                continue
            result = search(adjacency(subset), [cell.kind for cell in subset], required,
                            limit=max(1, int(old_nodes * args.maximum_clique_ratio)),
                            seconds=args.clique_seconds)
            if result['status'] == 'excluded':
                cost = result['visits'] * max(1, len(subset))
                if best is None or cost < best[0]:
                    best = (cost, {**case, **result, 'method': 'clique', 'kinds': kinds,
                                   'quota': required, 'candidates': [cell.__dict__ for cell in subset]})
        if best is not None:
            result = best[1]
            summary.update(method='clique', visits=result['visits'], unique_nodes=len(result['nodes']),
                           local_candidates=len(result['candidates']))
        elif args.solver:
            orbits = leaf_orbits(raw, [cell.kind for cell in cells], quota)
            result = solve(cells, quota, args.solver, args.output / 'solver-temporary',
                           seconds=args.solver_seconds, counter=args.counter, orbits=orbits,
                           required_edges=natural(raw['requiredEdges']) if args.edge_cover else None)
            result.update(case, method='sat')
            if result['status'] == 'unsat' and args.refinement_rounds:
                from minimize_facet_sat_certificates import minimize
                result = minimize(result, args.solver, args.output / 'refine-temporary',
                                  rounds=args.refinement_rounds, seconds=args.solver_seconds)
            summary.update(method=result['status'], orbits=len(orbits))
            if result['status'] == 'unsat':
                core = result['core']
                summary.update(initial=len(core['clauses']), derived=core['derived_clauses'],
                               hints=core['retained_hints'])
        else:
            result = None
            summary.update(method='fallback')
        if result and result['status'] in ('excluded', 'unsat'):
            name = f'row{case["row"]}_{case["complement"]}.json'
            data = (json.dumps(result, separators=(',', ':')) + '\n').encode()
            (args.output / name).write_bytes(data)
            summary.update(file=name, sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
        report.append(summary)
        if len(report) % 25 == 0:
            print(json.dumps(dict(processed=len(report), methods=dict(Counter(r['method'] for r in report)),
                                  seconds=round(time.monotonic() - started, 2))), flush=True)
            (args.output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    (args.output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(processed=len(report), methods=dict(Counter(r['method'] for r in report)),
                         old_nodes=sum(r['old_nodes'] for r in report),
                         seconds=round(time.monotonic() - started, 2))), flush=True)


if __name__ == '__main__':
    main()
