#!/usr/bin/env python3
"""Regenerate a bounded set of SAT certificates using incompatible facet groups.

This is untrusted proof search. The selected certificate is later translated
to an ordinary Lean proof, including the class partition and quota theorem.
Original certificates remain the fallback if grouping produces a larger core
or the solver exhausts its explicit budget.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import time

from generate_facet_sat_certificates import SatCell, solve
from minimize_facet_sat_certificates import minimize, proof_cost


def write_manifest(path: Path, report: list[dict]) -> None:
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(path)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('manifest', type=Path)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--max-cases', type=int, default=1)
    p.add_argument('--seconds', type=int, default=1)
    p.add_argument('--rounds', type=int, default=3)
    p.add_argument('--alternative-manifest', type=Path,
                   help='also consider already refined certificates with the same geometry')
    args = p.parse_args()
    if args.max_cases <= 0 or args.seconds <= 0 or args.rounds < 0:
        p.error('positive case and solver budgets, and nonnegative refinement rounds, are required')
    source = json.loads(args.manifest.read_text())
    alternatives = ({entry['record']: entry for entry in json.loads(args.alternative_manifest.read_text())}
                    if args.alternative_manifest else {})
    args.output.mkdir(parents=True, exist_ok=True)
    report = []
    processed = 0
    started = time.monotonic()
    for entry in source:
        if 'file' not in entry:
            report.append(entry)
            continue
        encoded = (args.manifest.parent / entry['file']).read_bytes()
        if hashlib.sha256(encoded).hexdigest() != entry['sha256']:
            raise ValueError('source certificate differs from its manifest')
        result = json.loads(encoded)
        updated = dict(entry)
        if entry['method'] == 'unsat' and processed < args.max_cases:
            original = result
            alternative = alternatives.get(entry['record'])
            if alternative is not None and alternative['method'] == 'unsat':
                other_bytes = (args.alternative_manifest.parent / alternative['file']).read_bytes()
                if hashlib.sha256(other_bytes).hexdigest() != alternative['sha256']:
                    raise ValueError('alternative certificate differs from its manifest')
                other = json.loads(other_bytes)
                if any(other.get(key) != original.get(key)
                       for key in ('record', 'row', 'complement', 'quota', 'cells', 'orbits')):
                    raise ValueError('alternative certificate has different geometry or terminal orbits')
                if proof_cost(other['core']) < proof_cost(result['core']):
                    result = other
            grouped = solve([SatCell(**cell) for cell in original['cells']], tuple(original['quota']),
                            args.solver, args.output / 'solver-temporary', seconds=args.seconds,
                            counter='grouped', orbits=original.get('orbits'))
            grouped.update({key: original[key] for key in ('record', 'row', 'complement', 'method')
                            if key in original})
            if grouped['status'] == 'sat':
                raise ValueError('equivalent grouped constraints became satisfiable')
            if grouped['status'] == 'unsat':
                if args.rounds:
                    grouped = minimize(grouped, args.solver, args.output / 'refine-temporary',
                                       rounds=args.rounds, seconds=args.seconds)
                if proof_cost(grouped['core']) < proof_cost(result['core']):
                    result = grouped
            core = result['core']
            updated.update(counter=result['counter'], initial=len(core['clauses']),
                           derived=core['derived_clauses'], hints=core['retained_hints'],
                           original_cost=proof_cost(original['core']), cost=proof_cost(core),
                           grouped_status=grouped['status'])
            processed += 1
            encoded = (json.dumps(result, separators=(',', ':')) + '\n').encode()
        (args.output / entry['file']).write_bytes(encoded)
        updated.update(sha256=hashlib.sha256(encoded).hexdigest(), bytes=len(encoded))
        report.append(updated)
        if processed and processed % 25 == 0 and entry['method'] == 'unsat':
            write_manifest(args.output / 'manifest.json', report)
            print(json.dumps(dict(processed=processed, entries=len(report),
                                  methods=dict(Counter(r.get('counter', r['method']) for r in report)),
                                  seconds=round(time.monotonic() - started, 2))), flush=True)
    write_manifest(args.output / 'manifest.json', report)
    print(json.dumps(dict(processed=processed, entries=len(report),
                          methods=dict(Counter(r.get('counter', r['method']) for r in report)),
                          seconds=round(time.monotonic() - started, 2))), flush=True)


if __name__ == '__main__':
    main()
