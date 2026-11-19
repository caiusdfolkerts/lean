#!/usr/bin/env python3
"""Spend bounded producer time to reduce subsequent kernel verification work.

Re-solving a dependency core removes clauses the original solver retained
only because of its search order. A small deterministic ordering portfolio
can also shorten the refutation. The minimum-cost proof is kept; every output
clause retains its typed semantic witness and the ordinary kernel remains
the sole mathematical checker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time

from generate_facet_sat_certificates import Formula, trim


def proof_cost(core: dict) -> int:
    """A producer heuristic, not a theorem or a measured runtime prediction."""
    return 8 * len(core['clauses']) + 5 * core['derived_clauses'] + core['retained_hints']


def permute_core(core: dict, seed: int) -> Formula:
    order = list(range(len(core['atoms'])))
    if seed:
        random.Random(seed).shuffle(order)
    mapping = {old + 1: new + 1 for new, old in enumerate(order)}
    def remap(literal):
        return literal if isinstance(literal, bool) else (
            mapping[abs(literal)] * (1 if literal > 0 else -1))
    formula = Formula(0)
    formula.atoms = [core['atoms'][i] for i in order]
    formula.clauses = [[remap(literal) for literal in clause] for clause in core['clauses']]
    formula.rules = [{**rule, 'full_literals': [remap(lit) for lit in rule['full_literals']]}
                     for rule in core['rules']]
    return formula


def minimize(case: dict, solver: Path, directory: Path, *, rounds: int = 8, seconds: int = 1) -> dict:
    if case.get('status') != 'unsat' or rounds <= 0 or seconds <= 0:
        raise ValueError('a completed certificate and positive search budgets are required')
    directory.mkdir(parents=True, exist_ok=True)
    original = case['core']
    best, current = original, original
    history = []
    started = time.monotonic()
    for index in range(rounds):
        # First shrink the current core. Periodically restart from the best
        # proof so that a smaller but harder core cannot trap every attempt.
        source = best if index % 4 == 3 else current
        seed = 0 if index < 2 else index - 1
        formula = permute_core(source, seed)
        cnf, lrat = directory / 'input.cnf', directory / 'proof.lrat'
        cnf.write_text(formula.dimacs())
        options = ['--phase=false'] if index % 4 == 2 else []
        proc = subprocess.run([str(solver), '-q', '--lrat', '--no-binary', '-t', str(seconds),
                               *options, str(cnf), str(lrat)], stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, timeout=seconds + 5)
        if proc.returncode == 10:
            raise ValueError('a previously refuted clause core became satisfiable')
        if proc.returncode == 0:
            history.append(dict(round=index, status='budget'))
            continue
        if proc.returncode != 20:
            raise ValueError('solver refinement failed: ' + proc.stdout[-2000:])
        current = trim(formula, lrat.read_text())
        cost = proof_cost(current)
        history.append(dict(round=index, seed=seed, options=options, initial=len(current['clauses']),
                            derived=current['derived_clauses'], hints=current['retained_hints'], cost=cost))
        if cost < proof_cost(best):
            best = current
    return {**case, 'core': best, 'refinement': dict(
        original_cost=proof_cost(original), cost=proof_cost(best), rounds=rounds,
        seconds=time.monotonic() - started, history=history,
        input_core_sha256=hashlib.sha256(json.dumps(original, sort_keys=True).encode()).hexdigest())}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path, help='one certificate or a replacement manifest')
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--rounds', type=int, default=8)
    p.add_argument('--seconds', type=int, default=1)
    p.add_argument('--max-cases', type=int, default=1)
    p.add_argument('--minimum-nodes', type=int, default=64)
    args = p.parse_args()
    value = json.loads(args.input.read_text())
    if isinstance(value, dict):
        result = minimize(value, args.solver, args.output.with_suffix(''),
                          rounds=args.rounds, seconds=args.seconds)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
        print(json.dumps(result['refinement']))
        return
    if args.max_cases <= 0:
        p.error('the manifest case budget must be positive')
    args.output.mkdir(parents=True, exist_ok=True)
    report = []
    processed = 0
    for entry in value:
        if 'file' not in entry:
            report.append(entry)
            continue
        source = args.input.parent / entry['file']
        encoded = source.read_bytes()
        if hashlib.sha256(encoded).hexdigest() != entry['sha256']:
            raise ValueError('source certificate does not match its manifest')
        updated = dict(entry)
        if (entry['method'] == 'unsat' and entry['old_nodes'] >= args.minimum_nodes and
                processed < args.max_cases):
            case = minimize(json.loads(encoded), args.solver, args.output / 'solver-temporary',
                            rounds=args.rounds, seconds=args.seconds)
            encoded = (json.dumps(case, separators=(',', ':')) + '\n').encode()
            core = case['core']
            updated.update(initial=len(core['clauses']), derived=core['derived_clauses'],
                           hints=core['retained_hints'], refinement=case['refinement'])
            processed += 1
        (args.output / entry['file']).write_bytes(encoded)
        updated.update(sha256=hashlib.sha256(encoded).hexdigest(), bytes=len(encoded))
        report.append(updated)
        if processed and processed % 25 == 0 and updated['method'] == 'unsat':
            print(json.dumps(dict(refined=processed, entries=len(report))), flush=True)
            (args.output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    (args.output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(refined=processed, entries=len(report))), flush=True)


if __name__ == '__main__':
    main()
