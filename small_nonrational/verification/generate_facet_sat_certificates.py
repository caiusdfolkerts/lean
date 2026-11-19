#!/usr/bin/env python3
"""Produce typed, untrusted facet SAT certificates for ordinary Lean replay.

The solver is used only to find a proof. Every retained initial clause records
its geometric or cardinality rule, and every learned clause is checked again
when ordinary proof terms are admitted by Lean's kernel. This module does not
run the existing growth-case verification.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from itertools import combinations
import json
from pathlib import Path
import re
import subprocess
import time

from generate_clique_certificates import Cell, QUOTAS, adjacency, compatible, pack, unpack_list

PROJECT = Path(__file__).resolve().parents[1]
PAIR_MASKS = tuple((1 << a) | (1 << b) for a, b in combinations(range(10), 2))
PAIR_INDEX = {mask: i for i, mask in enumerate(PAIR_MASKS)}
WITHIN = tuple(sum(1 << i for i, pair in enumerate(PAIR_MASKS) if vertices & pair == pair)
               for vertices in range(1024))


@dataclass(frozen=True)
class SatCell(Cell):
    cell_code: int
    ridges: tuple[int, ...]


def make_cell(index: int, kind: int, vertices: int, edges: list[int], ridges: list[int]) -> SatCell:
    if not 0 <= kind < 5 or not 0 <= vertices < 1024:
        raise ValueError('invalid cell header')
    if any(edge not in PAIR_INDEX for edge in edges) or any(not 0 <= q < 1024 for q in ridges):
        raise ValueError('invalid cell incidence')
    if len(set(edges)) != len(edges) or len(set(ridges)) != len(ridges):
        raise ValueError('duplicate cell incidences')
    edge_mask = sum(1 << PAIR_INDEX[edge] for edge in edges)
    if edge_mask & ~WITHIN[vertices]:
        raise ValueError('cell edge is outside its vertices')
    faces = sum(1 << q for q in edges + ridges)
    code = kind | (vertices << 5) | (len(edges) << 15)
    shift = 20
    for edge in edges:
        code |= edge << shift
        shift += 10
    code |= len(ridges) << shift
    shift += 5
    for ridge in ridges:
        code |= ridge << shift
        shift += 10
    if shift > 512:
        raise ValueError('cell does not fit the existing checked pool layout')
    return SatCell(index, kind, vertices, faces, WITHIN[vertices] ^ edge_mask, code, tuple(ridges))


def universe(project: Path = PROJECT, *, six: bool = False) -> list[SatCell]:
    text = (project / 'source/geometry/full_small_facet_universe.lean').read_text()
    codes = [int(s) for s in re.findall(r'\(\.leaf (\d+)\)', text)]
    if len(codes) != 6510:
        raise ValueError('the small universe must contain exactly 6510 cells')
    result = []
    for index, code in enumerate(codes):
        edges, rest = unpack_list(code >> 32)
        ridges, rest = unpack_list(rest)
        if rest:
            raise ValueError('unexpected trailing packed cell data')
        result.append(make_cell(index, code & 65535, (code >> 16) & 65535, edges, ridges))
    if six:
        paths = sorted((project / 'source/finite/full_six').glob('full_six0_facet_universe_data_part*.lean'))
        suffix = [int(s) for path in paths for s in re.findall(r'\(\.leaf (\d+)\)', path.read_text())]
        if len(suffix) != 37800:
            raise ValueError('the six-facet suffix must contain exactly 37800 cells')
        for index, code in enumerate(suffix, start=6510):
            digits = [(code >> (10 * j)) & 1023 for j in range(21)]
            if code >> 210:
                raise ValueError('unexpected trailing six-facet cell data')
            result.append(make_cell(index, 4, digits[0], digits[1:13], digits[13:21]))
    return result


def candidates(cells: list[SatCell], complement: int, quotas: tuple[int, ...]) -> list[SatCell]:
    if not 0 <= complement < 1 << 45:
        raise ValueError('the graph complement must fit 45 bits')
    return [cell for cell in cells if quotas[cell.kind] > 0 and
            WITHIN[cell.vertices] & complement == cell.missing]


def negate(literal: int | bool) -> int | bool:
    return not literal if isinstance(literal, bool) else -literal


class Formula:
    def __init__(self, count: int):
        self.atoms = [{'tag': 'facet', 'index': i} for i in range(count)]
        self.clauses: list[list[int]] = []
        self.rules: list[dict] = []
        self.groupings: list[dict] = []

    def variable(self, atom: dict) -> int:
        self.atoms.append(atom)
        return len(self.atoms)

    def add(self, rule: dict, *literals: int | bool) -> None:
        if any(literal is True for literal in literals):
            return
        reduced = [literal for literal in literals if literal is not False]
        if any(not isinstance(literal, int) or literal == 0 for literal in reduced):
            raise ValueError('invalid CNF literal')
        if any(-literal in reduced for literal in reduced):
            return
        self.clauses.append(list(dict.fromkeys(reduced)))
        self.rules.append({**rule, 'full_literals': list(literals)})

    def counter(self, variables: list[int], quota: int, kind: int, *, lower_only: bool) -> None:
        maximum = quota if lower_only else quota + 1
        if maximum == 0:
            return
        previous: list[int | bool] = [True] + [False] * maximum
        for position, vertex in enumerate(variables):
            current: list[int | bool] = [True]
            for threshold in range(1, maximum + 1):
                y = self.variable(dict(tag='counter', kind=kind, prefix=position + 1, threshold=threshold))
                a, b = previous[threshold], previous[threshold - 1]
                rule = dict(tag='counter', kind=kind, position=position, threshold=threshold)
                self.add({**rule, 'gate': 'carry'}, negate(a), y)
                self.add({**rule, 'gate': 'take'}, -vertex, negate(b), y)
                self.add({**rule, 'gate': 'previous_or_selected'}, -y, a, vertex)
                self.add({**rule, 'gate': 'previous_or_lower'}, -y, a, b)
                current.append(y)
            previous = current
        self.add(dict(tag='quota_lower', kind=kind, quota=quota), previous[quota])
        if not lower_only:
            self.add(dict(tag='quota_upper', kind=kind, quota=quota), negate(previous[quota + 1]))

    def totalizer(self, variables: list[int], quota: int, kind: int, *, lower_only: bool,
                  group_indices: list[int] | None = None) -> None:
        """Count variables with explicit semantic indices, independently of CNF IDs."""
        grouped = group_indices is not None
        indices = dict(zip(variables, group_indices if grouped else [v - 1 for v in variables], strict=True))
        if len(indices) != len(variables):
            raise ValueError('a cardinality input is repeated')
        maximum = quota if lower_only else quota + 1
        if maximum == 0:
            return
        def at(values, threshold):
            return values[threshold] if threshold < len(values) else False
        def build(vertices):
            if not vertices:
                return [True]
            if len(vertices) == 1:
                return [True, vertices[0]]
            middle = len(vertices) // 2
            lv, rv = vertices[:middle], vertices[middle:]
            left, right = build(lv), build(rv)
            output = [True] + [self.variable(dict(tag='group_totalizer' if grouped else 'totalizer', kind=kind,
                       vertices=[indices[v] for v in vertices], threshold=t))
                       for t in range(1, min(len(vertices), maximum) + 1)]
            for a in range(min(len(lv), maximum) + 1):
                for b in range(min(len(rv), maximum) + 1):
                    rule = dict(tag='merge', kind=kind, left=[indices[v] for v in lv],
                                right=[indices[v] for v in rv], a=a, b=b)
                    if grouped:
                        rule['grouped'] = True
                    if 0 < a + b <= maximum:
                        self.add({**rule, 'direction': 'forward'},
                                 negate(at(left, a)), negate(at(right, b)), at(output, a + b))
                    if a + b + 1 <= min(len(vertices), maximum):
                        self.add({**rule, 'direction': 'backward'},
                                 negate(at(output, a + b + 1)), at(left, a + 1), at(right, b + 1))
            return output
        result = build(variables)
        rule = dict(kind=kind, quota=quota)
        if grouped:
            rule['grouped'] = True
        self.add(dict(tag='quota_lower', **rule), at(result, quota))
        if not lower_only:
            self.add(dict(tag='quota_upper', **rule), negate(at(result, quota + 1)))

    def grouped_counter(self, cells: list[SatCell], rows: list[int], quota: int,
                        kind: int, *, lower_only: bool) -> None:
        """Count occupied incompatible classes instead of individual facets.

        Every complete boundary is pairwise compatible. A proper coloring of
        the compatibility graph therefore puts at most one selected facet in
        each class; its exact quota is also the number of occupied classes.
        The generated Lean proof checks the partition and this argument.
        """
        members = incompatible_classes([a for a, cell in enumerate(cells) if cell.kind == kind], rows)
        color = [0] * len(cells)
        variables = []
        for index, vertices in enumerate(members):
            g = self.variable(dict(tag='group', kind=kind, index=index))
            variables.append(g)
            for a in vertices:
                color[a] = index
            self.add(dict(tag='group_or', kind=kind, index=index, members=vertices),
                     -g, *(a + 1 for a in vertices))
            for a in vertices:
                self.add(dict(tag='group_take', kind=kind, index=index, member=a), -(a + 1), g)
        self.groupings.append(dict(kind=kind, count=len(members), members=members, color=color))
        self.totalizer(variables, quota, kind, lower_only=lower_only,
                       group_indices=list(range(len(members))))

    def dimacs(self) -> str:
        return f'p cnf {len(self.atoms)} {len(self.clauses)}\n' + ''.join(
            ' '.join(map(str, clause)) + ' 0\n' for clause in self.clauses)


def incompatible_classes(vertices: list[int], rows: list[int]) -> list[list[int]]:
    """Deterministic saturation-degree coloring of the compatibility graph."""
    colors: dict[int, int] = {}
    classes: list[list[int]] = []
    vertex_mask = sum(1 << a for a in vertices)
    if len(set(vertices)) != len(vertices) or any(not 0 <= a < len(rows) for a in vertices):
        raise ValueError('invalid coloring vertex list')
    while len(colors) < len(vertices):
        a = max((a for a in vertices if a not in colors), key=lambda a: (
            len({colors[b] for b in colors if rows[a] >> b & 1}),
            (rows[a] & vertex_mask).bit_count(), -a))
        forbidden = {colors[b] for b in colors if rows[a] >> b & 1}
        index = next(index for index in range(len(classes) + 1) if index not in forbidden)
        if index == len(classes):
            classes.append([])
        colors[a] = index
        classes[index].append(a)
    return [sorted(group) for group in classes]


def encode(cells: list[SatCell], quota: tuple[int, ...], *, lower_only: bool = False,
           counter: str = 'sequential', orbits: list[dict] | None = None,
           required_edges: int | None = None) -> Formula:
    if counter not in ('sequential', 'totalizer', 'grouped'):
        raise ValueError('unknown cardinality encoding')
    formula = Formula(len(cells))
    rows = adjacency(cells)
    owners: dict[int, list[int]] = {}
    for a, cell in enumerate(cells):
        for b in range(a):
            if not (rows[a] >> b) & 1:
                formula.add(dict(tag='incompatible', a=a, b=b), -(a + 1), -(b + 1))
        for ridge in cell.ridges:
            owners.setdefault(ridge, []).append(a)
    for ridge, vertices in owners.items():
        for a in vertices:
            others = [b for b in vertices if b != a and (rows[a] >> b) & 1]
            formula.add(dict(tag='mate', ridge=ridge, a=a, owners=others),
                        -(a + 1), *(b + 1 for b in others))
        for a, b, c in combinations(vertices, 3):
            if (rows[a] >> b) & (rows[a] >> c) & (rows[b] >> c) & 1:
                formula.add(dict(tag='three', ridge=ridge, vertices=[a, b, c]),
                            -(a + 1), -(b + 1), -(c + 1))
    for kind, required in enumerate(quota):
        vertices = [i + 1 for i, cell in enumerate(cells) if cell.kind == kind]
        if vertices or required:
            if counter == 'grouped':
                formula.grouped_counter(cells, rows, required, kind, lower_only=lower_only)
            else:
                getattr(formula, 'counter' if counter == 'sequential' else 'totalizer')(
                    vertices, required, kind, lower_only=lower_only)
    if lower_only and orbits:
        raise ValueError('terminal blocking requires exact quotas')
    for leaf, orbit in enumerate(orbits or []):
        vertices = orbit['vertices']
        if (len(vertices) != len(set(vertices)) or
                any(not 0 <= c < len(cells) for c in vertices) or
                tuple(sum(cells[c].kind == key for c in vertices)
                      for key in range(len(quota))) != quota):
            raise ValueError('terminal blocking requires a complete leaf with exact quotas')
        formula.add(dict(tag='block', leaf=leaf, vertices=vertices),
                    *[-(c + 1) for c in vertices])
    if required_edges is not None:
        if not 0 <= required_edges < 1 << 45:
            raise ValueError('required graph edges must fit the original 45-bit layout')
        for edge in range(45):
            if required_edges >> edge & 1:
                owners = [i for i, cell in enumerate(cells)
                          if (WITHIN[cell.vertices] ^ cell.missing) >> edge & 1]
                formula.add(dict(tag='edge', edge=edge, owners=owners), *(i + 1 for i in owners))
    return formula


def parse_rup(text: str, initial_count: int) -> tuple[dict[int, tuple[list[int], list[int]]], int]:
    steps = {}
    final = None
    for line in text.splitlines():
        words = line.split()
        if not words:
            continue
        identifier = int(words[0])
        if len(words) > 1 and words[1] == 'd':
            continue
        values = list(map(int, words[1:]))
        if not values or values[-1] != 0:
            raise ValueError('unterminated LRAT record')
        zero = values.index(0)
        clause, hints = values[:zero], values[zero + 1:-1]
        if identifier <= initial_count or identifier in steps:
            raise ValueError('repeated or colliding LRAT clause identifier')
        if any(hint <= 0 or hint >= identifier for hint in hints):
            raise ValueError('only backward RUP hints are supported')
        steps[identifier] = clause, hints
        if not clause:
            final = identifier
    if final is None:
        raise ValueError('the certificate does not derive the empty clause')
    return steps, final


def prune_rup_dependencies(clause: list[int], hints: list[int], clauses: dict[int, list[int]]) -> list[int]:
    """Discard propagation steps that do not contribute to the final conflict.

    This is an untrusted proof-size optimization. The emitted RUP chain is
    subsequently validated and converted to kernel-checked proof terms.
    """
    known: dict[int, int | None] = {}
    for literal in clause:
        if literal in known:
            return []  # A tautological learned clause needs no premises.
        known[-literal] = None
    events: list[tuple[int, list[int]]] = []
    roots = None
    conflict_hint = None
    for hint in hints:
        current = clauses.get(hint)
        if current is None:
            raise ValueError('missing RUP hint clause')
        if any(literal in known for literal in current):
            raise ValueError('RUP hint is already satisfied')
        unknown = [literal for literal in current if -literal not in known]
        if len(unknown) > 1:
            raise ValueError('RUP hint is not a unit or conflict')
        dependencies = [known[-literal] for literal in current if -literal in known
                        and known[-literal] is not None]
        if not unknown:
            roots, conflict_hint = dependencies, hint
            break
        known[unknown[0]] = len(events)
        events.append((hint, dependencies))
    if roots is None:
        raise ValueError('RUP chain does not finish with a conflict')
    needed: set[int] = set()
    pending = list(roots)
    while pending:
        event = pending.pop()
        if event not in needed:
            needed.add(event)
            pending.extend(events[event][1])
    return [hint for i, (hint, _) in enumerate(events) if i in needed] + [conflict_hint]


def trim(formula: Formula, proof: str) -> dict:
    """Keep the transitive dependency core; retain typed witnesses for every input."""
    empty = next((i for i, clause in enumerate(formula.clauses, start=1) if not clause), None)
    if empty is not None:
        # The semantic rule for this input clause already proves False. Retain
        # one explicit RUP application so the ordinary macro interface is uniform.
        proof = f'{len(formula.clauses) + 1} 0 {empty} 0\n'
    steps, final = parse_rup(proof, len(formula.clauses))
    all_clauses = {i: clause for i, clause in enumerate(formula.clauses, start=1)}
    original_hints = sum(len(hints) for _, hints in steps.values())
    for identifier, (clause, hints) in steps.items():
        steps[identifier] = clause, prune_rup_dependencies(clause, hints, all_clauses)
        all_clauses[identifier] = clause
    needed: set[int] = set()
    pending = [final]
    while pending:
        identifier = pending.pop()
        if identifier in needed:
            continue
        needed.add(identifier)
        if identifier > len(formula.clauses):
            if identifier not in steps:
                raise ValueError('a RUP hint has no clause')
            pending.extend(steps[identifier][1])
    initial = sorted(i for i in needed if i <= len(formula.clauses))
    derived = sorted(i for i in needed if i > len(formula.clauses))
    ids = {old: new for new, old in enumerate(initial + derived, start=1)}
    variables = sorted({abs(lit) for i in initial for lit in formula.clauses[i - 1]} |
                       {abs(lit) for i in derived for lit in steps[i][0]})
    variable_ids = {old: new for new, old in enumerate(variables, start=1)}
    def remap(clause):
        return [variable_ids[abs(lit)] * (1 if lit > 0 else -1) for lit in clause]
    clauses = [remap(formula.clauses[i - 1]) for i in initial]
    cnf = f'p cnf {len(variables)} {len(initial)}\n' + ''.join(
        ' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    lrat = ''.join(f'{ids[i]} ' + (' '.join(map(str, remap(steps[i][0]))) + ' ' if steps[i][0] else '') +
                   '0 ' + ' '.join(str(ids[j]) for j in steps[i][1]) + ' 0\n' for i in derived)
    rules = []
    for i in initial:
        rule = dict(formula.rules[i - 1])
        rule['original_id'] = i
        rule['full_literals'] = [literal if isinstance(literal, bool) else
                                 variable_ids[abs(literal)] * (1 if literal > 0 else -1)
                                 for literal in rule['full_literals']]
        rules.append(rule)
    return dict(atoms=[formula.atoms[i - 1] for i in variables], clauses=clauses, rules=rules,
                cnf=cnf, lrat=lrat, derived_clauses=len(derived), original_clause_ids=initial,
                original_hints=original_hints,
                retained_hints=sum(len(steps[i][1]) for i in derived))


def solve(cells: list[SatCell], quota: tuple[int, ...], solver: Path, directory: Path, *,
          seconds: int = 2, lower_only: bool = False, counter: str = 'sequential',
          orbits: list[dict] | None = None, required_edges: int | None = None) -> dict:
    if seconds <= 0:
        raise ValueError('the solver budget must be positive')
    directory.mkdir(parents=True, exist_ok=True)
    formula = encode(cells, quota, lower_only=lower_only, counter=counter, orbits=orbits,
                     required_edges=required_edges)
    cnf, lrat = directory / 'input.cnf', directory / 'proof.lrat'
    cnf.write_text(formula.dimacs())
    start = time.perf_counter()
    proc = subprocess.run([str(solver), '-q', '--lrat', '--no-binary', '-t', str(seconds),
                           str(cnf), str(lrat)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, timeout=seconds + 5)
    result = dict(status={10: 'sat', 20: 'unsat', 0: 'budget'}.get(proc.returncode, 'error'),
                  solver_exit=proc.returncode, solver_seconds=time.perf_counter() - start,
                  original_variables=len(formula.atoms), original_clauses=len(formula.clauses),
                  lower_only=lower_only, counter=counter, quota=list(quota), cells=[asdict(cell) for cell in cells])
    if orbits is not None:
        result['orbits'] = orbits
    if formula.groupings:
        result['groupings'] = formula.groupings
    if required_edges is not None:
        result['required_edges'] = required_edges
    if proc.returncode == 20:
        result['core'] = trim(formula, lrat.read_text())
    elif proc.returncode not in (0, 10):
        result['solver_output'] = proc.stdout
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--row', type=int, choices=sorted(QUOTAS), required=True)
    p.add_argument('--complement', type=int, required=True)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--seconds', type=int, default=2)
    p.add_argument('--lower-only', action='store_true')
    p.add_argument('--counter', choices=['sequential', 'totalizer', 'grouped'], default='sequential')
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--record', help='fully qualified original RawData; preserve its order and block its terminal orbits')
    p.add_argument('--edge-cover', action='store_true', help='also require every original graph edge to occur')
    p.add_argument('--project', type=Path, default=PROJECT)
    args = p.parse_args()
    pool = universe(args.project, six=args.row == 32)
    cells = candidates(pool, args.complement, QUOTAS[args.row])
    orbits = None
    required_edges = None
    if args.edge_cover and not args.record:
        p.error('--edge-cover requires an original --record')
    if args.record:
        from read_graph_records import Records, entries, fields, leaf_orbits, natural
        raw = Records(args.project).get(args.record)
        n = natural(raw['cellPred']) + 1
        embedding = entries(fields(raw['embedding']), n)
        if sorted(embedding) != [cell.index for cell in cells]:
            raise ValueError('the original candidate universe differs from the graph candidates')
        cells = [pool[i] for i in embedding]
        if entries(fields(raw['cells']), n) != [cell.cell_code for cell in cells]:
            raise ValueError('the original cell encoding differs from the shared universe')
        if tuple(entries(fields(raw['quota']), len(QUOTAS[args.row]))) != QUOTAS[args.row]:
            raise ValueError('the original quotas differ from the specified row')
        orbits = leaf_orbits(raw, [cell.kind for cell in cells], QUOTAS[args.row])
        if args.edge_cover:
            required_edges = natural(raw['requiredEdges'])
    result = solve(cells, QUOTAS[args.row], args.solver, args.output.with_suffix(''),
                   seconds=args.seconds, lower_only=args.lower_only, counter=args.counter, orbits=orbits,
                   required_edges=required_edges)
    result.update(row=args.row, complement=args.complement)
    if args.record:
        result['record'] = args.record
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('cells', 'core', 'orbits')}, indent=2))
    if orbits is not None:
        print(json.dumps(dict(terminal_orbits=len(orbits))))
    if result['status'] == 'unsat':
        print(json.dumps(dict(core_variables=len(result['core']['atoms']),
                              core_initial_clauses=len(result['core']['clauses']),
                              core_derived_clauses=result['core']['derived_clauses'])))


if __name__ == '__main__':
    main()
