#!/usr/bin/env python3
"""Read the closed scalar data of selected existing graph certificates.

This is an untrusted producer helper. It accepts only the generated RawData
record syntax and the closed numeral grammar; it never evaluates source code.
Every emitted orbit witness is checked again by Lean's ordinary kernel.
"""
from __future__ import annotations

from collections import deque
from functools import lru_cache
import json
from pathlib import Path

from fold_packed_numerals import parse_closed_nat
from share_graph_geometry import parse_records, schema_fields


def natural(text: str) -> int:
    value, end, _ = parse_closed_nat(text, 0)
    if text[end:].strip():
        raise ValueError('trailing input in a packed natural')
    return value


def fields(text: str) -> tuple[int, int]:
    if not text.startswith('⟨') or not text.endswith('⟩'):
        raise ValueError('expected a literal Fields pair')
    width, comma, code = text[1:-1].partition(',')
    if not comma:
        raise ValueError('missing Fields separator')
    return natural(width.strip()), natural(code.strip())


def entries(field: tuple[int, int], count: int) -> list[int]:
    width, code = field
    if width < 0 or count < 0:
        raise ValueError('negative packed dimension')
    mask = (1 << width) - 1
    return [(code >> (width * i)) & mask for i in range(count)]


def finite_list(code: int, width: int, count: int) -> list[int]:
    if count <= 0:
        raise ValueError('the original RawData universe is nonempty')
    return [x % count for x in entries((width, code >> 16), code & 65535)]


class Records:
    def __init__(self, project: Path):
        self.project = project
        index = json.loads((project / 'verification/source_index.json').read_text())
        self.paths = {entry['module']: project / entry['path'] for entry in index['entries']}
        self.schema = set(schema_fields(project))

    @lru_cache(maxsize=4)
    def file(self, module: str):
        path = self.paths[module]
        return {record.qualified: record for record in parse_records(path, path.read_text())}

    @lru_cache(maxsize=24)
    def get(self, qualified: str) -> dict[str, str]:
        namespace, _, name = qualified.rpartition('.')
        module = namespace.rsplit('.', 1)[-1] + 'Data'
        record = self.file(module)[qualified]
        if record.base:
            base = record.base if '.' in record.base else namespace + '.' + record.base
            if base == qualified:
                raise ValueError('self-referencing graph record')
            result = {**self.get(base), **record.fields}
        else:
            result = record.fields
        if set(result) != self.schema:
            raise ValueError(f'incomplete RawData: {qualified}')
        return result


def leaf_orbits(data: dict[str, str], kinds: list[int], quota: tuple[int, ...],
                *, limit: int = 100000) -> list[dict]:
    """Return terminal orbits with a word carrying each entry to its leaf.

    Inverse maps find candidates only. A direct forward calculation verifies
    every discovered word before output; the emitted Lean `sameCheck` does the
    same calculation independently. Terminal counts must match the exact
    quotas, so a blocking clause may mention only its selected facets.
    """
    n = natural(data['cellPred']) + 1
    g = natural(data['framePred']) + 1
    l = natural(data['leafPred']) + 1
    width = natural(data['cellWidth'])
    if len(kinds) != n or limit <= 0:
        raise ValueError('invalid orbit dimensions')
    forward_rows = entries((width, natural(data['cellMaps'])), n * g)
    inverse_rows = entries((width, natural(data['inverseCellMaps'])), n * g)
    forward = [[x % n for x in forward_rows[i*n:(i+1)*n]] for i in range(g)]
    inverse = [[x % n for x in inverse_rows[i*n:(i+1)*n]] for i in range(g)]
    for f, inv in zip(forward, inverse):
        if sorted(f) != list(range(n)) or any(f[inv[c]] != c for c in range(n)):
            raise ValueError('recorded maps are not inverse permutations')
    leaves = [finite_list(code, width, n) for code in entries(fields(data['leaves']), l)]
    result: list[dict] = []
    seen: set[tuple[int, ...]] = set()
    queue = deque()
    for j, leaf in enumerate(leaves):
        if len(leaf) != len(set(leaf)):
            raise ValueError('a recorded terminal has duplicate facets')
        if tuple(sum(kinds[c] == key for c in leaf) for key in range(len(quota))) != quota:
            continue
        vertices = tuple(sorted(leaf))
        if vertices not in seen:
            seen.add(vertices)
            queue.append((vertices, j, []))
    while queue:
        vertices, j, word = queue.popleft()
        actual = list(vertices)
        for f in word:
            actual = [forward[f][c] for c in actual]
        if sorted(actual) != sorted(leaves[j]):
            raise ValueError('incorrect orbit word')
        result.append(dict(vertices=list(vertices), original_leaf=j, word=word))
        for f, inv in enumerate(inverse):
            renamed = tuple(sorted(inv[c] for c in vertices))
            if renamed not in seen:
                if len(seen) >= limit:
                    raise ValueError('terminal orbit budget exceeded')
                seen.add(renamed)
                queue.append((renamed, j, [f] + word))
    return result
