#!/usr/bin/env python3
"""Produce small, untrusted quota-clique certificates with explicit budgets.

The emitted Lean data are checked by ``CliqueExclusion.checkQuotas``.  This
program is not part of the trusted proof: neither finding a graph obstruction
nor emitting a certificate establishes any theorem until Lean checks it.

This command handles one selected graph, never the complete case collection.
The reusable search routine accepts any symmetric adjacency rows and kinds.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
import json
from pathlib import Path
import re
import time


PROJECT = Path(__file__).resolve().parents[1]
QUOTAS = {
    16: (0, 3, 8, 2, 0), 19: (0, 2, 7, 4, 0),
    23: (0, 4, 10, 0, 0), 24: (0, 4, 8, 2, 0),
    25: (0, 3, 9, 2, 0), 26: (0, 3, 7, 4, 0),
    27: (0, 2, 6, 6, 0), 28: (0, 5, 10, 0, 0),
    29: (0, 5, 8, 2, 0), 30: (0, 4, 7, 4, 0),
    31: (0, 6, 8, 2, 0), 32: (0, 4, 5, 4, 1),
}


@dataclass(frozen=True)
class Cell:
    index: int
    kind: int
    vertices: int
    faces: int
    missing: int


class SearchBudget(Exception):
    """The producer stopped before proving or refuting the necessary condition."""


def unpack_list(code: int) -> tuple[list[int], int]:
    count, code = code & 65535, code >> 16
    values = []
    for _ in range(count):
        values.append(code & 65535)
        code >>= 16
    return values, code


def small_universe(project: Path = PROJECT) -> list[Cell]:
    """Read the literal small-facet universe; reject unexpected source shape."""
    source = (project / "source/geometry/full_small_facet_universe.lean").read_text()
    codes = [int(s) for s in re.findall(r"\(\.leaf (\d+)\)", source)]
    if len(codes) != 6510:
        raise ValueError(f"expected 6510 small facet cells, found {len(codes)}")
    edge_masks = [(1 << a) | (1 << b) for a, b in combinations(range(10), 2)]
    edge_index = {mask: i for i, mask in enumerate(edge_masks)}
    cells = []
    for index, code in enumerate(codes):
        kind, vertices = code & 65535, (code >> 16) & 65535
        edges, tail = unpack_list(code >> 32)
        ridges, tail = unpack_list(tail)
        if tail or vertices >= 1024 or any(face >= 1024 for face in edges + ridges):
            raise ValueError(f"invalid literal cell at index {index}")
        within = sum(1 << i for i, mask in enumerate(edge_masks) if vertices & mask == mask)
        actual_edges = sum(1 << edge_index[edge] for edge in edges)
        if actual_edges & ~within:
            raise ValueError(f"edge outside cell vertices at index {index}")
        faces = 0
        for face in edges + ridges:
            faces |= 1 << face
        cells.append(Cell(index, kind, vertices, faces, within ^ actual_edges))
    return cells


def compatible(a: Cell, b: Cell) -> bool:
    common = a.vertices & b.vertices
    return common & (common - 1) == 0 or bool((a.faces >> common) & (b.faces >> common) & 1)


def candidates(cells: list[Cell], complement: int, kinds: tuple[int, ...]) -> list[Cell]:
    edge_masks = [(1 << a) | (1 << b) for a, b in combinations(range(10), 2)]
    within = {
        cell.vertices: sum(1 << i for i, edge in enumerate(edge_masks) if cell.vertices & edge == edge)
        for cell in cells
    }
    return [cell for cell in cells if cell.kind in kinds and
            within[cell.vertices] & complement == cell.missing]


def adjacency(cells: list[Cell]) -> list[int]:
    rows = [0] * len(cells)
    for i, a in enumerate(cells):
        for j, b in enumerate(cells[:i]):
            if compatible(a, b):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
    return rows


def pack(values: list[int], width: int) -> int:
    if width < 0 or any(value < 0 or value >= 1 << width for value in values):
        raise ValueError("packed value does not fit its field")
    return sum(value << (width * i) for i, value in enumerate(values))


def search(rows: list[int], kinds: list[int], quotas: tuple[int, ...], *,
           limit: int = 10000, seconds: float = 1.0) -> dict:
    """Search only for a necessary clique condition, returning a certificate DAG.

    Nodes are topologically ordered tuples: ``('size', kind)``,
    ``('color', kind, count, width, payload)``, or
    ``('split', pivot, without_child, with_child)``.  DAG sharing is an output
    compression only; the transparent Lean certificate still checks every use.
    """
    size = len(rows)
    if len(kinds) != size or any(kind < 0 or kind >= len(quotas) for kind in kinds):
        raise ValueError("every vertex must have a kind covered by the quota vector")
    if limit <= 0 or seconds <= 0 or any(quota < 0 for quota in quotas):
        raise ValueError("positive search budgets and nonnegative quotas are required")
    mask = (1 << size) - 1
    if any(row < 0 or row & ~mask or row & (1 << i) for i, row in enumerate(rows)):
        raise ValueError("adjacency rows must be bounded and have zero diagonal")
    if any(bool(rows[i] & (1 << j)) != bool(rows[j] & (1 << i))
           for i in range(size) for j in range(i)):
        raise ValueError("the producer requires symmetric adjacency rows")

    start = time.monotonic()
    visits = 0
    maxdepth = 0
    kind_masks = [sum(1 << i for i, kind in enumerate(kinds) if kind == key)
                  for key in range(len(quotas))]
    nodes: list[tuple] = []
    interned: dict[tuple, int] = {}
    cache: dict[tuple[int, tuple[int, ...]], int] = {}

    def intern(node: tuple) -> int:
        existing = interned.get(node)
        if existing is not None:
            return existing
        result = len(nodes)
        interned[node] = result
        nodes.append(node)
        return result

    def coloring(available: int) -> tuple[int, list[int], list[int]]:
        count = 0
        order = []
        colors = [0] * size
        priority = sorted((vertex for vertex in range(size) if available & (1 << vertex)),
                          key=lambda vertex: (-(rows[vertex] & available).bit_count(), vertex))
        while available:
            free = available
            while free:
                vertex = next(vertex for vertex in priority if free & (1 << vertex))
                bit = 1 << vertex
                colors[vertex] = count
                order.append(vertex)
                available ^= bit
                free ^= bit
                free &= ~rows[vertex]
            count += 1
        return count, order, colors

    def visit(available: int, need: tuple[int, ...], chosen: tuple[int, ...]) -> tuple[str, object]:
        nonlocal visits, maxdepth
        visits += 1
        maxdepth = max(maxdepth, len(chosen))
        if visits > limit or time.monotonic() - start > seconds:
            raise SearchBudget
        if not any(need):
            return "witness", chosen
        state = available, need
        if state in cache:
            return "excluded", cache[state]
        for key, required in enumerate(need):
            if required and (available & kind_masks[key]).bit_count() < required:
                node = intern(("size", key))
                cache[state] = node
                return "excluded", node
        options = []
        for key, required in enumerate(need):
            if not required:
                continue
            part = available & kind_masks[key]
            count, order, colors = coloring(part)
            if count < required:
                width = max(1, (count - 1).bit_length())
                node = intern(("color", key, count, width, pack(colors, width)))
                cache[state] = node
                return "excluded", node
            options.append((count - required, part.bit_count() / required, key, order))
        _, _, key, order = min(options)
        pivot = order[-1]
        remaining = list(need)
        remaining[key] -= 1
        with_status, with_child = visit(available & rows[pivot], tuple(remaining), chosen + (pivot,))
        if with_status == "witness":
            return with_status, with_child
        without_status, without_child = visit(available & ~(1 << pivot), need, chosen)
        if without_status == "witness":
            return without_status, without_child
        node = intern(("split", pivot, without_child, with_child))
        cache[state] = node
        return "excluded", node

    try:
        status, result = visit(mask, tuple(quotas), ())
    except SearchBudget:
        status, result = "budget", None
    return dict(status=status, root=result if status == "excluded" else None,
                witness=list(result) if status == "witness" else None,
                nodes=nodes if status == "excluded" else [], visits=visits,
                depth=maxdepth, states=len(cache), seconds=time.monotonic() - start)


def emit_certificate(nodes: list[tuple], root: int, type_name: str = "data.count", *,
                     vertex_count: int | None = None, class_masks: bool = False) -> str:
    """Emit shared transparent lets; certificate references must point backwards."""
    if not 0 <= root < len(nodes):
        raise ValueError("invalid certificate root")
    lines = [f"def certificate : CliqueExclusion.QuotaCertificate {type_name} :="]
    for index, node in enumerate(nodes):
        if node[0] == "size":
            term = f".size {node[1]}"
        elif node[0] == "color":
            _, kind, count, width, payload = node
            if class_masks:
                if vertex_count is None:
                    raise ValueError("explicit color classes require the vertex count")
                masks = [sum(1 << vertex for vertex in range(vertex_count)
                             if (payload >> (width * vertex)) & ((1 << width) - 1) == color)
                         for color in range(count)]
                term = f".classes {kind} [" + ", ".join(map(str, masks)) + "]"
            else:
                term = f'.color {kind} {count} {width} (hexnat% "{payload:x}")'
        elif node[0] == "split":
            _, pivot, left, right = node
            if not 0 <= left < index or not 0 <= right < index:
                raise ValueError("certificate contains a forward or cyclic reference")
            term = f".split ⟨{pivot}, by decide⟩ c{left} c{right}"
        else:
            raise ValueError(f"unknown certificate node {node[0]!r}")
        lines.append(f"  let c{index} : CliqueExclusion.QuotaCertificate {type_name} := {term}")
    lines.append(f"  c{root}")
    return "\n".join(lines)


def emit_data(cells: list[Cell]) -> str:
    fields = [("embedding", 13, [cell.index for cell in cells]),
              ("vertices", 10, [cell.vertices for cell in cells]),
              ("faces", 1024, [cell.faces for cell in cells]),
              ("kinds", 3, [cell.kind for cell in cells])]
    lines = ["def data : GraphFacetClique.Data where", f"  count := {len(cells)}"]
    for name, width, values in fields:
        lines.append(f'  {name} := ⟨{width}, hexnat% "{pack(values, width):x}"⟩')
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", type=int, choices=sorted(set(QUOTAS) - {32}), required=True)
    parser.add_argument("--complement", type=int, required=True)
    parser.add_argument("--kinds", default="2,3")
    parser.add_argument("--limit", type=int, default=10000)
    parser.add_argument("--seconds", type=float, default=1.0)
    parser.add_argument("--class-masks", action="store_true",
                        help="emit explicit color-class masks instead of packed color labels")
    parser.add_argument("--output", type=Path, required=True, help="output prefix, without extension")
    parser.add_argument("--project", type=Path, default=PROJECT)
    args = parser.parse_args()
    kinds = tuple(int(kind) for kind in args.kinds.split(","))
    if len(set(kinds)) != len(kinds) or any(kind < 0 or kind >= 5 for kind in kinds):
        parser.error("kinds must be distinct integers from 0 through 4")
    if args.complement < 0 or args.complement >= 1 << 45:
        parser.error("the graph complement must fit 45 bits")
    quota = tuple(q if kind in kinds else 0 for kind, q in enumerate(QUOTAS[args.row]))
    cells = candidates(small_universe(args.project), args.complement, kinds)
    result = search(adjacency(cells), [cell.kind for cell in cells], quota,
                    limit=args.limit, seconds=args.seconds)
    result.update(row=args.row, complement=args.complement, kinds=kinds,
                  quota=quota, candidates=[cell.__dict__ for cell in cells])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    if result["status"] == "excluded":
        lean = "\n".join([
            "module", "prelude", "public import GraphFacetClique",
            "public meta import HexNatLiteral", "public meta import KernelDecideContext",
            "@[expose] public section", "set_option maxHeartbeats 0",
            "set_option maxRecDepth 100000", "namespace Papers.RationalityTen.CliqueSample",
            emit_data(cells), emit_certificate(result["nodes"], result["root"],
                                               vertex_count=len(cells), class_masks=args.class_masks),
            "def quota (key : Nat) : Nat :=",
            *[f"  if key = {key} then {q} else" for key, q in enumerate(quota) if q],
            "  0", "theorem checked : CliqueExclusion.checkQuotas data.relation data.kind",
            "    (List.finRange data.count) quota certificate = true := by decide_kernel_context",
            "#print axioms checked", "end Papers.RationalityTen.CliqueSample", "",
        ])
        args.output.with_suffix(".lean").write_text(lean)
    print(json.dumps({key: value for key, value in result.items() if key not in {"nodes", "candidates"}},
                     sort_keys=True))


if __name__ == "__main__":
    main()
