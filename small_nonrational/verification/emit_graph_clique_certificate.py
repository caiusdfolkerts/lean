#!/usr/bin/env python3
"""Emit a quota-clique proof on an original graph record's local indices."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from generate_clique_certificates import pack
from generate_facet_sat_certificates import PROJECT
from read_graph_records import Records, entries, fields, natural


def literal(value: int) -> str:
    return str(value) if value < 1 << 64 else f'hexnat% "{value:x}"'


def emit_case(case: dict, raw: dict[str, str], namespace: str, *,
              full_core: bool = False, raw_import: str | None = None) -> str:
    if case.get('status') != 'excluded' or case.get('method', 'clique') != 'clique':
        raise ValueError('expected a completed quota-clique certificate')
    if not re.fullmatch(r'[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*', namespace):
        raise ValueError('invalid namespace')
    record = case['record']
    record_namespace, _, local = record.rpartition('.')
    module = record_namespace.rsplit('.', 1)[-1]
    n = natural(raw['cellPred']) + 1
    embedding = entries(fields(raw['embedding']), n)
    if len(set(embedding)) != len(embedding):
        raise ValueError('original embedding is not injective')
    raw_index = {global_index: i for i, global_index in enumerate(embedding)}
    ids = [raw_index[cell['index']] for cell in case['candidates']]
    packed_cells = entries(fields(raw['cells']), n)
    vertices = [(code >> 5) & 1023 for code in packed_cells]
    kinds = [code & 31 for code in packed_cells]
    imports = ['FacetCliqueRaw', 'GraphDirectCore', raw_import or module + 'Data']
    if full_core:
        imports.extend(module + suffix for suffix in ('Metadata', 'Frames', 'Leaves'))
    lines = ['module', 'prelude', *['public import ' + name for name in imports],
             'public meta import HexNatLiteral', 'public meta import KernelDecideContext', '',
             '@[expose] public section', 'set_option maxHeartbeats 0',
             'set_option maxRecDepth 100000', 'namespace ' + namespace,
             'open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate',
             f'abbrev raw := {record}',
             f'def vertexColumn : Fields := ⟨10, {literal(pack(vertices, 10))}⟩',
             f'def kindColumn : Fields := ⟨3, {literal(pack(kinds, 3))}⟩',
             'def data := FacetSat.RawProjection.data raw vertexColumn kindColumn',
             'theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=',
             '  by decide_kernel_context',
             'def selectedKinds : List Nat := [' + ', '.join(map(str, case['kinds'])) + ']',
             'def candidates : List (Fin raw.n) := [' + ', '.join(f'⟨{i}, by decide⟩' for i in ids) + ']',
             'def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota',
             'theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=',
             '  by decide_kernel_context',
             'def certificate : CliqueExclusion.QuotaCertificate raw.n :=']
    for index, node in enumerate(case['nodes']):
        if node[0] == 'size':
            term = f'.size {node[1]}'
        elif node[0] == 'color':
            _, key, count, width, payload = node
            masks = [sum(1 << ids[i] for i in range(len(ids))
                         if (payload >> (width * i)) & ((1 << width) - 1) == color)
                     for color in range(count)]
            term = f'.classes {key} [' + ', '.join(literal(mask) for mask in masks) + ']'
        elif node[0] == 'split':
            _, pivot, left, right = node
            if not 0 <= left < index or not 0 <= right < index:
                raise ValueError('certificate contains a forward reference')
            term = f'.split ⟨{ids[pivot]}, by decide⟩ c{left} c{right}'
        else:
            raise ValueError('unknown clique certificate node')
        lines.append(f'  let c{index} : CliqueExclusion.QuotaCertificate raw.n := {term}')
    lines.extend([f'  c{case["root"]}',
                  'theorem checked : CliqueExclusion.checkQuotas data.relation data.kind',
                  '    candidates requirements certificate = true := by decide_kernel_context',
                  'theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)',
                  '    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))',
                  '    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=',
                  '  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn',
                  '    projection_checked selectedKinds candidates candidates_complete certificate checked B H'])
    if full_core:
        lines.extend(['theorem direct_core : DirectCore raw where',
                      f'  matrix := {record}_matrix_checked',
                      f'  valid := {record}_validity',
                      f'  literal := {record}_literal',
                      '  leaf_nodup := by decide +kernel',
                      f'  frames := {record}_frames_supported {record}_cells_exact',
                      f'  leaves_checked := ⟨{record}_certificates, {record}_leaf_certificates_checked⟩',
                      f'  complete := fun B H => False.elim (local_excluded {record}_validity {record}_matrix_checked B H)'])
    lines.extend(['#print axioms local_excluded', 'end ' + namespace, ''])
    return '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    p.add_argument('--project', type=Path, default=PROJECT)
    p.add_argument('--namespace', default='Papers.RationalityTen.CliqueRawSample')
    p.add_argument('--full-core', action='store_true')
    p.add_argument('--raw-import')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    case = json.loads(args.certificate.read_text())
    source = emit_case(case, Records(args.project).get(case['record']), args.namespace,
                       full_core=args.full_core, raw_import=args.raw_import)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source)


if __name__ == '__main__':
    main()
