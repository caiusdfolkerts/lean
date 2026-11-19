#!/usr/bin/env python3
"""Install selected structural proofs and retire the corresponding growth checks.

The selector is an optimization policy, never evidence for a theorem. Each
installed source contains a complete kernel-checkable replacement. Original
metadata, frame, terminal, parameter and candidate-coverage proofs are reused.
No principal theorem statement, verification gate or axiom policy is changed.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

from emit_graph_clique_certificate import emit_case as emit_clique
from generate_facet_sat_certificates import PROJECT
from read_graph_records import Records
from share_graph_geometry import parse_records


DECL = re.compile(r'^theorem (record\d+_\w+)\b.*?(?=^theorem |^#print |^end |\Z)', re.M | re.S)

RETIRED_NODE_FIELDS = dict(nodePred='0', frameWidth='1', leafWidth='1', nodeWidth='1',
                          nodeCodes='⟨1, 0⟩', selectedMasks='⟨1, 0⟩', baseMasks='⟨1, 0⟩',
                          bounds='⟨1, 0⟩', missingSupport='0', root='0', rootFrame='0')


def retire_node_payload(path: Path, source: str, selected: set[str],
                        clear_incompatibility: set[str] | None = None) -> str:
    """Drop only fields read by the retired growth replay, preserving geometry.

    DirectCore quantifies over every complete boundary, so it has no growth
    root or intermediate-node premises. The replacement still uses the exact
    original cells, incidence matrices, embedding, quotas, maps and leaves.
    """
    replacements = []
    for record in parse_records(path, source):
        if record.name not in selected:
            continue
        if record.base:
            raise ValueError('retiring an updated RawData record requires explicit expansion')
        if not set(RETIRED_NODE_FIELDS) <= set(record.fields):
            raise ValueError('missing original growth fields')
        fields = {**record.fields, **RETIRED_NODE_FIELDS}
        if record.name in (clear_incompatibility or set()):
            fields.update(badLists='⟨0, 0⟩', badMasks='⟨0, 0⟩')
        replacement = f'def {record.name} : RawData := {{\n' + ''.join(
            f'  {name} := {value}\n' for name, value in fields.items()) + '}'
        replacements.append((record.start, record.end, replacement))
    if len(replacements) != len(selected):
        raise ValueError('not every selected RawData record was found')
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return source


def shared_local_owners(records: Records) -> set[str]:
    """Conservatively preserve any cache whose metadata is reused elsewhere."""
    pattern = re.compile(r'(Papers\.RationalityTen\.CompactReplay\.GraphInputs\w+\.record\d+)'
                         r'_(?:local_\w+|matrix_checked|validity)\b')
    result = set()
    for module, path in records.paths.items():
        if module.startswith('GraphInputs') and module.endswith('Metadata'):
            result.update(pattern.findall(path.read_text()))
    return result


def refresh_local_checks(source: str, selected: set[str]) -> str:
    """Recheck cleared caches directly, without a stale cross-record alias."""
    replacements = []
    for match in DECL.finditer(source):
        name = match.group(1)
        if name.split('_', 1)[0] not in selected or '_local_' not in name:
            continue
        declaration = match.group(0)
        signature, separator, _ = declaration.partition(':=')
        interval = re.search(r'Interval \(localCheck record\d+\) (\d+) (\d+)\s*$', signature)
        if not separator or not interval:
            raise ValueError('unexpected local cache proof shape: ' + name)
        lo, hi = map(int, interval.groups())
        if hi < lo:
            raise ValueError('reversed local cache interval')
        replacement = signature + ':=\n' + f'  interval_of_check _ {lo} {hi-lo} (by decide +kernel)\n\n'
        replacements.append((match.start(), match.end(), replacement))
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return source


def remove_checked_records(source: str, selected: set[str]) -> str:
    """Remove the old executable replay, including its otherwise unused proofs."""
    spans = [(match.start(), match.end()) for match in DECL.finditer(source)
             if match.group(1).split('_', 1)[0] in selected]
    for start, end in reversed(spans):
        source = source[:start] + source[end:]
    source = re.sub(r'^#print axioms (record\d+)_\w+\s*\n',
                    lambda m: '' if m.group(1) in selected else m.group(0), source, flags=re.M)
    if any(re.search(r'\b' + re.escape(name) + r'_\w+\b', source) for name in selected):
        raise ValueError('a retained checked declaration references a retired record')
    return source


def replace_case(source: str, local: str, namespace: str, row: int) -> str:
    core = re.compile(r'^theorem ' + re.escape(local) + r'_core\b.*?(?=^theorem |^#print |^end |\Z)', re.M | re.S)
    source, count = core.subn('', source)
    if count > 1:
        raise ValueError(f'expected at most one old core for {local}')
    result = re.compile(r'(^theorem ' + re.escape(local) + r'_result\b.*?)(?=^theorem |^#print |^end |\Z)', re.M | re.S)
    match = result.search(source)
    if match is None:
        raise ValueError(f'missing case result for {local}')
    body = match.group(0)
    old_constructor, new_constructor = ('of_six', 'of_direct_six') if row == 32 else ('of_small', 'of_direct_small')
    if count == 0:
        if namespace + '.direct_core' in body and re.search(r'\b' + new_constructor + r'\b', body):
            return source
        raise ValueError(f'neither an old core nor this installed replacement was found for {local}')
    body, constructors = re.subn(r'\b' + old_constructor + r'\b', new_constructor, body)
    body, cores = re.subn(r'\b' + re.escape(local) + r'_core\b', namespace + '.direct_core', body)
    if constructors != 1 or cores != 1:
        raise ValueError(f'unexpected old result shape for {local}')
    return source[:match.start()] + body + source[match.end():]


def merge_sources(sources: list[str]) -> str:
    imports = set()
    bodies = []
    for source in sources:
        header, marker, body = source.partition('@[expose] public section')
        if not marker:
            raise ValueError('generated source has no public section')
        for line in header.splitlines():
            if line.startswith('public import ') or line.startswith('public meta import '):
                imports.add(line)
            elif line.strip() and line not in ('module', 'prelude'):
                raise ValueError('unexpected generated source header')
        bodies.append(marker + body)
    return 'module\nprelude\n' + '\n'.join(sorted(imports)) + '\n\n' + '\n'.join(bodies)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('manifest', type=Path)
    p.add_argument('--project', type=Path, default=PROJECT)
    p.add_argument('--write', action='store_true', help='install the selected proofs; otherwise report the exact plan')
    p.add_argument('--include-sat', action='store_true')
    p.add_argument('--sat-max-hints-per-node', type=float, default=20)
    p.add_argument('--sat-max-initial-per-node', type=float, default=2)
    p.add_argument('--max-cases', type=int, default=0, help='zero selects every eligible manifest entry')
    p.add_argument('--maximum-module-bytes', type=int, default=750000)
    p.add_argument('--report', type=Path, required=True)
    args = p.parse_args()
    manifest = json.loads(args.manifest.read_text())
    records = Records(args.project)
    protected_caches = shared_local_owners(records)
    chosen = []
    for row in manifest:
        if row['method'] == 'clique' or (
                args.include_sat and row['method'] == 'unsat' and
                row['hints'] <= args.sat_max_hints_per_node * row['old_nodes'] and
                row['initial'] <= args.sat_max_initial_per_node * row['old_nodes']):
            chosen.append(row)
    if args.max_cases:
        chosen = chosen[:args.max_cases]
    groups = defaultdict(list)
    for entry in chosen:
        part = entry['record'].split('.')[-2]
        groups[part].append(entry)
    changes: dict[Path, str] = {}
    installed = []
    for part, group in sorted(groups.items()):
        data_path = records.paths[part + 'Data']
        cases_path = records.paths[part + 'Cases']
        checked_path = records.paths[part + 'Checked']
        metadata_path = records.paths[part + 'Metadata']
        cases_source = cases_path.read_text()
        cases_source = re.sub(r'^public import ' + re.escape(part) + r'Structural\d+\n',
                              '', cases_source, flags=re.M)
        new_modules = []
        bodies = []
        body_size = 0
        chunk = 0
        def flush():
            nonlocal bodies, body_size, chunk
            if not bodies:
                return
            module = part + f'Structural{chunk:03d}'
            filename = data_path.name.replace('_data.lean', f'_structural{chunk:03d}.lean')
            path = args.project / 'source/finite/graph_structural' / filename
            changes[path] = merge_sources(bodies)
            new_modules.append(module)
            bodies, body_size = [], 0
            chunk += 1
        for entry in group:
            certificate_path = args.manifest.parent / entry['file']
            encoded = certificate_path.read_bytes()
            if hashlib.sha256(encoded).hexdigest() != entry['sha256']:
                raise ValueError('certificate differs from the selected manifest')
            case = json.loads(encoded)
            if case['record'] != entry['record']:
                raise ValueError('certificate names a different original record')
            local = entry['record'].split('.')[-1]
            namespace = 'Papers.RationalityTen.StructuralGraphCases.' + part + '.' + local
            if entry['method'] == 'clique':
                source = emit_clique(case, records.get(entry['record']), namespace, full_core=True)
            else:
                from emit_facet_sat_semantics import emit_case
                source = emit_case(case, namespace, full_result=True, raw_record=True, direct_expr=True)
            if bodies and body_size + len(source.encode()) > args.maximum_module_bytes:
                flush()
            bodies.append(source)
            body_size += len(source.encode())
            cases_source = replace_case(cases_source, local, namespace, entry['row'])
            installed.append({**entry, 'namespace': namespace,
                              'incompatibility_cache_retired': entry['record'] not in protected_caches})
        flush()
        import_lines = ''.join('public import ' + module + '\n' for module in new_modules)
        imports = list(re.finditer(r'^public import \S+\n', cases_source, re.M))
        if not imports:
            raise ValueError('case module lacks imports')
        point = imports[-1].end()
        cases_source = cases_source[:point] + import_lines + cases_source[point:]
        changes[cases_path] = cases_source
        selected = {entry['record'].split('.')[-1] for entry in group}
        clear_cache = {entry['record'].split('.')[-1] for entry in group
                       if entry['record'] not in protected_caches}
        changes[checked_path] = remove_checked_records(checked_path.read_text(), selected)
        changes[data_path] = retire_node_payload(data_path, data_path.read_text(), selected, clear_cache)
        if clear_cache:
            changes[metadata_path] = refresh_local_checks(metadata_path.read_text(), clear_cache)
    report = dict(cases=installed, old_nodes_replaced=sum(row['old_nodes'] for row in installed),
                  files=[dict(path=str(path.relative_to(args.project)),
                              source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                              bytes=len(source.encode())) for path, source in sorted(changes.items())])
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    if args.write:
        for path, source in changes.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
    print(json.dumps(dict(cases=len(installed), old_nodes_replaced=report['old_nodes_replaced'],
                         files=len(changes), written=args.write)))


if __name__ == '__main__':
    main()
