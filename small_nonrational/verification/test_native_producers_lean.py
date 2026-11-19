#!/usr/bin/env python3
"""Build three tiny source modules with fresh linked native proof producers.

This exercises the real verifier, its receipt checker/exporter, shared-library
dependency loading, and rejection of an invalid theorem. It never selects any
polytope case or imports recovered project artifacts.
"""
from pathlib import Path
import argparse
import contextlib
import json
import os
import shutil
import subprocess
import tempfile

import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--mathlib', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--workdir', type=Path, help='Keep the tiny fixture in a new directory for inspection')
    args = parser.parse_args()
    lean = args.lean.resolve()
    if verify.run(str(lean), '--githash') != verify.LEAN_COMMIT:
        raise RuntimeError('Use the exact pinned Lean compiler')
    here = Path(__file__).resolve().parent
    repository = here.parent
    report = {'passed': False, 'lean_commit': verify.LEAN_COMMIT}
    if args.workdir:
        args.workdir.mkdir(parents=True, exist_ok=False)
    workspace = (contextlib.nullcontext(str(args.workdir.resolve())) if args.workdir else
                 tempfile.TemporaryDirectory(prefix='native-producer-fixture-'))
    with workspace as temporary:
        root = Path(temporary)
        (root / 'Sources').mkdir()
        (root / 'scripts').mkdir()
        (root / 'audit').mkdir()
        for source, destination in [('verify.py', 'verify.py'), ('parse_imports.lean', 'ParseImports.lean'),
                ('export_dependencies.py', 'export_dependencies.py'),
                ('export_dependencies.lean', 'ExportDependencies.lean')]:
            shutil.copyfile(here / source, root / 'scripts' / destination)
        shutil.copyfile(repository / 'lake-manifest.json', root / 'lake-manifest.json')
        shutil.copyfile(repository / 'lean-toolchain', root / 'lean-toolchain')
        fixtures = {
            'RupProofTerm': ('module\npublic meta import Lean.Elab.Term\n'
                'public meta section\nnamespace NativeFixture\n'
                'def successor (n : Nat) : Nat := n + 1\nend NativeFixture\n', ['Lean.Elab.Term']),
            'FacetSatInitials': ('module\npublic meta import Lean.Elab.Term\n'
                'public meta import RupProofTerm\npublic meta section\n'
                'open Lean Elab Term\n'
                'syntax (name := nativeFixture) "native_fixture% " num : term\n'
                '@[term_elab nativeFixture] def elaborateNativeFixture : TermElab := fun stx _ => do\n'
                '  let some n := stx[1].isNatLit? | throwError "expected numeral"\n'
                '  return mkNatLit (NativeFixture.successor n)\n',
                ['Lean.Elab.Term', 'RupProofTerm']),
            'Probe': ('module\npublic meta import FacetSatInitials\n@[expose] public section\n'
                'def nativeValue : Nat := native_fixture% 4\n'
                'theorem nativeValue_checked : nativeValue = 5 := rfl\n'
                '#print axioms nativeValue_checked\n', ['FacetSatInitials'])}
        entries = []
        for name, (text, imports) in fixtures.items():
            source = root / 'Sources' / (name + '.lean')
            source.write_text(text)
            entries.append({'module': name, 'source_sha256': verify.hash_file(source), 'imports': imports})
        (root / 'audit/source-index.json').write_text(json.dumps({'roots': ['Probe'], 'entries': entries}))
        env = dict(os.environ)
        prefix = Path(verify.run(str(lean), '--print-prefix'))
        env['PATH'] = str(prefix / 'bin') + os.pathsep + env.get('PATH', '')
        command = ['python3', str(root / 'scripts/verify.py'), '--project', str(root),
            '--mathlib', str(args.mathlib.resolve()), '--lean', str(lean), '--jobs', '1',
            '--memory', '1024', '--memory-budget', '2048', '--audit-memory', '2048', '--timeout', '60']
        result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=240)
        if result.returncode:
            raise RuntimeError(result.stdout[-6000:] + result.stderr[-6000:])
        built = json.loads((root / '.lake/build/verification/result.json').read_text())
        if not built['passed'] or built['checked_modules'] != 3:
            raise RuntimeError('Incomplete tiny native source build')
        records = {name: json.loads((root / '.lake/build/verification/modules' / (name + '.json')).read_text())
                   for name in fixtures}
        if [p['module'] for p in records['FacetSatInitials']['native_plugins']] != ['RupProofTerm']:
            raise RuntimeError('The dependent native producer was not linked to its exact input')
        if len(records['Probe']['native_plugins']) != 2:
            raise RuntimeError('The consuming module did not record both native plugins')
        bad = root / 'Sources/Bad.lean'
        bad.write_text('module\npublic meta import FacetSatInitials\n'
                       'theorem invalidNativeClaim : (native_fixture% 4 : Nat) = 6 := rfl\n')
        library_paths, _, _, _, _ = verify.library_environment(lean, args.mathlib.resolve(), root)
        bad_env = dict(env, LEAN_PATH=os.pathsep.join([str(root / '.lake/build/lib/lean'),
                                                    *map(str, library_paths)]))
        bad_result = subprocess.run([str(lean), '-t1', '-j1', '-M1024', '-DElab.async=false',
            '-Ddebug.skipKernelTC=false', *verify.native_plugin_flags(records['Probe']['native_plugins'], root),
            str(bad)], env=bad_env, capture_output=True, text=True, timeout=60)
        if bad_result.returncode == 0 or 'error:' not in bad_result.stdout + bad_result.stderr:
            raise RuntimeError('The native producer bypassed ordinary rejection of a false theorem')
        export = root / 'export'
        exported = subprocess.run(['python3', str(root / 'scripts/export_dependencies.py'),
            '--project', str(root), '--mathlib', str(args.mathlib.resolve()), '--lean', str(lean),
            '--output', str(export), '--batch-modules', '64', '--memory', '2048',
            '--memory-budget', '2048', '--timeout', '60'],
            env=env, capture_output=True, text=True, timeout=300)
        if exported.returncode:
            raise RuntimeError(exported.stdout[-6000:] + exported.stderr[-6000:])
        manifest = json.loads((export / 'extraction-manifest.json').read_text())
        if not manifest['extraction_passed'] or manifest['project_modules'] != 3:
            raise RuntimeError('The fresh native build failed its full receipt/export gate')
        report.update(passed=True, source_modules=3, native_producers=2,
                      native_dependency_linking=True, false_theorem_rejected=True,
                      complete_receipt_export=True,
                      declarations=manifest['project_declarations'])
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
