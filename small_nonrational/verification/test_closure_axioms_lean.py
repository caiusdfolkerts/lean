#!/usr/bin/env python3
"""Bounded regression for per-occurrence imported axiom auditing.

Only tiny fixtures are compiled. A repeated theorem's type may agree while
one proof uses a forbidden axiom. Its own module's serialized axiom metadata
must still be checked after Lean merges the theorem names on import.
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    executable = shutil.which(args.lean)
    if executable is None:
        parser.error('Lean was not found')
    lean = Path(executable).resolve()
    if subprocess.check_output([lean, '--githash'], text=True).strip() != verify.LEAN_COMMIT:
        raise RuntimeError('Use the exact pinned Lean compiler')
    prefix = Path(subprocess.check_output([lean, '--print-prefix'], text=True).strip())
    flags = ['-t1', '-j1', '-M2048', '-DElab.async=false', '-Ddebug.skipKernelTC=false']
    report = {'lean_commit': verify.LEAN_COMMIT, 'checks': []}
    with tempfile.TemporaryDirectory(prefix='lean-own-axioms-') as temporary:
        root = Path(temporary)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(root), str(prefix / 'lib/lean')]))
        for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_PLUGIN_PATH'):
            env.pop(key, None)
        fixtures = {
            'ForeignAxiom': 'public section\naxiom fixtureForbidden : True\n',
            'GoodA': 'public section\ntheorem fixtureRepeated : True := True.intro\n',
            'GoodB': 'public import ForeignAxiom\npublic section\n'
                     'theorem fixtureRepeated : True := True.intro\n',
            'DirtyB': 'public import ForeignAxiom\npublic section\n'
                      'theorem fixtureRepeated : True := fixtureForbidden\n',
            'PrivateBad': 'public import ForeignAxiom\n'
                          'private theorem fixtureHidden : True := fixtureForbidden\n',
        }
        for name, body in fixtures.items():
            source = root / f'{name}.lean'
            source.write_text('module\n' + body)
            result = subprocess.run([str(lean), *flags, '-R', str(root), '-o',
                                     str(root / f'{name}.olean'), str(source)], env=env,
                                    capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)

        cases = [(['GoodA', 'GoodB'], True), (['GoodA', 'DirtyB'], False),
                 (['DirtyB', 'GoodA'], False), (['DirtyB'], False), (['PrivateBad'], False)]
        for index, (modules, expected) in enumerate(cases):
            captured = io.StringIO()
            with contextlib.redirect_stderr(captured):
                result = verify.closure_axiom_batch(modules, modules, lean, flags, env,
                    root / 'audits' / str(index), 60)
            if result['passed'] != expected:
                raise RuntimeError(f'Incorrect audit result for {modules}: {result}\n{captured.getvalue()}')
            if not expected and 'Unapproved axiom fixtureForbidden' not in captured.getvalue():
                raise RuntimeError(f'Fixture failed for the wrong reason: {captured.getvalue()}')
            if expected and result['declarations'] != 2:
                raise RuntimeError('Repeated clean theorem occurrences were omitted')
            report['checks'].append({'modules': modules, 'expected_accept': expected, 'passed': True})
    report['passed'] = True
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
