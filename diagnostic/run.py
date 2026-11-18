#!/usr/bin/env python3
"""Two ordered Wishart component checks. Diagnostic only, never full preflight."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil, sys, time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
PIN = '14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def write(p, value):
    p.write_text(json.dumps(value, indent=2) + '\n')

def inspect():
    frozen = json.loads((HERE / 'inputs.json').read_text())
    for name, expected in frozen['hashes'].items():
        p = HERE / name
        assert p.is_file() and not p.is_symlink() and sha(p) == expected, name
    assert (HERE / 'lean-toolchain').read_text().strip() == frozen['lean_toolchain']
    manifest = json.loads((HERE / 'lake-manifest.json').read_text())
    assert {p['name']: p['rev'] for p in manifest['packages']}['TauCeti'] == frozen['tauceti_pin']
    assert {p['name']: p['rev'] for p in manifest['packages']}['mathlib'] == frozen['mathlib_pin']
    if os.getenv('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
            f.write('lean_toolchain=' + frozen['lean_toolchain'] + '\n')
    return frozen

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=['inspect', 'run', 'finalize'])
    p.add_argument('--pipeline', type=Path)
    p.add_argument('--work', type=Path)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    if args.command == 'inspect':
        print(json.dumps(inspect(), indent=2))
        return 0
    assert args.output
    args.output.mkdir(parents=True, exist_ok=True)
    receipt_path = args.output / 'receipt.json'
    if args.command == 'finalize':
        r = json.loads(receipt_path.read_text()) if receipt_path.exists() else {
            'kind': __doc__, 'status': 'blocked-before-run', 'complete': False}
        r['workflow_steps'] = json.loads(os.getenv('DIAGNOSTIC_STEPS', '{}'))
        write(receipt_path, r)
        return 0
    frozen = inspect()
    assert args.pipeline and args.work
    args.pipeline = args.pipeline.resolve()
    args.work = args.work.resolve()
    args.output = args.output.resolve()
    r = {'kind': __doc__, 'status': 'running', 'complete': False,
         'source_commit': os.getenv('GITHUB_SHA'), 'workflow_run': os.getenv('GITHUB_RUN_ID'),
         'inputs_sha256': sha(HERE / 'inputs.json'), 'input_hashes': frozen['hashes'],
         'pipeline_commit': PIN, 'meaning': 'Independent canonical law elaboration followed by exact-source equality proofs. No full Wishart Challenge, Comparator, external kernel, trusted-root preflight, or intake claim.'}
    write(receipt_path, r)
    spec = importlib.util.spec_from_file_location('canonical_runner', HERE / 'canonical_runner.py')
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    stage = None
    try:
        case = {'id': 'wishart_independent_laws_first', 'module': 'LiteralWishartLaws',
                'lean_toolchain': frozen['lean_toolchain'],
                'hashes': {**frozen['hashes'], 'Challenge.lean': frozen['hashes']['LiteralWishartLaws.lean']},
                'original_challenge': 'LiteralWishartLaws.lean',
                'diagnostic_class': 'canonical-only-genuine-bridge-proof-smoke'}
        # execute() compiles the law module before building any TauCeti module:
        # its header imports Mathlib only. The exact original manifest remains fixed.
        folder = args.output / 'canonical-input'
        folder.mkdir()
        for name in ['lean-toolchain', 'lake-manifest.json']:
            shutil.copyfile(HERE / name, folder / name)
        shutil.copyfile(HERE / 'LiteralWishartLaws.lean', folder / 'Challenge.lean')
        o = SimpleNamespace(pipeline=args.pipeline, work=args.work,
                            output=args.output / 'canonical', memory_mib=8192,
                            setup_timeout=2400, compile_timeout=2400)
        manifest = json.loads((HERE / 'lake-manifest.json').read_text())
        code = runner.execute(o, case, folder, manifest)
        r['canonical_receipt_sha256'] = sha(o.output / 'receipt.json')
        r['canonical_exit_code'] = code
        if code:
            raise RuntimeError('Independent canonical module did not pass; source bridge is blocked')
        workspace = args.work / 'workspace'
        origin = workspace / 'diagnostic-output'
        libs = workspace / '.lake/build/lib/lean'
        libs.mkdir(parents=True, exist_ok=True)
        artifacts = sorted(origin.glob('LiteralWishartLaws.*'))
        assert any(x.suffix == '.olean' for x in artifacts)
        r['independent_artifacts'] = []
        for artifact in artifacts:
            target = libs / artifact.name
            shutil.copyfile(artifact, target)
            r['independent_artifacts'].append({'name': artifact.name, 'sha256': sha(target), 'bytes': target.stat().st_size})
        closure = json.loads((HERE / 'source-closure-manifest.json').read_text())
        tau = workspace / '.lake/packages/TauCeti'
        assert len(closure['files']) == 32
        checked = []
        for row in closure['files']:
            src = tau / row['path']
            assert src.is_file() and not src.is_symlink()
            data = src.read_bytes()
            assert sha(src) == row['sha256'], row['module']
            assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob_sha1'], row['module']
            checked.append({'module': row['module'], 'sha256': sha(src)})
        r['source_closure_verified_before_build'] = checked
        write(receipt_path, r)
        stage_o = SimpleNamespace(output=args.output / 'source')
        stage = runner.Diagnostic(stage_o, case)
        stage.receipt['kind'] = 'Actual source bridge diagnostic; not full preflight'
        tc = ['elan', 'run', frozen['lean_toolchain']]
        # Compile the exact two-root closure in dependency order, one compiler
        # at a time. Never invoke TauCeti's 22,249-module default target.
        pending = {row['module']: row for row in closure['files']}
        order = []
        while pending:
            ready = sorted(name for name, row in pending.items()
                           if not any(dep in pending for dep in row['imports']))
            assert ready, 'Cycle in pinned source import graph'
            for name in ready:
                row = pending.pop(name)
                assert all(not dep.startswith('TauCeti.') or dep in {x['module'] for x in closure['files']} for dep in row['imports'])
                order.append(row)
        budget_start = time.monotonic()
        r['source_topological_order'] = [row['module'] for row in order]
        write(receipt_path, r)
        for row in order:
            remaining = 2400 - (time.monotonic() - budget_start)
            if remaining <= 0:
                raise TimeoutError('Entire 32-module source-closure budget expired')
            target = tau / '.lake/build/lib/lean' / Path(row['path']).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            stage.run('source-module-' + row['module'], tc + ['lake', '--keep-toolchain', 'env', 'lean', '--trust=0', '-j1', '-M8192', '-DElab.async=false', '-Ddebug.skipKernelTC=false', '--root=' + str(tau), '-o', str(target), str(tau / row['path'])], cwd=workspace, timeout=remaining)
        bridge = workspace / 'LiteralWishartLawsSourceBridge.lean'
        shutil.copyfile(HERE / bridge.name, bridge)
        artifact = workspace / 'diagnostic-output' / 'LiteralWishartLawsSourceBridge.olean'
        code, _ = stage.run('actual-source-equality-bridge', tc + ['lake', '--keep-toolchain', 'env', 'lean', '--trust=0', '-j1', '-M8192', '-DElab.async=false', '-Ddebug.skipKernelTC=false', '--root=' + str(workspace), '-o', str(artifact), str(bridge)], cwd=workspace, timeout=2400, required=False)
        r['source_bridge_exit_code'] = code
        for row in r['independent_artifacts']:
            assert sha(libs / row['name']) == row['sha256'], 'Canonical artifact changed'
        assert sha(bridge) == frozen['hashes'][bridge.name]
        assert sha(workspace / 'lake-manifest.json') == frozen['hashes']['lake-manifest.json']
        assert sha(workspace / 'lean-toolchain') == frozen['hashes']['lean-toolchain']
        # Preserve exact upstream source bytes after the targeted build too.
        for row in closure['files']:
            assert sha(tau / row['path']) == row['sha256']
        if code == 0:
            assert artifact.is_file()
            r['source_bridge_olean_sha256'] = sha(artifact)
        stage.finish('source-bridge-elaborated' if code == 0 else 'source-bridge-elaboration-failed')
        r['source_receipt_sha256'] = sha(stage_o.output / 'receipt.json')
        r['status'] = 'both-stages-elaborated' if code == 0 else 'source-bridge-elaboration-failed'
        r['complete'] = code == 0
        write(receipt_path, r)
        return 0 if code == 0 else 1
    except Exception as error:
        if stage:
            stage.finish('source-bridge-blocked', error)
        r['status'] = 'diagnostic-blocked'
        r['error'] = str(error)[:4000]
        write(receipt_path, r)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
