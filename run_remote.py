#!/usr/bin/env python3
"""Build a pinned fixture sample and compare both proofs on one Linux runner."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import graphlib
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
FIXTURE = ROOT / 'fixture.json'
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
LEAN_FLAGS = ['-t1', '-j1', '-s65536', '-DmaxHeartbeats=0', '-DElab.async=false',
              '-Ddebug.skipKernelTC=false']


def source_path(module):
    return Path(*module.split('.')).with_suffix('.lean')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_rss(path):
    for line in path.read_text().splitlines():
        if 'Maximum resident set size (kbytes):' in line:
            return int(line.rsplit(': ', 1)[1])
    return None


def compile_lean(lean, module, directory, search, log, compile_output=True, profile=False):
    target = source_path(module)
    log.parent.mkdir(parents=True, exist_ok=True)
    timelog = log.with_suffix('.time')
    cmd = ['/usr/bin/time', '-v', '-o', str(timelog), lean, *LEAN_FLAGS]
    if profile:
        cmd.append('-Dprofiler=true')
    if compile_output:
        cmd.extend(('-o', target.with_suffix('.olean').as_posix()))
    cmd.append(target.as_posix())
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(
        [*(str(p) for p in search), os.environ.get('LEAN_PATH', '')]).rstrip(os.pathsep))
    started = time.monotonic()
    with log.open('w') as output:
        proc = subprocess.run(cmd, cwd=directory, env=env, stdout=output, stderr=subprocess.STDOUT,
                              timeout=1800)
    elapsed = time.monotonic() - started
    if proc.returncode:
        tail = log.read_text(errors='replace').splitlines()[-12:]
        raise RuntimeError(f'{module} exited {proc.returncode} ({log}): ' + '\n'.join(tail))
    return {'seconds': round(elapsed, 4), 'peak_rss_kib': read_rss(timelog)}


def build_common(lean, common, graph, log_root):
    started = time.monotonic()
    closure = graph.keys()
    order = graphlib.TopologicalSorter({m: [d for d in deps if d in closure] for m, deps in graph.items()})
    order.prepare()
    tasks = {}
    timings = {}
    with ThreadPoolExecutor(max_workers=2) as pool:
        while order.is_active():
            for module in order.get_ready():
                log = (log_root / source_path(module)).with_suffix('.log')
                task = pool.submit(compile_lean, lean, module, common, [common], log)
                tasks[task] = module
            finished, _ = wait(tasks, return_when=FIRST_COMPLETED)
            for task in finished:
                module = tasks.pop(task)
                timings[module] = task.result()
                order.done(module)
    return {'wall_seconds': round(time.monotonic() - started, 4), 'modules': timings}


def audit(log, declarations):
    raw = log.read_text()
    no_axioms = raw.count('does not depend on any axioms')
    found = re.findall(r'depends on axioms: \[([^\]]*)\]', raw)
    if no_axioms + len(found) != declarations:
        raise ValueError(f'expected {declarations} axiom reports in {log}, saw {no_axioms + len(found)}')
    axioms = {re.sub(r'\.\{[^}]+\}$', '', ax.strip()) for group in found for ax in group.split(',')}
    if axioms - AXIOMS:
        raise ValueError(f'unexpected axioms in {log}: {sorted(axioms - AXIOMS)}')
    return raw, sorted(axioms)


def measure(sample, manifest, repeats, profile):
    if platform.system() != 'Linux' or not os.environ.get('LEAN_PATH'):
        raise SystemExit('Run on a separate Linux host under lake env.')
    source = manifest['samples'][sample]
    for filename, value in manifest['sha256'].items():
        if sha(ROOT / filename) != value:
            raise ValueError(f'fixture digest mismatch: {filename}')
    results = ROOT / 'results'
    results.mkdir(exist_ok=False)
    output = ROOT / 'build'
    common = output / 'common'
    shutil.copytree(ROOT / 'common', common)
    report = {
        'sample': sample, 'fixture_sha256': sha(FIXTURE), 'source_transforms': source['source_transforms'],
        'github_run_id': os.getenv('GITHUB_RUN_ID'), 'github_run_attempt': os.getenv('GITHUB_RUN_ATTEMPT'),
        'github_sha': os.getenv('GITHUB_SHA'), 'host': platform.platform(), 'cpu_count': os.cpu_count(),
        'flags': LEAN_FLAGS, 'runs': [],
    }

    def save():
        (results / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')

    try:
        lean = subprocess.check_output(['elan', 'which', 'lean'], text=True).strip()
        report['lean'] = subprocess.check_output([lean, '--version'], text=True).strip()
        graph = {m: manifest['common_graph'][m] for m in source['common']}
        report['common'] = build_common(lean, common, graph, results / 'common')
        save()
        observed = None
        for round_number in range(repeats):
            arms = ('before', 'after') if round_number % 2 == 0 else ('after', 'before')
            for arm in arms:
                tag = f'{round_number + 1}-{arm}'
                location = output / tag
                logs = results / tag
                shutil.copytree(ROOT / 'samples' / sample / arm, location)
                # Lean resolves a namespace root using the first matching directory.
                # Make its compiled common prerequisites visible in the arm's tree.
                for artifact in common.rglob('*.olean*'):
                    target = location / artifact.relative_to(common)
                    if artifact.is_file() and not target.exists():
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.symlink_to(artifact)
                search = [location, common]
                setup = {module: compile_lean(lean, module, location, search, logs / f'{module}.log')
                         for module in (source['after_setup'] if arm == 'after' else [])}
                timings = {module: compile_lean(lean, module, location, search, logs / f'{module}.log')
                           for module in source['modules']}
                row = {'round': round_number + 1, 'arm': arm, 'helper_setup': setup, 'modules': timings,
                       'sum_seconds': round(sum(t['seconds'] for t in timings.values()), 4)}
                report['runs'].append(row)
                save()
                audit_log = logs / 'Audit.log'
                row['audit'] = compile_lean(lean, 'Audit', location, search, audit_log, compile_output=False)
                printed, axioms = audit(audit_log, source['declarations'])
                row['print_sha256'] = sha(audit_log)
                if observed is None:
                    observed = printed
                elif observed != printed:
                    raise ValueError(f'original declarations or axiom output changed in {tag}')
                report['audit'] = {'declarations': source['declarations'], 'axioms': axioms}
                save()
        report['median_seconds'] = {
            arm: statistics.median(row['sum_seconds'] for row in report['runs'] if row['arm'] == arm)
            for arm in ('before', 'after')}
        report['comparison_equal'] = True
        if profile:
            for arm in ('before', 'after'):
                location = output / f'1-{arm}'
                for module in source['modules']:
                    compile_lean(lean, module, location, [location, common],
                                 results / 'profile' / arm / f'{module}.log',
                                 compile_output=False, profile=True)
        report['status'] = 'pass'
    except Exception as error:
        report.update(status='fail', error=str(error))
        raise
    finally:
        save()


def main():
    manifest = json.loads(FIXTURE.read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sample', choices=sorted(manifest['samples']))
    parser.add_argument('--external', action='store_true')
    parser.add_argument('--repeats', type=int, choices=(1, 2), default=2)
    parser.add_argument('--profile', action='store_true')
    args = parser.parse_args()
    if args.external:
        print(' '.join(m for m in manifest['samples'][args.sample]['external']
                       if m.split('.')[0] not in {'Init', 'Lean', 'Std'}))
        return
    measure(args.sample, manifest, args.repeats, args.profile)


if __name__ == '__main__':
    main()
