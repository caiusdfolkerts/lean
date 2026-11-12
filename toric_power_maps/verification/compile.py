#!/usr/bin/env python3
"""Compile the exact principal dependency closure with the stock Lean kernel.

Previously checked results may be reused with --retry when their source,
output, and dependency digests match. A module is rebuilt only after its
custom imports succeed, and every fresh result records source and output digests.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import shutil
import sys
import time

ap = argparse.ArgumentParser()
ap.add_argument('project', type=Path, nargs='?', default=Path(__file__).parent)
ap.add_argument('--workers', type=int, default=1)
ap.add_argument('--roots', nargs='*')
ap.add_argument('--retry', action='store_true')
ap.add_argument('--run-id',default='kernel')
args = ap.parse_args()
p = args.project.resolve()
out = p / '.lake/verified/lib/lean'
logs = p / 'verification' / args.run_id
out.mkdir(parents=True, exist_ok=True)
logs.mkdir(parents=True, exist_ok=True)

def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and s[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if s[i] == '\n': out.append('\n')
            i += 1
        elif s[i:i+2] == '--':
            j = s.find('\n',i)
            i = len(s) if j == -1 else j
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)

def imports(f):
    s = strip_comments(f.read_text())
    return re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?([\w.]+)', s, re.M)

roots = args.roots or ['Audit']
deps, sources, standard = {}, {}, set()
def visit(m):
    if m in deps: return
    f = p / (m.replace('.', '/') + '.lean')
    if m.startswith(('Mathlib', 'Lean', 'Std', 'Batteries', 'Qq', 'Aesop', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient')) or not f.is_file():
        standard.add(m)
        return
    sources[m] = f
    deps[m] = []
    for n in imports(f):
        visit(n)
        if n in deps: deps[m].append(n)
for m in roots: visit(m)
(logs / 'dependency-graph.json').write_text(json.dumps({'roots':roots,'dependencies':deps,'external_imports':sorted(standard)},indent=2))

env = os.environ.copy()
packages = p / '.lake/packages'
libdirs = [str(out)] + [str(d / '.lake/build/lib/lean') for d in packages.iterdir() if d.is_dir()]
env['LEAN_PATH'] = ':'.join(libdirs)
lean = shutil.which('lean')
if not lean:
    raise SystemExit('The pinned Lean compiler is not on PATH; run this verification through lake build.')
version = subprocess.check_output([lean, '--version'], cwd=p, text=True).strip()
if not re.search(r'\bversion 4\.35\.0\b', version):
    raise SystemExit(f'Expected Lean 4.35.0; found {version}')
records = {}
record_path = logs / 'results.json'
seed_path = record_path
if args.retry and seed_path.exists():
    old = json.loads(seed_path.read_text())
    for m,r in old.items():
        f = out / (m.replace('.', '/') + '.olean')
        if m in sources and r.get('status') == 'passed' and r.get('source_sha256') == sha(sources[m]) and f.exists() and r.get('olean_sha256') == sha(f):
            records[m] = r
    # Invalidate every dependent of a changed or unaccepted source.
    changed = True
    while changed:
        changed = False
        for m in list(records):
            if any(d not in records or records[d].get('olean_sha256') != records[m].get('dependencies_sha256', {}).get(d) for d in deps[m]):
                del records[m]
                changed = True

def save():
    t = record_path.with_suffix('.tmp')
    t.write_text(json.dumps(records,indent=2))
    t.replace(record_path)

def run(m):
    f = sources[m]
    o = out / (m.replace('.', '/') + '.olean')
    o.parent.mkdir(parents=True,exist_ok=True)
    log = logs / (m + '.jsonl')
    cmd = [lean,'-R',str(p),'-j1','-M5000',str(f),'-o',str(o),'--json']
    start = time.time()
    r = {'source_sha256':sha(f),'command':cmd,'started':start,
         'dependencies_sha256': {d: records[d]['olean_sha256'] for d in deps[m]}}
    try:
        with log.open('w') as w:
            result = subprocess.run(cmd,cwd=p,env=env,stdout=w,stderr=subprocess.STDOUT,timeout=1800)
        text = log.read_text()
        bad = re.search(r"hasSorry|declaration uses [`']sorry|sorryAx",text)
        r.update(exit_code=result.returncode,status='passed' if result.returncode==0 and not bad and o.exists() else 'failed')
    except subprocess.TimeoutExpired:
        r.update(status='failed',exit_code='timeout')
    r['seconds'] = round(time.time()-start,2)
    if r['source_sha256'] != sha(f) or any(
        records.get(d, {}).get('status') != 'passed' or
        records[d].get('olean_sha256') != h
        for d,h in r['dependencies_sha256'].items()):
        r['status'] = 'source_changed'
    if r['status']=='passed': r['olean_sha256'] = sha(o)
    return r

pending = set(deps)-set(records)
active = {}
print(json.dumps({'modules':len(deps),'roots':len(roots),'reused_fresh':len(records),'workers':args.workers}),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
    while pending or active:
        # Reject changed source and all of its transitive dependants.
        dirty = {m for m,r in records.items() if m in sources and r.get('source_sha256') and r['source_sha256'] != sha(sources[m])}
        grew = True
        while grew:
            added = {m for m in records if any(d in dirty for d in deps[m])} - dirty
            grew = bool(added)
            dirty |= added
        for m in dirty:
            records.pop(m,None)
            if m not in active.values(): pending.add(m)
        # A failed source is retried after it has actually changed.
        for m, r in list(records.items()):
            if m in sources and (r.get('status') == 'source_changed' or (r.get('status') == 'failed' and r.get('source_sha256') != sha(sources[m]))):
                del records[m]
                pending.add(m)
        ready = sorted(m for m in pending if all(records.get(d,{}).get('status')=='passed' for d in deps[m]))
        for m in ready[:args.workers-len(active)]:
            pending.remove(m)
            active[pool.submit(run,m)] = m
        if not active:
            for m in pending:
                records[m] = {'status':'blocked','dependencies':[d for d in deps[m] if records.get(d,{}).get('status')!='passed']}
            break
        done,_ = concurrent.futures.wait(active,timeout=2,return_when=concurrent.futures.FIRST_COMPLETED)
        for task in done:
            m = active.pop(task)
            records[m] = task.result()
            print(json.dumps({'module':m,'status':records[m]['status'],'seconds':records[m]['seconds'],'remaining':len(pending)}),flush=True)
        save()
save()
counts = {s:sum(r.get('status')==s for r in records.values()) for s in ['passed','failed','blocked','source_changed']}
print(json.dumps({'summary':counts,'root_status':{m:records.get(m,{}).get('status') for m in roots}}),flush=True)

sys.exit(0 if all(records.get(m,{}).get('status') == 'passed' for m in roots) else 1)

