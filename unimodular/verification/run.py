#!/usr/bin/env python3
"""Reproduce the pinned kernel checks from the published mathematical source."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prepare(root):
    config=json.loads((root/'verification/source_index.json').read_text())
    workspace=root/'.lake/verification_workspace';workspace.mkdir(parents=True,exist_ok=True)
    seen=set()
    for row in config['entries']:
        name=row['module'];parts=name.split('.')
        if name in seen or any(not x or any(c in x for c in '/\\\n\0') for x in parts):raise RuntimeError('Invalid source module')
        seen.add(name);src=(root/row['path']).resolve()
        if not src.is_relative_to((root/'source').resolve()) or sha(src)!=row['source_sha256']:raise RuntimeError(f'Missing or changed source: {name}')
        dst=workspace/Path(*parts).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.is_symlink():dst.unlink()
        if dst.exists() and not os.path.samefile(dst,src):dst.unlink()
        if not dst.exists():
            try:os.link(src,dst)
            except OSError:shutil.copyfile(src,dst)
    for f in ['lean-toolchain','lake-manifest.json']:(workspace/f).write_bytes((root/f).read_bytes())
    (workspace/'lakefile.toml').write_bytes((root/'verification/project.toml').read_bytes())
    (workspace/'compile.py').write_bytes((root/'verification/compile.py').read_bytes())
    packages=workspace/'.lake/packages';packages.parent.mkdir(exist_ok=True)
    if not packages.exists():packages.symlink_to(root/'.lake/packages',target_is_directory=True)
    return workspace,config

def check_audit(log,expected):
    allowed={'propext','Classical.choice','Quot.sound'};seen={}
    for line in log.read_text().splitlines():
        try:message=json.loads(line)
        except json.JSONDecodeError:continue
        if message.get('severity')=='error':raise RuntimeError('Lean reported an audit error')
        data=message.get('data','')
        m=re.search(r"'([^']+)' depends on axioms:\s*\[([\s\S]*?)\]",data)
        if m:
            axioms={re.sub(r'\.\{[^}]*\}','',x).strip() for x in m[2].split(',') if x.strip()}
            if not axioms<=allowed:raise RuntimeError(f'Unexpected axioms in {m[1]}: {axioms-allowed}')
            seen[m[1]]=axioms
        m=re.search(r"'([^']+)' does not depend on any axioms",data)
        if m:seen[m[1]]=set()
    if set(seen)!=set(expected):raise RuntimeError('The declaration audit does not match the published interface')
    print(f'Checked all {len(seen)} advertised declarations: only the three standard logical axioms.',flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--prepare-only',action='store_true');args=parser.parse_args()
    root=Path(__file__).resolve().parents[1];workspace,config=prepare(root)
    if args.prepare_only:print(f"Prepared {len(config['entries'])} unchanged source modules.");return
    subprocess.run(['lake','env','python3','compile.py','--workers','8'],cwd=workspace,check=True)
    records=json.loads((workspace/'verification/kernel/results.json').read_text())
    if set(records)!={r['module'] for r in config['entries']} or any(r.get('status')!='passed' for r in records.values()):raise RuntimeError('Not all published modules passed')
    check_audit(workspace/'verification/kernel/Audit.jsonl',config['audited_declarations'])
    print('Proof verification passed.',flush=True)
if __name__=='__main__':
    try:main()
    except (OSError,RuntimeError,ValueError,KeyError,subprocess.CalledProcessError) as e:print(f'Verification stopped: {e}',file=sys.stderr);sys.exit(1)
