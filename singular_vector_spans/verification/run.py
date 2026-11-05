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
    packages=workspace/'.lake/packages';packages.parent.mkdir(exist_ok=True)
    if not packages.exists():packages.symlink_to(root/'.lake/packages',target_is_directory=True)
    return workspace,config

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--prepare-only',action='store_true');args=parser.parse_args()
    root=Path(__file__).resolve().parents[1];workspace,config=prepare(root)
    if args.prepare_only:print(f"Prepared {len(config['entries'])} unchanged source modules.");return
    subprocess.run(['lake','build','SegreVerified'],cwd=workspace,check=True)
    audit=workspace/'SegreVerified.audit.jsonl'
    if not audit.exists():raise RuntimeError('Missing final theorem audit')
    records=audit.read_text()
    if 'SEGRE_FULL_KERNEL_AUDIT_PASS ' not in records or 'SEGRE_DEPENDENCY_GRAPH_PASS ' not in records:raise RuntimeError('The final verification did not complete')
    print('Proof verification passed.',flush=True)
if __name__=='__main__':
    try:main()
    except (OSError,RuntimeError,ValueError,KeyError,subprocess.CalledProcessError) as e:print(f'Verification stopped: {e}',file=sys.stderr);sys.exit(1)
