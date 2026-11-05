#!/usr/bin/env python3
"""Build the published source with its unchanged, verified Lean module identities."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def put_link(dst,src):
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.is_symlink():
        if dst.resolve()==src.resolve():return
        dst.unlink()
    elif dst.exists():
        raise RuntimeError(f'Refusing to replace a non-generated file: {dst}')
    dst.symlink_to(os.path.relpath(src,dst.parent),target_is_directory=src.is_dir())

def put_source(dst,src):
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.is_symlink():dst.unlink()
    elif dst.exists():
        if os.path.samefile(dst,src):return
        dst.unlink()
    try:os.link(src,dst)
    except OSError:shutil.copyfile(src,dst)


def prepare(root):
    config=json.loads((root/'verification/source_index.json').read_text())
    workspace=root/'.lake/verification_workspace'
    workspace.mkdir(parents=True,exist_ok=True)
    seen=set()
    for row in config['entries']:
        name=row['module'];parts=name.split('.')
        if name in seen or any(not p or any(c in p for c in '/\\\n\r\0') for p in parts):
            raise RuntimeError('Invalid or duplicate module name')
        seen.add(name)
        src=(root/row['path']).resolve()
        if not src.is_relative_to((root/'source').resolve()) or sha(src)!=row['source_sha256']:
            raise RuntimeError(f'Missing or modified source: {name}')
        put_source(workspace/'Sources'/Path(*parts).with_suffix('.lean'),src)
    (workspace/'audit').mkdir(exist_ok=True)
    (workspace/'audit/source-index.json').write_text(json.dumps(config,separators=(',',':'))+'\n')
    (workspace/'audit/modules.txt').write_text('\n'.join(sorted(seen))+'\n')
    for filename in ['lean-toolchain','lake-manifest.json']:
        data=(root/filename).read_bytes();p=workspace/filename
        if not p.exists() or p.read_bytes()!=data:p.write_bytes(data)
    (workspace/'lakefile.lean').write_bytes((root/'verification/project.lean').read_bytes())
    names={'parse_imports.lean':'ParseImports.lean','export_dependencies.lean':'ExportDependencies.lean'}
    for filename in ['verify.py','fetch_mathlib_cache.py','export_dependencies.py','audit_exported_proofs.py','parse_imports.lean','export_dependencies.lean']:
        dst=workspace/'scripts'/names.get(filename,filename)
        dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.is_symlink():dst.unlink()
        dst.write_bytes((root/'verification'/filename).read_bytes())
    put_link(workspace/'.lake/packages',root/'.lake/packages')
    print(f'Prepared {len(seen):,} byte-identical Lean modules.',flush=True)
    return workspace

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only',action='store_true',help='Check source hashes and prepare the build layout; does not verify proofs.')
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    workspace=prepare(root)
    if args.prepare_only:return
    def run(*args):subprocess.run(args,cwd=workspace,check=True)
    run('lake','env','python3','scripts/fetch_mathlib_cache.py')
    command=['lake','env','python3','scripts/verify.py','--project',str(workspace),'--jobs','16','--heavy-jobs','8','--memory','4096','--finite-memory','1024','--memory-budget','49152','--audit-memory','32768','--keep-going']
    overrides={'PolygonN7ClassificationPart001':4096,'Consolidated.RankFourCharts12':4096,'RootedSubsumedForest0161Proof001':2048,'Papers.SmallNonrational':8192,'Audit.SmallNonrational':8192,'Audit.SupportingLemmas':8192,'Audit.TerminalEndpoints':8192,'Audit.RankFourEndpoints':8192,'CompletedResidualCoverage':8192,'VerifiedTargets':8192,'Papers.GlobalEightRelationRowsClosed':8192}
    for name,limit in overrides.items():command.extend(['--module-memory',f'{name}={limit}'])
    run(*command)
    stamp=str(time.time_ns());output=workspace/'.lake/build'/f'dependency_export_{stamp}'
    run('lake','env','python3','scripts/export_dependencies.py','--project',str(workspace),'--output',str(output),'--batch-modules','64','--batch-input-mib','128','--memory','32768','--timeout','900')
    run('lake','env','python3','scripts/audit_exported_proofs.py','--project',str(workspace),'--export',str(output),'--output',str(workspace/'.lake/build'/f'proof_check_{stamp}'),'--batch-modules','32','--memory','32768','--timeout','900')
    print('Verification complete: all source modules, principal statements, and proof dependencies passed.',flush=True)

if __name__=='__main__':
    try:main()
    except (OSError,RuntimeError,ValueError,KeyError,subprocess.CalledProcessError) as e:
        print(f'Verification stopped: {e}',file=sys.stderr);sys.exit(1)
