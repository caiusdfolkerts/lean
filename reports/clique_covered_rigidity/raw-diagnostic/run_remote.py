#!/usr/bin/env python3
"""Frozen canonical clique raw-ConstantInfo diagnostic; never a full preflight."""
from __future__ import annotations
import argparse,datetime as dt,hashlib,json,os,re,shutil,signal,subprocess,sys,threading,time
from pathlib import Path
PIN='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
LIMIT=1048576

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while c:=f.read(1048576):h.update(c)
 return h.hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def validate(bundle):
 manifest=json.loads((bundle/'manifest.json').read_text());snapshot=bundle/manifest['snapshot_directory']
 if manifest['pipeline_commit']!=PIN:raise ValueError('Pipeline pin mismatch')
 actual={str(p.relative_to(snapshot)) for p in snapshot.rglob('*') if p.is_file()}
 if actual!=set(manifest['snapshot_files']):raise ValueError('Snapshot file inventory mismatch')
 for rel,expected in manifest['snapshot_files'].items():
  p=snapshot/rel
  if p.is_symlink() or not p.is_file() or sha(p)!=expected:raise ValueError('Snapshot mismatch: '+rel)
 if (snapshot/'lean-toolchain').read_text().strip()!=manifest['toolchain']:raise ValueError('Toolchain mismatch')
 dependencies=json.loads((snapshot/'lake-manifest.json').read_text())
 for p in dependencies['packages']:
  if p.get('type')!='git' or not re.fullmatch('[0-9a-f]{40}',p.get('rev','')):raise ValueError('Dependency not pinned Git')
 roots=[p for p in dependencies['packages'] if p['name']=='mathlib']
 if len(roots)!=1 or roots[0]['rev']!=manifest['mathlib_rev']:raise ValueError('Mathlib pin mismatch')
 return manifest,snapshot,dependencies
class Runner:
 def __init__(self,o,m):
  self.o=o;o.output.mkdir(parents=True,exist_ok=True)
  self.receipt={'schema_version':1,'kind':'raw ConstantInfo diagnostic; NOT full preflight','status':'running','started_at':dt.datetime.now(dt.timezone.utc).isoformat(),'pipeline_commit':PIN,'diagnostic_source_commit':os.getenv('GITHUB_SHA'),'diagnostic_source_repository':os.getenv('GITHUB_REPOSITORY'),'workflow_run':os.getenv('GITHUB_RUN_ID'),'frozen_input_files':m['snapshot_files'],'source_public_commit':m['source_public_commit'],'toolchain':m['toolchain'],'worker_count':1,'lean_memory_mib':o.memory_mib,'log_limit_each_bytes':LIMIT,'targets':{},'phases':[],'meaning':'Source/import-all and independent Challenge values only. No Comparator, external kernel, registry/intake action or permission is claimed.'}
  self.save()
 def save(self):write(self.o.output/'receipt.json',self.receipt)
 def run(self,name,cmd,cwd,env=None,timeout=2400,required=True):
  self.receipt['phase']=name;self.save();started=time.monotonic();head=bytearray();tail=bytearray();digest=hashlib.sha256();count=0
  child_env=(env or os.environ).copy()
  child=subprocess.Popen([str(x) for x in cmd],cwd=cwd,env=child_env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
  def consume():
   nonlocal count
   while chunk:=child.stdout.read(65536):
    count+=len(chunk);digest.update(chunk)
    if len(head)<LIMIT*3//4:head.extend(chunk[:LIMIT*3//4-len(head)])
    tail.extend(chunk)
    if len(tail)>LIMIT//4:del tail[:-LIMIT//4]
  reader=threading.Thread(target=consume,daemon=True);reader.start();expired=False
  try:code=child.wait(timeout=timeout)
  except subprocess.TimeoutExpired:
   expired=True;os.killpg(child.pid,signal.SIGTERM)
   try:code=child.wait(timeout=10)
   except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);code=child.wait()
  reader.join();marker=b'\n... BOUNDED LOG: middle omitted ...\n'
  if count<=len(head):data=bytes(head)
  elif count<=LIMIT:
   # Tail may overlap the retained head; preserve exactly one full stream.
   data=bytes(head)+bytes(tail)[-(count-len(head)):]
  else:data=bytes(head[:LIMIT*3//4-len(marker)])+marker+bytes(tail)
  log=self.o.output/(name+'.log');log.write_bytes(data)
  row={'phase':name,'command':[str(x) for x in cmd],'exit_code':code,'timed_out':expired,'elapsed_seconds':round(time.monotonic()-started,3),'full_stream_bytes':count,'full_stream_sha256':digest.hexdigest(),'log_truncated':count>LIMIT,'bounded_log_file':log.name,'bounded_log_bytes':len(data),'bounded_log_sha256':sha(log)}
  self.receipt['phases'].append(row);self.save();print(json.dumps({'phase':name,'exit_code':code,'output_bytes':count,'truncated':row['log_truncated']}),flush=True)
  if required and (code or expired):raise RuntimeError(name+' failed; inspect '+log.name)
  return code,data.decode(errors='replace')
 def finish(self,status,error=None):
  self.receipt['status']=status;self.receipt['finished_at']=dt.datetime.now(dt.timezone.utc).isoformat()
  if error:self.receipt['error']=str(error)[:4000]
  self.save()
def materialize(o):
 sys.path.insert(0,str(o.pipeline));from scripts.render_challenge import challenge_only_manifest
 from scripts.verify_submission import materialize_packages,manifest_packages,package_checkout,allowed_roots,canonical_repository
 workspace=o.work/'workspace';original=json.loads((workspace/'lake-manifest.json').read_text());control=o.work/'control';control.mkdir(exist_ok=True)
 canonical,excluded=challenge_only_manifest(original,control)
 if excluded:raise ValueError('Noncanonical dependency excluded; refusing automatic rewrite')
 expected={p['name']:p['rev'] for p in original['packages']};actual={p['name']:p['rev'] for p in canonical['packages']}
 if expected!=actual:raise ValueError('Canonical closure differs from frozen manifest')
 env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
 materialize_packages(workspace,checkout=workspace,base_env=env)
 _,aliases=allowed_roots();records=[]
 for p in manifest_packages(workspace):
  folder=package_checkout(workspace,p,checkout=workspace);head=subprocess.check_output(['git','-C',folder,'rev-parse','HEAD'],text=True).strip()
  if head!=p['revision']:raise ValueError('Dependency checkout drift')
  dirty=subprocess.check_output(['git','-C',folder,'status','--porcelain','--untracked-files=no'],text=True)
  if dirty.strip():raise ValueError('Dependency tracked source dirty')
  repository=canonical_repository(p['repository'],aliases)
  if p['repository'].lower() in aliases and (folder/'lean-toolchain').read_text().strip()!=(workspace/'lean-toolchain').read_text().strip():raise ValueError('Canonical root toolchain mismatch')
  records.append({'name':p['name'],'repository':repository,'revision':head})
 write(o.work/'canonical-closure.json',records)
 return 0
def run(o,m,snapshot,deps):
 r=Runner(o,m)
 try:
  if o.work.exists():raise ValueError('Work directory must be fresh')
  o.work.mkdir(parents=True);workspace=o.work/'workspace';shutil.copytree(snapshot,workspace)
  for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LEAN','LAKE_OVERRIDE_LEAN']:os.environ.pop(key,None)
  os.environ['LEAN_NUM_THREADS']='1'
  _,pin=r.run('pipeline-pin',['git','-C',o.pipeline,'rev-parse','HEAD'],o.work)
  if pin.strip()!=PIN:raise ValueError('Wrong pipeline commit')
  mathlib=next(p for p in deps['packages'] if p['name']=='mathlib')
  config=['name = '+json.dumps(deps['name']),'version = "0.1.0"','defaultTargets = []','[[require]]','name = "mathlib"','git = '+json.dumps(mathlib['url']),'rev = '+json.dumps(mathlib['rev']),'[[lean_lib]]','name = "RawDiagnosticPaths"','srcDir = "."','roots = ["Challenge", "RawChallengeProbe", "RawSourceProbe", "RawLiteralProbe"]','allowImportAll = true','']
  (workspace/'lakefile.toml').write_text('\n'.join(config));r.receipt['generated_lakefile_sha256']=sha(workspace/'lakefile.toml');r.save()
  r.run('canonical-materialization',[sys.executable,Path(__file__).resolve(),'_materialize','--pipeline',o.pipeline,'--work',o.work],o.work)
  r.receipt['canonical_dependency_closure']=json.loads((o.work/'canonical-closure.json').read_text());r.save()
  elan=['elan','run',m['toolchain']]
  _,prefix=r.run('lean-prefix',elan+['lean','--print-prefix'],workspace);binary=Path(prefix.strip())/'bin/lean'
  if not binary.is_file():raise ValueError('Invalid exact toolchain prefix')
  r.receipt['lean_binary_sha256']=sha(binary);_,version=r.run('lean-version',elan+['lean','--version'],workspace);r.receipt['lean_version']=version.strip();r.save()
  r.run('official-mathlib-cache',elan+['lake','--keep-toolchain','exe','cache','get'],workspace)
  # Keep optional checkpoint/report persistence unavailable just as in preflight;
  # the actual source validations and their assertions still execute unchanged.
  for name in ['checkpoints','reports']:
   directory=workspace/'.lake'/name;directory.mkdir(parents=True,exist_ok=True);directory.chmod(0o555)
  r.receipt['optional_audit_persistence_directories_read_only']=['.lake/checkpoints','.lake/reports'];r.save()
  sys.path.insert(0,str(o.pipeline));from scripts.verify_submission import parse_lean_header,manifest_packages,package_checkout
  files={'.'.join(p.relative_to(workspace/'source').with_suffix('').parts):p for p in (workspace/'source').rglob('*.lean')}
  files.update({n:workspace/(n+'.lean') for n in ['Challenge',*m['targets']]})
  graphs={};headers={}
  for n,p in sorted(files.items()):
   code,output=r.run('header-'+n.replace('.','_'),elan+['lean','--deps-json',p],workspace)
   h=parse_lean_header(output)
   if not h.is_module:raise ValueError('Non-module source '+n)
   headers[n]=list(h.imports);graphs[n]=[d for d in h.imports if d in files]
  r.receipt['module_import_graph']=headers;r.save()
  order=[];seen=set();active=set()
  def visit(n):
   if n in seen:return
   if n in active:raise ValueError('Import cycle '+n)
   active.add(n)
   for d in graphs[n]:visit(d)
   active.remove(n);seen.add(n);order.append(n)
  out=workspace/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True);results={}
  for target in m['targets']:
   order=[];visit(target);closure=list(order);r.receipt['targets'][target]={'status':'building','new_modules':closure};r.save()
   for n in closure:
    if any(results.get(d)!=0 for d in graphs[n]):results[n]=125;continue
    dest=out/Path(*n.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    source=files[n];source_root=workspace/'source' if source.is_relative_to(workspace/'source') else workspace
    cmd=elan+['lake','--keep-toolchain','env','lean','--trust=0','-j1',f'-M{o.memory_mib}','-t0','-s65536','-DElab.async=false','-Ddebug.skipKernelTC=false','--root='+str(source_root),'-o',dest,source]
    results[n],compile_text=r.run('compile-'+n.replace('.','_'),cmd,workspace,timeout=3600,required=False)
    if results[n] and re.search(r'lean::memory_exception|maximum memory|out of memory|memory limit',compile_text,re.I):
     r.receipt['targets'][target]['status']='memory-exhausted';r.receipt['memory_exhaustion']=True;r.receipt['module_exit_codes']=results;r.finish('raw-diagnostic-resource-exhausted')
     if os.getenv('GITHUB_OUTPUT'):
      with open(os.environ['GITHUB_OUTPUT'],'a') as f:f.write('memory_exhausted=true\n')
     return 83
    if results[n]==0 and not dest.is_file():raise ValueError('Compiler success without .olean '+n)
   r.receipt['targets'][target]['status']='elaborated' if results.get(target)==0 else 'failed-or-dependency-failed';r.receipt['targets'][target]['exit_code']=results.get(target);r.save()
  # Confirm all frozen mathematical inputs and the manifest survived untouched.
  for rel,expected in m['snapshot_files'].items():
   if sha(workspace/rel)!=expected:raise ValueError('Frozen input changed: '+rel)
  for p in manifest_packages(workspace):
   directory=package_checkout(workspace,p,checkout=workspace)
   if subprocess.check_output(['git','-C',directory,'rev-parse','HEAD'],text=True).strip()!=p['revision']:raise ValueError('Dependency pin drift')
   if subprocess.check_output(['git','-C',directory,'status','--porcelain','--untracked-files=no'],text=True).strip():raise ValueError('Dependency source changed')
  r.receipt['module_exit_codes']=results
  okay=all(results.get(t)==0 for t in m['targets']);r.finish('raw-diagnostic-elaborated' if okay else 'raw-diagnostic-compile-failed');return 0 if okay else 1
 except Exception as e:r.finish('raw-diagnostic-blocked',e);return 2

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['check-inputs','run','_materialize','finalize']);p.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--pipeline',type=Path);p.add_argument('--work',type=Path);p.add_argument('--output',type=Path);p.add_argument('--memory-mib',type=int,choices=[4096,8192],default=4096);o=p.parse_args();o.bundle=o.bundle.resolve()
 if o.command=='_materialize':o.pipeline=o.pipeline.resolve();o.work=o.work.resolve();return materialize(o)
 m,snapshot,deps=validate(o.bundle)
 if o.command=='check-inputs':print(json.dumps({'validated_files':len(m['snapshot_files']),'toolchain':m['toolchain'],'targets':m['targets'],'compiler_started':False},indent=2));return 0
 if o.command=='finalize':
  o.output.mkdir(parents=True,exist_ok=True);f=o.output/'receipt.json';d=json.loads(f.read_text()) if f.exists() else {'kind':'raw ConstantInfo diagnostic; NOT full preflight','status':'diagnostic-not-started','frozen_input_files':m['snapshot_files']}
  if d['status']=='running':d['status']='diagnostic-interrupted'
  d['workflow_steps']=json.loads(os.getenv('DIAGNOSTIC_STEPS','{}'));write(f,d);return 0
 if not all([o.pipeline,o.work,o.output]):p.error('run requires --pipeline --work --output')
 o.pipeline=o.pipeline.resolve();o.work=o.work.resolve();o.output=o.output.resolve();return run(o,m,snapshot,deps)
if __name__=='__main__':raise SystemExit(main())
