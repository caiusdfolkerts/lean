#!/usr/bin/env python3
"""Canonical Challenge elaboration diagnostic. Never a full Palomar preflight."""
from __future__ import annotations
import argparse,datetime as dt,hashlib,json,os,re,shutil,signal,subprocess,sys,threading,time
from pathlib import Path
PIN='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
TOOLCHAIN=re.compile(r'leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?\Z')
ID=re.compile(r'[a-z0-9_]+\Z')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while c:=f.read(1024*1024):h.update(c)
 return h.hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def load_case(path,case_id):
 data=json.loads(path.read_text());assert data['pipeline_commit']==PIN
 if not ID.fullmatch(case_id):raise ValueError('Invalid case identifier')
 matches=[x for x in data['cases'] if x['id']==case_id]
 if len(matches)!=1:raise ValueError('Case must appear exactly once')
 case=matches[0]
 if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",case.get('module','')):raise ValueError('Invalid Challenge module name')
 root=path.parent.resolve();folder=(root/case['case_dir']).resolve()
 if not folder.is_relative_to(root):raise ValueError('Case path escapes bundle')
 for name,expected in case['hashes'].items():
  if Path(name).name!=name:raise ValueError('Unsafe input filename')
  p=folder/name
  if p.is_symlink() or not p.is_file() or sha(p)!=expected:raise ValueError(f'Input hash mismatch: {name}')
 tc=(folder/'lean-toolchain').read_text().strip()
 if tc!=case['lean_toolchain'] or not TOOLCHAIN.fullmatch(tc):raise ValueError('Toolchain mismatch')
 if (folder/'Challenge.lean').stat().st_size>100*1024 or len((folder/'Challenge.lean').read_text().splitlines())>1000:raise ValueError('Challenge exceeds bounded entry limits')
 manifest=json.loads((folder/'lake-manifest.json').read_text());seen=set()
 for package in manifest['packages']:
  name=package['name']
  if name in seen or package.get('type')!='git' or not re.fullmatch('[0-9a-f]{40}',package.get('rev','')):raise ValueError('Manifest requires unique full-commit Git dependencies')
  seen.add(name)
 if manifest.get('packagesDir')!='.lake/packages':raise ValueError('Expected ordinary canonical package directory')
 return case,folder,manifest
class Diagnostic:
 def __init__(self,o,case):
  self.o=o;self.case=case;self.logs=[];self.receipt={'schema_version':1,'kind':'Challenge-only elaboration diagnostic; NOT full preflight','case':case['id'],'challenge_module':case['module'],'source_commit':os.getenv('GITHUB_SHA'),'source_repository':os.getenv('GITHUB_REPOSITORY'),'workflow_run':os.getenv('GITHUB_RUN_ID'),'script_sha256':sha(Path(__file__)),'pipeline_commit':PIN,'meaning':'Intentional Challenge theorem placeholders are accepted. No Solution build, Comparator, external kernel or registry/intake authorization is claimed.','input_hashes':case['hashes'],'original_challenge':case['original_challenge'],'lean_toolchain':case['lean_toolchain'],'phases':[],'status':'running','started_at':dt.datetime.now(dt.timezone.utc).isoformat()}
  o.output.mkdir(parents=True,exist_ok=True);self.save()
 def save(self):write(self.o.output/'receipt.json',self.receipt)
 def run(self,phase,cmd,*,cwd,env=None,timeout=1800,required=True):
  self.receipt['phase']=phase;self.save();started=time.monotonic();head=bytearray();tail=bytearray();digest=hashlib.sha256();count=0
  child_env=(env or os.environ).copy();child_env.pop('LEAN_PATH',None);child_env.pop('LEAN_SRC_PATH',None)
  p=subprocess.Popen([str(x) for x in cmd],cwd=cwd,env=child_env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
  def consume():
   nonlocal count
   while chunk:=p.stdout.read(65536):
    count+=len(chunk);digest.update(chunk)
    if len(head)<32768:head.extend(chunk[:32768-len(head)])
    tail.extend(chunk)
    if len(tail)>65536:del tail[:-65536]
  reader=threading.Thread(target=consume,daemon=True);reader.start();timed_out=False
  try:code=p.wait(timeout=timeout)
  except subprocess.TimeoutExpired:
   timed_out=True;os.killpg(p.pid,signal.SIGTERM)
   try:code=p.wait(timeout=10)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);code=p.wait()
  reader.join();text=(bytes(head) if count<=len(head) else bytes(head)+b'\n... bounded middle omitted ...\n'+bytes(tail)).decode(errors='replace')
  record={'phase':phase,'command':[str(x) for x in cmd],'exit_code':code,'timed_out':timed_out,'elapsed_seconds':round(time.monotonic()-started,3),'output_bytes':count,'output_sha256':digest.hexdigest()};self.receipt['phases'].append(record);self.logs.append(f'=== {phase} ===\n{text}\n');self.save()
  if required and (code or timed_out):raise RuntimeError(f'{phase}: exit {code}'+(' (timeout)' if timed_out else '')+'\n'+text[-2500:])
  return code,text
 def finish(self,status,error=None):
  self.receipt['status']=status;self.receipt['finished_at']=dt.datetime.now(dt.timezone.utc).isoformat()
  if error:self.receipt['error']=str(error)[:4000]
  data='\n'.join(self.logs).encode();limit=100*1024
  if len(data)>limit:data=data[:20*1024]+b'\n... bounded diagnostic log omitted ...\n'+data[-(80*1024-100):]
  (self.o.output/'bounded.log').write_bytes(data);self.receipt['bounded_log_sha256']=sha(self.o.output/'bounded.log');self.receipt['bounded_log_bytes']=len(data);self.save()
def execute(o,case,folder,manifest):
 d=Diagnostic(o,case)
 try:
  if o.work.exists():raise ValueError('Work directory must be fresh')
  o.work.mkdir(parents=True);workspace=o.work/'workspace';workspace.mkdir();control=o.work/'control';control.mkdir()
  d.run('pipeline-pin',['git','-C',o.pipeline,'rev-parse','HEAD'],cwd=control)
  actual=subprocess.check_output(['git','-C',o.pipeline,'rev-parse','HEAD'],text=True).strip()
  if actual!=PIN:raise ValueError(f'Wrong pipeline commit: {actual}')
  sys.path.insert(0,str(o.pipeline.resolve()))
  from scripts.render_challenge import challenge_only_manifest
  from scripts.verify_submission import allowed_roots,canonical_repository,github_repository,materialize_packages,manifest_packages,package_checkout,parse_lean_header
  # This pinned helper reads each exact canonical root's own manifest and
  # rejects any substituted revision in its closure. No submitted Lake code runs.
  d.receipt['phase']='canonical-manifest-validation';d.save()
  canonical,excluded=challenge_only_manifest(manifest,control)
  if excluded:raise ValueError(f'Original manifest has Solution-only/noncanonical packages: {excluded}; no automatic rewrite is permitted')
  if {p['name'] for p in canonical['packages']}!={p['name'] for p in manifest['packages']}:raise ValueError('Canonical closure differs from the original manifest')
  _roots,aliases=allowed_roots();direct=[]
  for p in manifest['packages']:
   repository=github_repository(p.get('url',''))
   if repository and repository.lower() in aliases:direct.append(p)
  requested=case.get('canonical_direct_roots')
  if requested is not None:
   if not isinstance(requested,list) or not requested or len(set(requested))!=len(requested):raise ValueError('Invalid explicit canonical direct-root list')
   known={p['name'] for p in direct}
   if not set(requested)<=known:raise ValueError('Explicit direct root is not a canonical pinned manifest root')
   direct=[p for p in direct if p['name'] in requested]
  if not direct:raise ValueError('A pinned canonical Mathlib/TauCeti root is required')
  d.receipt['generated_canonical_direct_roots']=[p['name'] for p in direct]
  name=manifest.get('name')
  if not isinstance(name,str) or not name:raise ValueError('Manifest package name missing')
  config=[f'name = {json.dumps(name)}','version = "0.1.0"','defaultTargets = ["ChallengeDiagnostic"]','']
  for p in direct:
   config += ['[[require]]',f'name = {json.dumps(p["name"])}',f'git = {json.dumps(p["url"])}',f'rev = {json.dumps(p["rev"])}','']
  config += ['[[lean_lib]]','name = "ChallengeDiagnostic"','srcDir = "."',f'roots = [{json.dumps(case["module"])}]','defaultFacets = ["elabArts"]','']
  (workspace/'lakefile.toml').write_text('\n'.join(config))
  module_path=Path(*case['module'].split('.'));challenge_path=workspace/module_path.with_suffix('.lean');challenge_path.parent.mkdir(parents=True,exist_ok=True)
  shutil.copyfile(folder/'Challenge.lean',challenge_path)
  for filename in ['lean-toolchain','lake-manifest.json']:shutil.copyfile(folder/filename,workspace/filename)
  d.receipt['generated_lakefile_sha256']=sha(workspace/'lakefile.toml');d.receipt['manifest_policy']='Original manifest bytes are preserved; all canonical-root closure pins checked. No lake update or dependency/toolchain override.';d.save()
  tc=case['lean_toolchain'];elan=['elan','run',tc];base_env=os.environ.copy();base_env.pop('LEAN_PATH',None);base_env.pop('LEAN_SRC_PATH',None)
  code,prefix=d.run('lean-prefix',elan+['lean','--print-prefix'],cwd=workspace);lean_prefix=Path(prefix.strip())
  if not lean_prefix.is_dir():raise ValueError('Invalid selected toolchain prefix')
  d.receipt['lean_binary_sha256']=sha(lean_prefix/'bin/lean');_,version=d.run('lean-version',elan+['lean','--version'],cwd=workspace);d.receipt['lean_version']=version.strip()
  _,header_text=d.run('challenge-header',elan+['lean','--deps-json',str(challenge_path)],cwd=workspace);header=parse_lean_header(header_text)
  if not header.is_module:raise ValueError('Challenge does not use the module system')
  d.receipt['direct_imports']=list(header.imports);d.save()
  d.receipt['phase']='materialize-exact-canonical-closure';d.save();materialize_packages(workspace,checkout=workspace,base_env=base_env)
  packages=manifest_packages(workspace);roots=[]
  for package in packages:
   repository=canonical_repository(package['repository'],aliases)
   if package['repository'].lower() in aliases:
    package_dir=package_checkout(workspace,package,checkout=workspace)
    root_tc=(package_dir/'lean-toolchain').read_text().strip()
    if root_tc!=tc:raise ValueError(f'Canonical root {package["name"]} toolchain {root_tc} differs; no override permitted')
    roots.append({'name':package['name'],'repository':repository,'revision':package['revision'],'lean_toolchain':root_tc})
  d.receipt['canonical_roots']=roots;d.save()
  if any(x['repository'].lower()=='leanprover-community/mathlib4' for x in roots):
   d.run('official-mathlib-cache',elan+['lake','--keep-toolchain','exe','cache','get'],cwd=workspace,timeout=o.setup_timeout)
  # Mathlib is obtained from its exact official cache. Build only explicitly
  # imported canonical TauCeti modules, never a submitted project's targets.
  tau=[m for m in header.imports if m=='TauCeti' or m.startswith('TauCeti.')]
  if tau:d.run('canonical-tauceti-imports',elan+['lake','--keep-toolchain','build',*[f'+{m}:olean' for m in tau]],cwd=workspace,timeout=o.setup_timeout)
  if sha(workspace/'lake-manifest.json')!=case['hashes']['lake-manifest.json']:raise ValueError('Lake changed original manifest bytes; refusing to assert exact-manifest compilation')
  if sha(workspace/'lean-toolchain')!=case['hashes']['lean-toolchain']:raise ValueError('Lake changed the original toolchain file')
  pins=[]
  for package in packages:
   directory=package_checkout(workspace,package,checkout=workspace)
   _,head=d.run('dependency-head-'+package['name'],['git','-C',directory,'rev-parse','HEAD'],cwd=workspace)
   if head.strip()!=package['revision']:raise ValueError('Dependency HEAD drifted')
   _,dirty=d.run('dependency-source-'+package['name'],['git','-C',directory,'status','--porcelain','--untracked-files=no'],cwd=workspace)
   if dirty.strip():raise ValueError(f'Canonical tracked source changed: {package["name"]}')
   pins.append({'name':package['name'],'repository':package['repository'],'revision':head.strip()})
  d.receipt['materialized_dependency_pins']=pins;d.save();output=workspace/'diagnostic-output';output.mkdir();artifact=output/module_path.with_suffix('.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
  compile_cmd=elan+['lake','--keep-toolchain','env','lean','--trust=0','-j1',f'-M{o.memory_mib}','-DElab.async=false','-Ddebug.skipKernelTC=false',f'--root={workspace}','-o',str(artifact),str(challenge_path)]
  code,_=d.run('challenge-elaboration',compile_cmd,cwd=workspace,timeout=o.compile_timeout,required=False)
  d.receipt['challenge_exit_code']=code
  for filename in ['Challenge.lean','lean-toolchain','lake-manifest.json']:
   target=challenge_path if filename=='Challenge.lean' else workspace/filename
   if sha(target)!=case['hashes'][filename]:raise ValueError(f'Compilation changed input {filename}')
  if code==0 and not artifact.is_file():raise ValueError('Lean returned success without its expected Challenge artifact')
  if code==0:d.receipt['challenge_olean_sha256']=sha(artifact)
  status='challenge-elaboration-timed-out' if d.receipt['phases'][-1]['timed_out'] else ('challenge-elaborated' if code==0 else 'challenge-elaboration-failed')
  d.finish(status);return 0 if code==0 else 1
 except Exception as error:d.finish('diagnostic-blocked',error);return 2

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['inspect','list','check-inputs','run']);p.add_argument('--cases',type=Path,default=Path(__file__).with_name('cases.json'));p.add_argument('--case');p.add_argument('--pipeline',type=Path);p.add_argument('--work',type=Path);p.add_argument('--output',type=Path);p.add_argument('--memory-mib',type=int,default=8192);p.add_argument('--setup-timeout',type=int,default=2400);p.add_argument('--compile-timeout',type=int,default=2400);o=p.parse_args();data=json.loads(o.cases.read_text())
 if o.command=='list':
  raw=os.getenv('DIAGNOSTIC_CASE_FILTER','').strip();selected=raw.split(',') if raw else data.get('default_case_ids',[x['id'] for x in data['cases']])
  for name in selected:load_case(o.cases,name)
  if len(set(selected))!=len(selected):raise ValueError('Duplicate case filter')
  value=json.dumps(selected)
  if os.getenv('GITHUB_OUTPUT'):
   with open(os.environ['GITHUB_OUTPUT'],'a') as f:f.write('cases='+value+'\n')
  print(value);return 0
 if o.command=='check-inputs':
  for case in data['cases']:load_case(o.cases,case['id'])
  print(f'Validated {len(data["cases"])} exact source/toolchain/manifest snapshots without invoking Lean or fetching dependencies.');return 0
 if not o.case:p.error('--case is required')
 case,folder,manifest=load_case(o.cases,o.case)
 if o.command=='inspect':
  if os.getenv('GITHUB_OUTPUT'):
   with open(os.environ['GITHUB_OUTPUT'],'a') as f:f.write('lean_toolchain='+case['lean_toolchain']+'\n')
  print(json.dumps({'id':case['id'],'lean_toolchain':case['lean_toolchain'],'hashes':case['hashes']},indent=2));return 0
 if not all([o.pipeline,o.work,o.output]):p.error('run requires --pipeline --work --output')
 o.pipeline=o.pipeline.resolve();o.work=o.work.resolve();o.output=o.output.resolve();return execute(o,case,folder,manifest)
if __name__=='__main__':raise SystemExit(main())
