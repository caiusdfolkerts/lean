"""Bounded exact-source diagnostic, never a full preflight or kernel verdict."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,os,shutil,time,threading,signal,resource
p=argparse.ArgumentParser();p.add_argument('--case',required=True);p.add_argument('--work',type=Path,required=True);p.add_argument('--setup-evidence',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--pipeline',type=Path,required=True);p.add_argument('--solution-only',action='store_true');o=p.parse_args();o.output.mkdir(parents=True,exist_ok=True);root=Path(__file__).parent/'cases'/o.case;meta=json.loads((root/'source-targets.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();receipt={'kind':'measured repaired Source leaves and conditional actual Solution diagnostic; NOT full preflight','original_source_commit':meta['original_source_commit'],'repair_provenance':meta['source_repair_provenance'],'repair_status_sha256':meta['repair_status_sha256'],'diagnostic_commit':os.environ.get('GITHUB_SHA'),'workflow_run':os.environ.get('GITHUB_RUN_ID'),'targets':meta['targets'],'source_file_count':len(meta.get('sources',meta['targets'])),'all_source_and_original_lake_bytes_checked':False,'limits':{'target_timeout_seconds':600,'target_aggregate_resident_memory_bytes':12*1024**3,'per_target_output_bytes':4*1024**2,'error_excerpts_per_target':100,'error_excerpt_characters':8000,'combined_log_characters':1000000},'no_full_preflight_Comparator_kernel_or_intake_claim':True,'status':'running','phases':[]};allerrors=[];logs=[]
if o.solution_only:
 meta['targets']=[dict(next(x for x in meta['sources'] if x['path']=='lean/Solution.lean'),module='Solution')]
 receipt['targets']=meta['targets']
def save(): (o.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
def run_target(module,timeout=600):
 cmd=['elan','run',tc,'lake','--keep-toolchain','build','+'+module+':olean'];env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);env['LEAN_NUM_THREADS']='3';receipt['lake_runtime_environment']={'LEAN_NUM_THREADS':'3'};start=time.monotonic();buf=bytearray();count=0;digest=hashlib.sha256();cap=4*1024**2
 # Address-space caps prevent Lean's worker stacks from starting. Bound actual
 # aggregate resident pages instead; this does not alter any compiler option.
 child=subprocess.Popen(cmd,cwd=o.work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 done=threading.Event();memory_limit_fired=False;rss_peak=0
 def watch_memory():
  nonlocal memory_limit_fired,rss_peak
  page=os.sysconf('SC_PAGE_SIZE')
  while not done.is_set():
   resident=0
   for directory in Path('/proc').iterdir():
    if not directory.name.isdigit():continue
    try:
     if os.getpgid(int(directory.name))==child.pid:
      resident+=int((directory/'statm').read_text().split()[1])*page
    except (OSError,ValueError,IndexError):pass
   rss_peak=max(rss_peak,resident)
   if resident>12*1024**3:
    memory_limit_fired=True
    try:os.killpg(child.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    return
   done.wait(0.2)
 monitor=threading.Thread(target=watch_memory,daemon=True);monitor.start()
 def consume():
  nonlocal count
  while b:=child.stdout.read(65536):
   count+=len(b);digest.update(b)
   if len(buf)<cap:buf.extend(b[:cap-len(buf)])
 reader=threading.Thread(target=consume,daemon=True);reader.start();timed=False
 try:code=child.wait(timeout=timeout)
 except subprocess.TimeoutExpired:
  timed=True;os.killpg(child.pid,signal.SIGTERM)
  try:code=child.wait(timeout=10)
  except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);code=child.wait()
 done.set();monitor.join();reader.join();text=bytes(buf).decode(errors='replace');errors=v.solution_build_error_excerpts(text);configuration_errors=[line for line in text.splitlines() if line.startswith('error:') and any(mark in line for mark in ['no such file','bad import'])]
 record={'source_configuration_errors':configuration_errors,'module':module,'command':cmd,'exit_code':code,'timed_out':timed,'elapsed_seconds':round(time.monotonic()-start,3),'output_bytes':count,'output_sha256':digest.hexdigest(),'output_truncated':count>cap,'resident_memory_peak_bytes':rss_peak,'resident_memory_limit_fired':memory_limit_fired,'errors':errors};receipt['phases'].append(record);allerrors.extend([dict(x,target_module=module) for x in errors['errors']]);logs.append('=== '+module+' ===\n'+text+('\n... explicit target output truncation ...\n' if count>cap else ''));save()
try:
 assert subprocess.check_output(['git','-C',str(o.pipeline),'rev-parse','HEAD'],text=True).strip()=='14aa8d6b3c2f14a8540605e37144560b9a00e7e7';sys.path.insert(0,str(o.pipeline.resolve()));from scripts import verify_submission as v;assert v.MAX_BUILD_ERROR_EXCERPTS==20;v.MAX_BUILD_ERROR_EXCERPTS=100
 setup=json.loads(o.setup_evidence.read_text());(o.output/'canonical-setup-at-target.json').write_bytes(o.setup_evidence.read_bytes());receipt['canonical_setup_receipt_sha256']=sha(o.output/'canonical-setup-at-target.json');receipt['canonical_setup_status']=setup['status'];assert setup['input_hashes']==meta['input_hashes'];assert setup.get('canonical_roots'),'Canonical closure was not materialized/validated';assert not any(x['phase']=='official-mathlib-cache' and x['exit_code']!=0 for x in setup['phases']),'Official cache setup failed; no uncached full rebuild'
 manifest=json.loads((root/'lake-manifest.json').read_text());tc=(root/'lean-toolchain').read_text().strip();receipt['lean_toolchain']=tc;receipt['canonical_roots']=setup['canonical_roots'];receipt['materialized_dependency_pins']=[]
 for x in manifest['packages']:
  d=o.work/'.lake/packages'/x['name'];head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();assert head==x['rev'];assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True).strip();receipt['materialized_dependency_pins'].append({'name':x['name'],'revision':head})
 for f in ['lean-toolchain','lake-manifest.json']:assert sha(o.work/f)==meta['input_hashes'][f]
 for target in meta.get('sources',meta['targets']):
  f=root/target['input_path'];assert sha(f)==target['sha256'];q=o.work/target['path'];q.parent.mkdir(parents=True,exist_ok=True);None if q.is_file() and sha(q)==target['sha256'] else shutil.copyfile(f,q)
 shutil.copyfile(root/'original-lakefile.toml',o.work/'lakefile.toml');assert sha(o.work/'lakefile.toml')==meta['input_hashes']['original-lakefile.toml'];receipt['all_source_and_original_lake_bytes_checked']=True;save()
 for target in meta['targets']:
  run_target(target['module'], timeout=5400 if target['module']=='Solution' else 1200)

 for target in meta.get('sources',meta['targets']):assert sha(o.work/target['path'])==target['sha256']
 for f in ['lean-toolchain','lake-manifest.json']:assert sha(o.work/f)==meta['input_hashes'][f]
 assert sha(o.work/'lakefile.toml')==meta['input_hashes']['original-lakefile.toml']
 for x in manifest['packages']:
  d=o.work/'.lake/packages'/x['name'];assert subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()==x['rev'];assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True).strip()
 infrastructure=[x['module'] for x in receipt['phases'] if x['timed_out'] or x.get('resident_memory_limit_fired') or (x['exit_code']!=0 and not x['errors']['errors'] and not x.get('source_configuration_errors'))]
 receipt['infrastructure_failure_targets']=infrastructure
 receipt.update(status='targeted-source-infrastructure-failure' if infrastructure else 'targeted-source-diagnostic-completed',reported_error_count=len(allerrors),prior_full_error_count=53,all_inputs_and_pins_unchanged_after_build=True,all_requested_targets_returned=len(receipt['phases'])==len(meta['targets'])+int(receipt.get('conditional_Solution_requested',False)),all_repaired_leaf_builds_passed=all(x['exit_code']==0 for x in receipt['phases'] if x['module']!='Solution'),conditional_Solution_source_build_passed=any(x['module']=='Solution' and x['exit_code']==0 for x in receipt['phases']),omitted_error_count=sum(x['errors']['omitted_error_count'] for x in receipt['phases']),output_truncated=any(x['output_truncated'] or x['errors']['output_truncated'] for x in receipt['phases']),truncated_error_excerpt_count=sum(bool(x['truncated']) for x in allerrors))
except Exception as e:receipt.update(status='targeted-source-diagnostic-blocked',error=str(e))
finally:
 (o.output/'errors.json').write_text(json.dumps(allerrors,indent=2)+'\n');text='\n'.join(logs);receipt['combined_log_truncated']=len(text)>1000000;(o.output/'bounded.log').write_text(text[:1000000]);receipt['bounded_log_sha256']=sha(o.output/'bounded.log');receipt['errors_sha256']=sha(o.output/'errors.json');save();print(json.dumps({k:v for k,v in receipt.items() if k not in ['phases','targets','materialized_dependency_pins']},indent=2))
# Success means every requested diagnostic returned evidence, never that the target proofs passed.
raise SystemExit(0 if receipt['status']=='targeted-source-diagnostic-completed' else 1)
