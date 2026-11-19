#!/usr/bin/env python3
"""Read-only raw ConstantInfo diagnostics after the unmodified pinned verifier.
This script neither publishes nor submits, and does not certify a preflight.
Setup/prepare/toolchain installation remain the pinned pipeline's normal steps.
"""
from __future__ import annotations
import argparse,hashlib,json,os,resource,subprocess,time
from pathlib import Path
PIN='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
 a=argparse.ArgumentParser(description=__doc__)
 a.add_argument('--pipeline-root',type=Path,required=True)
 a.add_argument('--work-dir',type=Path,required=True)
 a.add_argument('--report',type=Path,required=True)
 a.add_argument('--output-dir',type=Path,required=True)
 a.add_argument('--audit-lean',type=Path,default=Path(__file__).with_name('AuditExports.lean'))
 a.add_argument('--execute',action='store_true',help='Run the unmodified official execute command once, then audit its retained exports.')
 a.add_argument('--bwrap');a.add_argument('--workflow-url',default='diagnostic-only')
 a.add_argument('--execution-budget-seconds',type=int,default=19800)
 a.add_argument('--memory-mib',type=int,default=2048)
 a.add_argument('--timeout-seconds',type=int,default=300)
 a.add_argument('--max-export-bytes',type=int,default=1024**3)
 o=a.parse_args();o.output_dir.mkdir(parents=True,exist_ok=True)
 actual=subprocess.check_output(['git','-C',str(o.pipeline_root),'rev-parse','HEAD'],text=True).strip()
 if actual!=PIN:raise SystemExit(f'Wrong pipeline revision: {actual}; expected {PIN}')
 if o.execute:
  if not o.bwrap:raise SystemExit('--execute requires --bwrap')
  subprocess.run(['python3',str(o.pipeline_root/'scripts/verify_submission.py'),'execute','--work-dir',str(o.work_dir),'--output',str(o.report),'--bwrap',o.bwrap,'--bwrap-source-tag','v0.12.0','--execution-budget-seconds',str(o.execution_budget_seconds),'--workflow-url',o.workflow_url],check=True)
 # execute returns after Comparator rejection and preserves work/exports. Its finally
 # only restores process-global accounting state; it does not delete these files.
 snapshot=o.output_dir/'mechanical-report-at-audit.json';snapshot.write_bytes(o.report.read_bytes())
 report=json.loads(snapshot.read_text());exports=[o.work_dir/'exports/challenge.export',o.work_dir/'exports/solution.export'];config=o.work_dir/'protected-comparator.json'
 receipt={'kind':'read-only diagnostic; not an official preflight or kernel verdict','pipeline_commit':actual,'mechanical_report_sha256':sha(snapshot),'mechanical_status':report.get('status'),'mechanical_stage':report.get('stage'),'audit_source_sha256':sha(o.audit_lean),'memory_limit_mib':o.memory_mib,'timeout_seconds':o.timeout_seconds}
 if not all(p.is_file() and not p.is_symlink() for p in [*exports,config]):
  receipt.update(status='blocked',reason='Both retained exports and protected comparator config are required. Source build/export may have failed before they existed.');write(o.output_dir/'audit-receipt.json',receipt);return
 receipt['exports']=[{'name':p.name,'bytes':p.stat().st_size} for p in exports]
 if sum(p.stat().st_size for p in exports)>o.max_export_bytes:
  receipt.update(status='blocked',reason='Combined export size exceeds explicit diagnostic cap; no parse or transfer attempted.');write(o.output_dir/'audit-receipt.json',receipt);return
 for d,p in zip(receipt['exports'],exports):d['sha256']=sha(p)
 receipt['protected_config_sha256']=sha(config)
 toolchain=report.get('lean_toolchain','')
 import re
 if not re.fullmatch(r'leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?',toolchain):raise SystemExit('Invalid report toolchain')
 # No Lake/project environment is imported by the diagnostic. The exact installed
 # toolchain's bundled Lake.Check.Compare + LeanExport.Parse provide raw metadata.
 env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
 prefix=Path(subprocess.check_output(['elan','run',toolchain,'lean','--print-prefix'],env=env,text=True).strip())
 shared=next((prefix/'lib/lean'/name for name in ['libLake_shared.so','libLake_shared.dylib'] if (prefix/'lib/lean'/name).is_file()),None)
 if shared is None:raise SystemExit('Bundled libLake_shared dynamic library is required for LeanExport native symbols')
 receipt['bundled_lake_library']={'path':str(shared),'sha256':sha(shared)}
 cmd=['elan','run',toolchain,'lean',f'-M{o.memory_mib}',f'--load-dynlib={shared}','--run',str(o.audit_lean.resolve()),*[str(p.resolve()) for p in exports],str(config.resolve())]
 receipt['command']=cmd;raw=o.output_dir/'audit-raw.log';started=time.monotonic()
 def limits():resource.setrlimit(resource.RLIMIT_FSIZE,(8*1024**2,8*1024**2))
 try:
  with raw.open('wb') as out:
   p=subprocess.run(cmd,cwd=o.output_dir,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=o.timeout_seconds,preexec_fn=limits)
  receipt.update(status='diagnostic-completed' if p.returncode==0 else 'diagnostic-failed',exit_code=p.returncode)
 except subprocess.TimeoutExpired:receipt.update(status='diagnostic-timeout')
 receipt['elapsed_seconds']=round(time.monotonic()-started,3)
 receipt['max_rss_kib']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
 text=raw.read_text(errors='replace');lines=text.splitlines()
 kept=lines if len(lines)<=400 else lines[:200]+['... bounded output omitted ...']+lines[-200:]
 bounded='\n'.join(kept)
 (o.output_dir/'audit-bounded.log').write_text(bounded[:800000]+'\n')
 receipt['bounded_log_sha256']=sha(o.output_dir/'audit-bounded.log');receipt['raw_log_bytes']=raw.stat().st_size
 write(o.output_dir/'audit-receipt.json',receipt)
if __name__=='__main__':main()
