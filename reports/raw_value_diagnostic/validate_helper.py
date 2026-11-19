#!/usr/bin/env python3
"""Compile the exact core-only diagnostic before any project source build."""
import argparse,hashlib,json,os,resource,subprocess,time
from pathlib import Path
a=argparse.ArgumentParser();a.add_argument('--toolchain',required=True);a.add_argument('--helper',type=Path,required=True);a.add_argument('--output',type=Path,required=True);o=a.parse_args();o.output.mkdir(parents=True,exist_ok=True);env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();prefix=Path(subprocess.check_output(['elan','run',o.toolchain,'lean','--print-prefix'],env=env,text=True).strip());shared=prefix/'lib/lean/libLake_shared.so';assert shared.is_file();target=o.output/'AuditExportsFirstDifferences.olean';log=o.output/'helper-check-raw.log';cmd=['elan','run',o.toolchain,'lean','-j1','-M1024','-DElab.async=false',f'--load-dynlib={shared}','-o',str(target.resolve()),str(o.helper.resolve())];started=time.monotonic();receipt={'kind':'early core-only diagnostic helper compile; no project source imported/built','toolchain':o.toolchain,'helper_sha256':sha(o.helper),'command':cmd,'memory_mib':1024,'timeout_seconds':120,'bundled_lake_library_sha256':sha(shared)}
def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(1024*1024,1024*1024))
code=1
try:
 with log.open('wb') as f:result=subprocess.run(cmd,cwd=o.helper.resolve().parent,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120,preexec_fn=limit)
 code=result.returncode;receipt.update(status='helper-compiled' if code==0 else 'helper-compile-failed',exit_code=code)
except subprocess.TimeoutExpired:receipt.update(status='helper-compile-timeout')
receipt['elapsed_seconds']=round(time.monotonic()-started,3);text=log.read_text(errors='replace');receipt['raw_log_bytes']=log.stat().st_size;receipt['raw_log_sha256']=sha(log);bounded=text if len(text)<=65536 else text[:16384]+'\n... explicit bounded middle omission ...\n'+text[-49152:];(o.output/'helper-check-bounded.log').write_text(bounded);receipt['log_truncated']=len(text)>65536
if code==0:assert target.is_file();receipt['compiled_olean_sha256']=sha(target)
(o.output/'helper-check.json').write_text(json.dumps(receipt,indent=2)+'\n');raise SystemExit(code)
