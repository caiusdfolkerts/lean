"""Replay the saved joint proof in one kernel and atomically update its bounded receipt."""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import time
from run import AXIOMS, ROOT, sha

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('phase',choices=['lean_kernel','nanoda','con_ron'])
    phase=p.parse_args().phase
    receipt=ROOT/'diagnostic-results/replacement.json'
    r=json.loads(receipt.read_text())
    assert r['commit']==os.environ['GITHUB_SHA'] and r['status']=='exported'
    tmp=Path(os.environ['RUNNER_TEMP'])
    proof=tmp/'graph-family.ndjson'
    assert sha(proof)==r['exports']['joint']['sha256']
    bindir=Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,text=True).strip())/'bin'
    cfg=tmp/'graph-family-nanoda.json'
    cfg.write_text(json.dumps({'use_stdin':False,'export_file_path':str(proof),'permitted_axioms':AXIOMS,
        'unpermitted_axiom_hard_error':False,'num_threads':4,'nat_extension':True,'string_extension':True}))
    cmd={'lean_kernel':['leanchecker','--silent','--from-export',proof],
         'nanoda':['nanoda_bin',cfg],'con_ron':['con-ron','--jobs=2','--verified',proof]}[phase]
    assert sha(bindir/cmd[0])==r['tools'][cmd[0]]
    cmd[0]=bindir/cmd[0]
    def save():
        data=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode()
        assert len(data)<=1_048_576
        dest=receipt.with_suffix('.tmp')
        dest.write_bytes(data);dest.replace(receipt)
    r['stage']=phase;save()
    start=time.monotonic()
    before=resource.getrusage(resource.RUSAGE_CHILDREN)
    log=tmp/(phase+'.log')
    with log.open('wb') as f:
        code=subprocess.run(cmd,cwd=tmp,env=dict(os.environ,LEAN_ABORT_ON_PANIC='1'),
                            stdout=f,stderr=subprocess.STDOUT).returncode
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    with log.open('rb') as f:
        f.seek(max(0,log.stat().st_size-8000));tail=f.read().decode(errors='replace')
    r['phases'][phase]={'exit_code':code,'wall_seconds':round(time.monotonic()-start,3),
                       'peak_rss_bytes':after.ru_maxrss*1024,'user_seconds':after.ru_utime-before.ru_utime,
                       'system_seconds':after.ru_stime-before.ru_stime,'checker_output_tail':tail}
    if code:r.update(status='failed',stage=phase)
    elif all(r['phases'].get(k,{}).get('exit_code')==0 for k in ['lean_kernel','nanoda','con_ron']):
        r.update(status='pass',stage='completed')
    save();print(phase,code,tail[-600:],flush=True)
    raise SystemExit(code)
if __name__=='__main__':
    main()
