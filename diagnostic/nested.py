"""Measure nested frozen graph proofs on one host. The three source scopes share one build."""
import argparse
import concurrent.futures
import graphlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import threading
import time

import support

ROOT = support.ROOT
TMP = Path(os.environ.get('RUNNER_TEMP','/tmp')) / 'frozen-nested-row29'
RESULTS = ROOT / 'diagnostic-results'
MANIFEST = ROOT / 'diagnostic/manifest.json'
MAX_FILE = 512 * 1024**2
MAX_ADDRESS = 14 * 1024**3
MIB = 1024**2

def load(p):return json.loads(p.read_text())

def save(out, data):
    raw = (json.dumps(data,indent=2,sort_keys=True)+'\n').encode()
    if len(raw)>MIB:raise ValueError('Receipt exceeded one MiB')
    tmp=out.with_suffix('.tmp');tmp.write_bytes(raw);tmp.replace(out)

def run(label, argv, env, cwd, timeout, payload=None):
    """Keep an 8-KiB log tail in RAM, per-command RSS/CPU from GNU time and a strict wall cap."""
    metric=TMP/(label+'.time');started=time.monotonic();tail=bytearray();stream=None
    command=['/usr/bin/time','-f','%e %U %S %M','-o',metric,'/usr/bin/prlimit',
             f'--as={MAX_ADDRESS}',f'--fsize={MAX_FILE}','--',*argv]
    try:
        if payload:stream=payload.open('wb')
        proc=subprocess.Popen([str(x) for x in command],cwd=cwd,env=env,stdin=subprocess.DEVNULL,
                              stdout=stream if stream else subprocess.PIPE,
                              stderr=subprocess.PIPE if stream else subprocess.STDOUT,start_new_session=True)
        pipe=proc.stderr if stream else proc.stdout
        def drain():
            while chunk:=pipe.read(16_384):
                tail.extend(chunk);del tail[:-8192]
        reader=threading.Thread(target=drain,daemon=True);reader.start();timed_out=False
        try:code=proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out=True
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            code=proc.wait()
        reader.join();pipe.close()
    finally:
        if stream:stream.close()
    row={'exit_code':code,'timed_out':timed_out,'limit_seconds':timeout,'wall_seconds':round(time.monotonic()-started,3),
         'output_tail':tail.decode(errors='replace')[-4096:] if code else ''}
    if metric.is_file():
        fields=metric.read_text().splitlines()[-1:]
        if fields and len(fields[0].split())==4:
            _,u,s,rss=fields[0].split();row.update(user_seconds=float(u),system_seconds=float(s),peak_rss_bytes=int(rss)*1024)
    return row

def inspect_export(path, scope):
    """Scan once for expression/axiom counts and every required original theorem."""
    targets=set(scope['required']); prefixes=set()
    for full in targets|set(support.AXIOMS):
        parts=full.split('.');prefixes.update('.'.join(parts[:i]) for i in range(1,len(parts)+1))
    names={0:''};found=set();axioms=[];kinds={};expressions=0
    with path.open('rb') as f:
        for line in f:
            if b'"in":' in line[:128]:
                record=json.loads(line);node=record.get('str')
                if 'in' in record and isinstance(node,dict) and node['pre'] in names:
                    full='.'.join(filter(None,[names[node['pre']],node['str']]))
                    if full in prefixes:names[record['in']]=full
            if b'"ie":' in line:
                expressions+=int('ie' in json.loads(line))
            match=support.DECL.match(line)
            if not match:continue
            kind=match[1].decode();v=json.loads(line)[kind]
            if kind=='inductive':
                for key in ['types','ctors','recs']:kinds[key]=kinds.get(key,0)+len(v[key])
            else:
                kinds[kind]=kinds.get(kind,0)+1
                if kind in ['thm','axiom']:
                    ident=names.get(v['name'],'unknown_name_'+str(v['name']))
                    if kind=='axiom':axioms.append(ident)
                    elif ident in targets:found.add(ident)
    if found!=targets or set(axioms)!=set(support.AXIOMS):
        raise ValueError('Missing theorem or incorrect axioms: '+str((targets-found,axioms)))
    return {'export_sha256':support.sha(path),'bytes':path.stat().st_size,'axioms':axioms,'declaration_kinds':kinds,
            'declarations':sum(kinds.values()),'expressions':expressions,'confirmed_theorems':sorted(found)}

def identifier():
    return {'commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],'attempt':os.environ['GITHUB_RUN_ATTEMPT'],
            'manifest_sha256':support.sha(MANIFEST)}

def tools(m):
    prefix=Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,text=True).strip());bindir=prefix/'bin'
    digests={k:support.sha(bindir/k) for k in m['tool_sha256']}
    if digests!=m['tool_sha256']:raise ValueError('Tool digest differs from prior verified direct family')
    env=dict(os.environ,LEAN_PATH=str(TMP/'build'),PATH=str(bindir)+':'+os.environ['PATH'],LEAN_ABORT_ON_PANIC='1')
    return bindir,digests,env

def build(m):
    TMP.mkdir(exist_ok=False);(TMP/'build').mkdir();RESULTS.mkdir(exist_ok=True)
    out=RESULTS/'build.json';r={**identifier(),'status':'running','modules':{},'exports':{},'stage':'source'};save(out,r)
    try:
        graph=support.source_graph(m,'replacement');src=ROOT/'source';bindir,hashes,env=tools(m)
        r.update(verified_files=len(m['files']),tool_sha256=hashes,workers=3,visible_cpus=len(os.sched_getaffinity(0)),
                 memory=Path('/proc/meminfo').read_text().splitlines()[0],free_disk=shutil.disk_usage(TMP).free,
                 lean_version=subprocess.check_output([bindir/'lean','--version'],text=True).strip())
        assert shutil.disk_usage(TMP).free >= 10*1024**3
        def compile_one(name):
            rel=Path(*name.split('.'));olean=TMP/'build'/rel.with_suffix('.olean');olean.parent.mkdir(parents=True,exist_ok=True)
            rec=run(name,[bindir/'lean','-t1','-j1','-s65536','-M4096','-DmaxHeartbeats=0','-DElab.async=false',
                          '-Ddebug.skipKernelTC=false','-o',olean,rel.with_suffix('.lean')],env,src,600)
            if rec['exit_code']==0:rec['olean_bytes']=olean.stat().st_size
            return rec
        r['stage']='build';save(out,r);started=time.monotonic();order=graphlib.TopologicalSorter(graph);order.prepare()
        waiting=list(order.get_ready());jobs={};failed=[]
        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            while (waiting or jobs) and not failed:
                while waiting and len(jobs)<3:
                    key=waiting.pop();jobs[pool.submit(compile_one,key)]=key
                done,_=concurrent.futures.wait(jobs,return_when=concurrent.futures.FIRST_COMPLETED)
                for f in done:
                    k=jobs.pop(f);row=f.result();r['modules'][k]=row
                    if row['exit_code']:failed.append(k)
                    else:order.done(k)
                waiting.extend(order.get_ready());save(out,r)
        r.update(build_wall_seconds=round(time.monotonic()-started,3),failed_modules=failed);save(out,r)
        if failed or len(r['modules'])!=len(graph):raise RuntimeError('Module compilation failed '+str(failed))
        r['stage']='original_endpoint_types';check=TMP/'EndpointTypes.lean'
        check.write_text('module\nimport NestedRow29\n'+'\n'.join('example : '+v+' := '+k for k,v in m['endpoint_types'].items())+'\n')
        r['endpoint_types']=run('types',[bindir/'lean','-t1','-j1','-M4096','-Ddebug.skipKernelTC=false',check.name],env,TMP,180)
        if r['endpoint_types']['exit_code']:raise RuntimeError('Original endpoint type audit failed')
        for s in m['scopes']:
            k=s['label'];r['stage']='export_'+k;save(out,r);dest=TMP/(k+'.ndjson')
            row=run('export_'+k,[bindir/'leanexport',s['module'],'--',*s['theorems'],*support.PRIMITIVES],env,src,300,dest)
            r['exports'][k]={'performance':row};save(out,r)
            if row['exit_code']:raise RuntimeError('Export failed '+k)
            info=inspect_export(dest,s);r['exports'][k].update(info)
            reference=m['reference_proof_exports'].get(k)
            if reference and info['export_sha256']!=reference:raise ValueError('Previously verified direct export hash differs: '+k)
            save(out,r)
        r.update(status='pass',stage='ready_for_six_mandatory_replays');save(out,r)
    except BaseException as e:
        r.update(status='failed',error=str(e)[-4000:]);save(out,r);raise

def replay(m,scope,checker):
    base=load(RESULTS/'build.json');out=RESULTS/(scope+'-'+checker+'.json')
    r={**identifier(),'scope':scope,'checker':checker,'status':'running'};save(out,r)
    try:
        assert base['status']=='pass' and all(base[k]==v for k,v in identifier().items())
        entry=base['exports'][scope];proof=TMP/(scope+'.ndjson');assert support.sha(proof)==entry['export_sha256']
        bindir,hashes,env=tools(m);r.update(export_sha256=entry['export_sha256'],export_bytes=entry['bytes'],tool_sha256=hashes,
                                          confirmed_theorems=entry['confirmed_theorems'],axioms=entry['axioms'])
        cfg=TMP/(scope+'-nanoda.json');cfg.write_text(json.dumps({'use_stdin':False,'export_file_path':str(proof),'permitted_axioms':support.AXIOMS,
                   'unpermitted_axiom_hard_error':True,'num_threads':4,'nat_extension':True,'string_extension':True}))
        argv=[bindir/'leanchecker','--silent','--from-export',proof] if checker=='lean_kernel' else [bindir/'nanoda_bin',cfg]
        rec=run(scope+'-'+checker,argv,env,TMP,m['per_checker_timeout_seconds'][scope][checker]);r.update(performance=rec,status='pass' if rec['exit_code']==0 else 'failed');save(out,r)
        if rec['exit_code']:raise RuntimeError('Checker timeout' if rec['timed_out'] else 'Checker failed')
    except BaseException as e:
        r.update(status='failed',error=str(e)[-4000:]);save(out,r);raise

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('scope',choices=['build','generic','single','eight']);p.add_argument('checker',nargs='?',choices=['lean_kernel','nanoda']);args=p.parse_args()
    m=load(MANIFEST)
    if args.scope=='build':
        assert not args.checker;build(m)
    else:
        assert args.checker;replay(m,args.scope,args.checker)
if __name__=='__main__':main()
