"""Build the common prerequisites once, then measure the baseline and pooled 30-target proofs."""
import argparse
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]
MFILE=ROOT/'diagnostic/manifest.json'
IMPORT=re.compile(r'^(?:public )?(?:meta )?import (?:all )?(\S+)\s*$',re.M)
def digest(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true')
    parser.add_argument('--external',action='store_true')
    args=parser.parse_args()
    manifest=json.loads(MFILE.read_text())
    assert (ROOT/'lean-toolchain').read_text().strip()==manifest['lean']
    assert next(v['rev'] for v in json.loads((ROOT/'lake-manifest.json').read_text())['packages'] if v['name']=='mathlib')==manifest['mathlib']
    for name,d in manifest['files'].items():
        p=ROOT/name
        assert p.stat().st_size==d['bytes'] and digest(p)==d['sha256'],name
    variants=manifest['variants'];graphs={}
    for var,v in variants.items():
        mods=v['modules']
        g={};external=set()
        for n,f in mods.items():
            ds=IMPORT.findall((ROOT/f).read_text());g[n]=[d for d in ds if d in mods];external.update(set(ds)-mods.keys())
        assert sorted(external)==v['external']
        todo=[manifest['endpoint']];reached=set()
        while todo:
            n=todo.pop()
            if n not in reached:reached.add(n);todo.extend(g[n])
        assert reached==set(g)
        graphs[var]=g
    common=set.intersection(*(set(g) for g in graphs.values()))
    common={n for n in common if all(v['modules'][n]==variants['baseline']['modules'][n] for v in variants.values())}
    nodes=list(graphlib.TopologicalSorter(graphs['baseline']).static_order())
    for n in nodes:
        if n in common and any(d not in common for d in graphs['baseline'][n]):common.remove(n)
    external=sorted({n for v in variants.values() for n in v['external'] if n.startswith('Mathlib.')})
    if args.external:print(' '.join(external));return
    print('Verified exact input closure of each variant', {k:len(g) for k,g in graphs.items()},len(common),'shared prerequisites', flush=True)
    if not args.run:return
    # Import a tested streaming reader only after source validation, and suppress Python cache files in checkout.
    from lean_export_reader import PRIMITIVES,export_measurements
    results=ROOT/'diagnostic-results';results.mkdir(exist_ok=True)
    receipt=results/'projection-pool.json'
    r={'status':'running','stage':'setup','commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],
       'manifest_sha256':digest(MFILE),'target':manifest['theorem'],'modules':{},'checks':{},'exports':{}}
    def save():
        content=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode();assert len(content)<1_048_576
        temp=receipt.with_suffix('.tmp');temp.write_bytes(content);temp.replace(receipt)
    save()
    with tempfile.TemporaryDirectory(prefix='projection-pool-',dir=os.environ['RUNNER_TEMP']) as t:
        work=Path(t)
        try:
            srcs={};builds={}
            for var in ['common','baseline','pooled','indexed']:
                srcs[var]=work/(var+'-source');srcs[var].mkdir()
                builds[var]=work/(var+'-build');builds[var].mkdir()
                spec=variants['baseline' if var=='common' else var]
                for key,phy in spec['paths'].items():
                    dest=srcs[var]/key;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/phy,dest)
            bin_dir=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin'
            lean=bin_dir/'lean';r['toolchain']=subprocess.check_output([lean,'--version'],text=True).strip()
            assert re.search(r'\b4\.35\.0\b',r['toolchain'])
            r['tools']={t:digest(bin_dir/t) for t in ['lean','leanexport']};save()
            mathlib=[str(Path(x).resolve()) for x in os.environ['LEAN_PATH'].split(os.pathsep) if x]
            def measure(var,args,payload=None):
                metric=work/'measure.time';log=work/'measure.log'
                env=dict(os.environ,LEAN_ABORT_ON_PANIC='1',LEAN_PATH=os.pathsep.join([str(builds[var]),str(builds['common']),*mathlib]),
                         PATH=str(bin_dir)+os.pathsep+os.environ['PATH'])
                start=time.monotonic();cmd=['/usr/bin/time','-f','%U %S %M','-o',metric,*args]
                with log.open('wb') as f:
                    if payload is None:x=subprocess.run(cmd,env=env,cwd=srcs[var],stdout=f,stderr=subprocess.STDOUT)
                    else:
                        with payload.open('wb') as out:x=subprocess.run(cmd,env=env,cwd=srcs[var],stdout=out,stderr=f)
                user,sys,rss=metric.read_text().splitlines()[-1].split()
                d={'exit_code':x.returncode,'wall_seconds':round(time.monotonic()-start,3),'user_seconds':float(user),'system_seconds':float(sys),'peak_rss_bytes':int(rss)*1024}
                if x.returncode:
                    with log.open('rb') as f:f.seek(max(0,log.stat().st_size-8000));d['error_tail']=f.read().decode(errors='replace')
                return d
            for var in ['common','baseline','pooled','indexed']:
                graph=graphs['baseline' if var=='common' else var]
                selected=common if var=='common' else set(graph)-common
                r['modules'][var]={}
                for n in graphlib.TopologicalSorter(graph).static_order():
                    if n not in selected:continue
                    rel=Path(*n.split('.')).with_suffix('.lean');out=builds[var]/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
                    r['stage']=var+'.'+n;save()
                    d=measure(var,[lean,'-t1','-j1','-s65536','-M4096','-DmaxHeartbeats=0','-DElab.async=false','-Ddebug.skipKernelTC=false','-o',out,rel])
                    r['modules'][var][n]=d
                    if d['exit_code']:raise RuntimeError(r['stage']+' '+d.get('error_tail',''))
                    d['olean_bytes']=out.stat().st_size
                    d['all_olean_bytes']=sum(f.stat().st_size for f in out.parent.glob(out.name+'*'))
                    save()
                if var=='common':continue
                audit=srcs[var]/'CheckProjection.lean'
                audit.write_text('module\nimport '+manifest['endpoint']+'\nexample : '+manifest['type']+' := '+manifest['theorem']+'\n')
                c=measure(var,[lean,'-t1','-j1','-M4096','-Ddebug.skipKernelTC=false',audit.name])
                r['checks'][var]=c;save()
                if c['exit_code']:raise RuntimeError(c.get('error_tail','endpoint type audit failed'))
                exp=work/'target.ndjson';r['stage']=var+'.export';save()
                ex=measure(var,[bin_dir/'leanexport',manifest['endpoint'],'--',manifest['theorem'],*PRIMITIVES],exp)
                r['exports'][var]={'phase':ex};save()
                if ex['exit_code']:raise RuntimeError(ex.get('error_tail','export failed'))
                r['exports'][var].update(export_measurements(exp,manifest['theorem']));exp.unlink();save()
            r.update(status='pass',stage='completed');save()
        except BaseException as exc:
            r.update(status='failed',error=str(exc)[-8000:]);save();raise
if __name__=='__main__':
    main()
