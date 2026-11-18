"""Verify the three-block source closure and measure all exports for later independent replay."""
import argparse
import concurrent.futures
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE_MANIFEST = ROOT / 'diagnostic/manifest.json'
IMPORT = re.compile(r'^(?:public )?(?:meta )?import (?:all )?(\S+)\s*$', re.M)
DECL = re.compile(rb'^\{"(axiom|def|opaque|thm|quot|inductive)":')
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
# Kernel primitives used by Lake's v4.35 comparator. Include identical targets in both exports.
PRIMITIVES = 'Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam'.split()


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def source_graph(m, variant):
    spec = m['variants'][variant]
    paths = spec['paths']
    modules = {name[:-5].replace('/', '.'): local for name,local in paths.items() if name.endswith('.lean')}
    fixed = [p for p in m['files'] if not p.startswith(('source/','original-source/'))]
    for src in [*paths.values(), *fixed]:
        desc = m['files'][src]
        path = ROOT/src
        if path.stat().st_size != desc['bytes'] or sha(path) != desc['sha256']:
            raise ValueError(f'Incorrect source snapshot: {src}')
    assert (ROOT/'lean-toolchain').read_text().strip() == m['lean_toolchain']
    locked = json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    assert next(item['rev'] for item in locked if item['name']=='mathlib') == m['mathlib_commit']
    graph = {}
    external = set()
    for name,src in modules.items():
        deps = IMPORT.findall((ROOT/src).read_text())
        graph[name] = [n for n in deps if n in modules]
        external.update(set(deps)-modules.keys())
    reached = set()
    todo = [m['endpoint_module']]
    while todo:
        name = todo.pop()
        if name not in reached:
            reached.add(name)
            todo.extend(graph[name])
    if reached != set(graph) or sorted(external) != spec['external_imports']:
        raise ValueError('Source closure differs from the snapshot manifest')
    if any(name.split('.')[0] not in {'Init','Lean','Std'} for name in external):
        raise ValueError('An external import needs a separate dependency build')
    if variant == 'original':
        assert len(spec['upstream_modules']) == len(graph)
        for name,origin in spec['upstream_modules'].items():
            assert origin['original_sha256'] == m['files'][modules[name]]['sha256']
    list(graphlib.TopologicalSorter(graph).static_order())
    return graph


def export_measurements(path, target):
    pieces = target.split('.')
    prefixes = {'.'.join(pieces[:n]) for n in range(1,len(pieces)+1)}
    prefixes.update(part for full in AXIOMS for part in [full,full.partition('.')[0]])
    names = {0:''}
    declarations = {}
    axioms = []
    found = False
    nat_count = 0
    nat_digits = 0
    digest = hashlib.sha256()
    with path.open('rb') as f:
        for line in f:
            digest.update(line)
            numeral = re.search(rb'"natVal"\s*:\s*"([0-9]+)"',line)
            if numeral:
                nat_count += 1
                nat_digits += numeral.end(1) - numeral.start(1)
            if b'"in":' in line[:128]:
                rec = json.loads(line)
                nm = rec.get('str')
                if 'in' in rec and isinstance(nm, dict) and nm['pre'] in names:
                    full = '.'.join(filter(None,[names[nm['pre']],nm['str']]))
                    if full in prefixes:
                        names[rec['in']] = full
            match = DECL.match(line)
            if not match:
                continue
            kind = match[1].decode()
            if kind == 'inductive':
                d = json.loads(line)[kind]
                for k in ['types','ctors','recs']:
                    declarations[k] = declarations.get(k,0) + len(d[k])
            else:
                declarations[kind] = declarations.get(kind,0) + 1
                if kind in ['thm','axiom']:
                    name_id = json.loads(line)[kind]['name']
                    if kind == 'axiom':
                        axioms.append(names.get(name_id, f'unknown-name-{name_id}'))
                    elif names.get(name_id) == target:
                        found = True
    if not found or set(axioms)-set(AXIOMS):
        raise ValueError(f'Unexpected export theorem or axioms: found={found}, axioms={axioms}')
    return {'bytes':path.stat().st_size,'sha256':digest.hexdigest(),'target_theorem_confirmed':found,
            'nat_value_records':nat_count,'nat_decimal_bytes':nat_digits,'declarations':sum(declarations.values()),'declaration_kinds':declarations,'axioms':axioms}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('variant',choices=['replacement'])
    ap.add_argument('--run',action='store_true')
    args = ap.parse_args()
    m = json.loads(SOURCE_MANIFEST.read_text())
    graph = source_graph(m,args.variant)
    print(f'{args.variant}: {len(graph)} reachable local sources, exact input hashes confirmed',flush=True)
    if not args.run:
        return
    if sys.platform != 'linux':
        raise SystemExit('The measurement command requires Linux GNU time')
    variant = args.variant
    endpoint = m['endpoint_module']
    target = m['endpoint_theorem']
    results = ROOT/'diagnostic-results'
    results.mkdir(exist_ok=True)
    receipt = results/(variant+'.json')
    report = {'variant':variant,'commit':os.getenv('GITHUB_SHA'),'run_id':os.getenv('GITHUB_RUN_ID'),
              'run_attempt':os.getenv('GITHUB_RUN_ATTEMPT'),'target':target,'module':endpoint,
              'manifest_sha256':sha(SOURCE_MANIFEST),'stage':'setup','status':'running','phases':{},'modules':{}}
    def save():
        temp = receipt.with_suffix('.tmp')
        body = (json.dumps(report,indent=2,sort_keys=True)+'\n').encode()
        if len(body) > 1_048_576:
            raise ValueError('Diagnostic receipt exceeded 1 MiB')
        temp.write_bytes(body)
        temp.replace(receipt)
    save()
    try:
        with tempfile.TemporaryDirectory(prefix='small-0528-',dir=os.getenv('RUNNER_TEMP')) as tempdir:
            scratch = Path(tempdir)
            src = scratch/'source'; build = scratch/'build'; logs=scratch/'logs'
            for p in [src,build,logs]: p.mkdir()
            for rel,physical in m['variants'][variant]['paths'].items():
                dest=src/rel;dest.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(ROOT/physical,dest)
            prefix = Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,text=True).strip())
            bin_dir=prefix/'bin'
            env = dict(os.environ,LEAN_PATH=str(build),PATH=str(bin_dir)+os.pathsep+os.environ['PATH'])
            version=subprocess.check_output([str(bin_dir/'lean'),'--version'],text=True,env=env).strip()
            if not re.search(r'\bversion 4\.35\.0\b',version):raise RuntimeError('Incorrect compiler: '+version)
            report.update({'lean_version':version,'pinned_mathlib':m['mathlib_commit'],'tools':{
                t:sha(bin_dir/t) for t in ['lean','leanexport','leanchecker','nanoda_bin','con-ron']},
                'workers':3,'cpu_affinity':len(os.sched_getaffinity(0)),
                'runner_memory':Path('/proc/meminfo').read_text().splitlines()[0],
                'free_workspace_bytes_at_start':shutil.disk_usage(scratch).free})
            def measure(label,command,export=None):
                metrics=logs/(label+'.time');console=logs/(label+'.log')
                # GNU time is outside all Lean tools. An export's stdout is its immutable proof payload.
                cmd=['/usr/bin/time','-f','%e %U %S %M','-o',str(metrics),*map(str,command)]
                start=time.monotonic()
                with console.open('wb') as log:
                    if export is None:
                        proc=subprocess.run(cmd,env=env,cwd=src,stdout=log,stderr=subprocess.STDOUT)
                    else:
                        with export.open('wb') as stream:
                            proc=subprocess.run(cmd,env=env,cwd=src,stdout=stream,stderr=log)
                out={'exit_code':proc.returncode,'wall_seconds':round(time.monotonic()-start,3)}
                if metrics.exists() and metrics.read_text().splitlines():
                    fields=metrics.read_text().splitlines()[-1].split()
                    if len(fields)==4:
                        out.update(user_seconds=float(fields[1]),system_seconds=float(fields[2]),peak_rss_bytes=int(fields[3])*1024)
                if proc.returncode:
                    with console.open('rb') as log:
                        log.seek(max(0,console.stat().st_size-12000));out['error_tail']=log.read().decode(errors='replace')
                console.unlink(missing_ok=True)
                return out
            report['stage']='build';save();dag=graphlib.TopologicalSorter(graph);dag.prepare()
            ready=list(dag.get_ready());running={};started=time.monotonic();failed=[]
            def build_module(name):
                rel=Path(*name.split('.'));output=build/rel.with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
                argv=[bin_dir/'lean','-t1','-j1','-s65536','-M4096','-DmaxHeartbeats=0','-DElab.async=false','-Ddebug.skipKernelTC=false','-o',output,rel.with_suffix('.lean')]
                result=measure(name,argv)
                if result['exit_code']==0:result['olean_bytes']=output.stat().st_size
                return result
            with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
                while (ready or running) and len(failed) < 8:
                    while ready and len(running)<3:
                        n=ready.pop();running[pool.submit(build_module,n)]=n
                    done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
                    for job in done:
                        n=running.pop(job);res=job.result();report['modules'][n]=res
                        if res['exit_code']:
                            print(n,res.get('error_tail',''),flush=True);failed.append(n)
                        else:
                            if n == 'PureGeometryProbe':
                                report['data_exports'] = {}
                                for tag in ['rawPayload', 'purePayload']:
                                    goal = 'PureGeometryProbe.' + tag
                                    dest = scratch/(tag+'.ndjson')
                                    result = measure(tag,[bin_dir/'leanexport',n,'--',goal,*PRIMITIVES],dest)
                                    report['phases'][tag]=result;save()
                                    if result['exit_code']:
                                        raise RuntimeError('Data export failed: '+str(result))
                                    report['data_exports'][tag] = export_measurements(dest,goal)
                                    dest.unlink()
                                save()
                            dag.done(n)
                    ready.extend(dag.get_ready());save()
                    if len(report['modules'])%25<2:print('Built',len(report['modules']),'of',len(graph),flush=True)
            report['phases']['build']={'wall_seconds':round(time.monotonic()-started,3),'completed_module_count':len(report['modules']),'failed_modules':sorted(failed)}
            if failed or len(report['modules'])!=len(graph):raise ValueError('Module compilation failed')
            scopes = m['measurement_scopes']
            audit = src/'DiagnosticEndpoint.lean'
            audit.write_text('module\nimport '+endpoint+'\n'+'\n'.join(
                'example : '+entry['type']+' := '+entry['theorem'] for entry in scopes if entry.get('type'))+'\n')
            check=measure('endpoint_type',[bin_dir/'lean','-t1','-j1','-M4096',
                                          '-Ddebug.skipKernelTC=false',audit.name])
            report['phases']['endpoint_type']=check
            if check['exit_code']:
                raise RuntimeError('Endpoint type audit failed: '+check.get('error_tail',''))
            report['exports']={}
            for entry in scopes:
                name=entry['label']
                report['stage']='export_'+name;save()
                # The joint proof persists on the ephemeral runner across the three separate checker steps.
                dest=(Path(os.environ['RUNNER_TEMP'])/'graph-family.ndjson' if name=='joint'
                      else scratch/(name+'.ndjson'))
                measured=measure('export_'+name,[bin_dir/'leanexport',entry['module'],'--',
                                                 entry['theorem'],*PRIMITIVES],dest)
                report['phases']['export_'+name]=measured;save()
                if measured['exit_code']:
                    raise RuntimeError('Export '+name+' failed: '+measured.get('error_tail',''))
                report['exports'][name]=export_measurements(dest,entry['theorem']);save()
                if name!='joint': dest.unlink()
            report.update(status='exported',stage='ready_for_independent_replay');save()
    except BaseException as e:
        report['status']='failed';report['error']=str(e)[-12000:];save();raise

if __name__=='__main__':
    main()
