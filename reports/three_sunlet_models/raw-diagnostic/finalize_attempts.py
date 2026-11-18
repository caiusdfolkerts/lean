#!/usr/bin/env python3
from pathlib import Path
import argparse,json,os,sys
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);o=p.parse_args();o.output.mkdir(parents=True,exist_ok=True)
records=[];steps=json.loads(os.getenv('DIAGNOSTIC_STEPS','{}'))
for memory,step in [(4096,'initial'),(8192,'fallback')]:
 f=o.output/f'attempt-{memory}'/'receipt.json'
 if f.exists():
  d=json.loads(f.read_text())
  if d['status']=='running':d['status']='diagnostic-interrupted'
 elif step=='initial' or steps.get(step,{}).get('outcome') not in [None,'skipped']:
  f.parent.mkdir(parents=True,exist_ok=True);d={'kind':'raw ConstantInfo diagnostic; NOT full preflight','status':'diagnostic-not-started','lean_memory_mib':memory}
 else:continue
 d['workflow_steps']=steps;f.write_text(json.dumps(d,indent=2)+'\n');records.append({'memory_mib':memory,'status':d['status'],'receipt':str(f.relative_to(o.output))})
okay=any(x['status']=='raw-diagnostic-elaborated' for x in records)
(o.output/'summary.json').write_text(json.dumps({'kind':'raw ConstantInfo diagnostic; NOT full preflight','status':'diagnostic-elaborated' if okay else 'diagnostic-incomplete','resource_only_retry':True,'attempts':records},indent=2)+'\n')
sys.exit(0 if okay else 1)
