#!/usr/bin/env python3
"""Mark interrupted/not-started diagnostics without ever manufacturing success."""
from pathlib import Path
import argparse,json,os
p=argparse.ArgumentParser();p.add_argument('--cases',type=Path,required=True);p.add_argument('--case',required=True);p.add_argument('--output',type=Path,required=True);o=p.parse_args();o.output.mkdir(parents=True,exist_ok=True);f=o.output/'receipt.json'
if f.exists():d=json.loads(f.read_text())
else:
 c=next(x for x in json.loads(o.cases.read_text())['cases'] if x['id']==o.case)
 d={'schema_version':1,'kind':'Challenge-only elaboration diagnostic; NOT full preflight','case':o.case,'input_hashes':c['hashes'],'lean_toolchain':c['lean_toolchain'],'status':'diagnostic-not-started','source_commit':os.getenv('GITHUB_SHA'),'source_repository':os.getenv('GITHUB_REPOSITORY'),'meaning':'No Lean elaboration result exists; no Solution/Comparator/registry authorization is claimed.'}
if d.get('status')=='running':d['status']='diagnostic-interrupted'
steps=json.loads(os.getenv('DIAGNOSTIC_STEPS','{}'));d['workflow_steps']={k:{'outcome':v.get('outcome'),'conclusion':v.get('conclusion')} for k,v in steps.items() if isinstance(v,dict)}
f.write_text(json.dumps(d,indent=2)+'\n')
