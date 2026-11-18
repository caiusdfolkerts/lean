#!/usr/bin/env python3
"""Snapshot explicitly supplied Challenge versions; does not elaborate or publish."""
from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parents[2];R=Path(__file__).resolve().parent
specs=[
 ('deformed_coinvariants','source/Challenge.lean','8e76d7765c61c614c3d003fd59bd2c3385a835bf8e351aca4f06a70e119bb20c'),
 ('alternating_forms','source/Challenge.lean','94d01dd1e17740e202beee4adcaba6d95612956e10abaf45db74798d7cdb0dd8'),
 ('barycentric_invariance','source/Challenge.lean','f516df0e2a21d8a6e19d12cfd1cee2d8e0f62733a267051010a4e2497ac2e589'),
 ('barycentric_invariance_relative','source/Challenge.lean','79f98e841903912fd4fd52fa05e85e4fa199ecf8267023ea8755aa75aa0280d2'),
 ('higher_specht_bases','source/Challenge.lean','cf5e4afd1fcf2fb43a2ac9a2a5b897caef3b7fe046597b2553ca0a55ab6de90e'),
 ('singular_vector_spans','Challenge.lean','291f45713e842e27af9762c6f57dbc3e30866fe7b5ae5b1818e985e194e212c4'),
 ('three_sunlet_models','Challenge.lean','7bda1d65fd4a9b1050d145761af8ed8daba12f49aec62ba8f15325680e9219c9')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cases=[]
for project,relative,expected in specs:
 p=B/'packages'/project;source=p/relative
 if sha(source)!=expected:raise SystemExit(f'{project}: Challenge changed since owner supplied snapshot; refusing snapshot')
 dst=R/'cases'/project;dst.mkdir(exist_ok=True)
 config=next(x for x in [p/'lakefile.toml',p/'lakefile.lean'] if x.is_file())
 for filename,src in [('Challenge.lean',source),('lean-toolchain',p/'lean-toolchain'),('lake-manifest.json',p/'lake-manifest.json'),('original-'+config.name+('.txt' if config.suffix=='.lean' else ''),config)]:shutil.copyfile(src,dst/filename)
 manifest=json.loads((dst/'lake-manifest.json').read_text());case={'id':project,'module':'Challenge','case_dir':f'cases/{project}','original_package':f'packages/{project}','original_challenge':f'packages/{project}/{relative}','lean_toolchain':(dst/'lean-toolchain').read_text().strip(),'hashes':{f.name:sha(f) for f in dst.iterdir() if f.is_file()},'challenge_lines':len(source.read_text().splitlines()),'challenge_bytes':source.stat().st_size,'dependency_pins':[{'name':x['name'],'url':x.get('url'),'rev':x.get('rev')} for x in manifest['packages']]};cases.append(case)
(R/'cases.json').write_text(json.dumps({'schema_version':1,'kind':'Challenge-only elaboration diagnostic; not full preflight','pipeline_commit':'14aa8d6b3c2f14a8540605e37144560b9a00e7e7','cases':cases,'default_case_ids':[x['id'] for x in cases if x['id']!='higher_specht_bases']},indent=2)+'\n')
print('Snapshotted',len(cases),'exact Challenges;',sum(x['challenge_bytes'] for x in cases),'Lean source bytes')
