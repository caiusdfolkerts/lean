"""Apply exactly the shared proof overlay, then use the previously checked direct-literal RawData module."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

here=Path(__file__).resolve().parent
base=Path(sys.argv[1]).resolve()
subprocess.run([sys.executable,str(here/'prepare_shared.py'),str(base)],check=True)
manifest=base/'diagnostic/manifest.json'
shared_hash=sha256(manifest.read_bytes()).hexdigest()
assert shared_hash=='58fcc7a633ca46595a96c31d5be057b090f1ee1c57aa47096300eeea2f2e6929'
m=json.loads(manifest.read_text());spec=m['variants']['replacement'];files=m['files']
name='GraphInputsRow29Part00094Data.lean'
direct=(here/'control'/name).read_bytes()
assert sha256(direct).hexdigest()=='9a3965938ee4bf89a8f48b69d23b97a900cc7ed1e1e6350162baf3ca3414683d'
def setfile(name,data):
    path=spec['paths'][name]
    assert sha256((base/path).read_bytes()).hexdigest()==files[path]['sha256']
    (base/path).write_bytes(data)
    files[path]={'bytes':len(data),'sha256':sha256(data).hexdigest()}
setfile(name,direct)
probe_name='PureGeometryProbe.lean'
probe=(base/spec['paths'][probe_name]).read_text()
assert probe.count('public meta import GeometricRecordFiles')==1
probe=probe.replace('public meta import GeometricRecordFiles','public import GraphPureGeometry\npublic meta import PureGeometricRecordFiles\npublic meta import GeometricRecordFiles')
insertion='\n'.join(f'def pure{i:03} : RawData := pureSmallRecord% {i}' for i in range(18))
probe=probe.replace('def originals : List RawData',insertion+'\ndef originals : List RawData',1)
for i in range(18):
    old=f'Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record{i:03}'
    assert probe.count(old)==2
    probe=probe.replace(old,f'pure{i:03}')
assert probe.count('pureSmallRecord%')==18 and probe.count('smallFacetRecord%')==18
setfile(probe_name,probe.encode())
spec['source_and_data_bytes']=sum(files[p]['bytes'] for p in spec['paths'].values())
m['tuple_diagnostic']['control']={'shared_manifest_sha256':shared_hash,
    'direct_literal_source_commit':'fbc597f853dcbc93f434da436617faa7ffe5ed1f',
    'direct_literal_source_sha256':sha256(direct).hexdigest(),
    'endpoint_data':'direct-literal RawData',
    'parity_data':'18 direct originals compared to independently pure-decoded values on the same .gpack and .gpool',
    'mathematical_proof_diff':'Identical packed alignment, tuple facts and vertex matrix transport; only RawData representation changes.'}
manifest.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print('control_manifest_sha256',sha256(manifest.read_bytes()).hexdigest())
