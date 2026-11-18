"""Rebuild the 18-key, proof-sharing experiment from the exact public pure-decoder snapshot."""
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

overlay=Path(__file__).resolve().parent
base=Path(sys.argv[1]).resolve()
expected='71fbc336902e0e680b452ffc4e38390ae6575527de8535f636278863e0a58a31'
manifest=base/'diagnostic/manifest.json'
assert sha256(manifest.read_bytes()).hexdigest()==expected
m=json.loads(manifest.read_text())
spec=m['variants']['replacement']
src=base/'source'
def checked(path):
    content=(base/path).read_bytes()
    assert sha256(content).hexdigest()==m['files'][path]['sha256']
    return content

def put(module,content):
    path='source/'+module+'.lean'
    (base/path).write_bytes(content)
    spec['paths'][module+'.lean']=path
    m['files'][path]={'bytes':len(content),'sha256':sha256(content).hexdigest()}
def encode(module,lines):
    content=('\n'.join(lines)+'\n').encode()
    assert len(lines)<=10000
    put(module,content)

def numbers(raw):
    out=bytearray()
    i=0
    def length(n):
        nonlocal i
        if n!=15:return n
        while True:
            x=raw[i];i+=1;n+=x
            if x!=255:return n
    while i<len(raw):
        h=raw[i];i+=1
        n=length(h>>4)
        assert i+n<=len(raw) and len(out)+n<=16_000_000
        out.extend(raw[i:i+n]);i+=n
        if i==len(raw):break
        off=int.from_bytes(raw[i:i+2],'little');i+=2
        assert 0<off<=len(out)
        n=length(h&15)+4
        assert len(out)+n<=16_000_000
        for _ in range(n):out.append(out[-off])
    pos=0;ns=[]
    while pos<len(out):
        n=int.from_bytes(out[pos:pos+3],'little');pos+=3
        assert pos+n<=len(out)
        ns.append(int.from_bytes(out[pos:pos+n],'little'));pos+=n
    return ns

for module in ['PackedSlot','TupleLiteralSharing','SharedRecord']:
    put(module,(overlay/(module+'.lean')).read_bytes())
root='GraphInputsRow29Part00094Data'
pool_values=numbers(checked(spec['paths']['SmallFacetCells.gpool']))
assert len(pool_values)%7==0
pool={pool_values[j]:tuple(pool_values[j+1:j+7]) for j in range(0,len(pool_values),7)}
fields=numbers(checked(spec['paths'][root+'.gpack']))
assert len(fields)==18*46
records=[];names={}
for i in range(18):
    f=fields[46*i:46*i+46]
    width,embedding=f[31:33]
    cells=[pool[(embedding>>(width*j))&((1<<width)-1)] for j in range(f[0]+1)]
    assert embedding>>(width*len(cells))==0
    records.append(cells)
    for t in cells:
        sig=sha256(','.join(map(str,t)).encode()).hexdigest()[:16]
        names[t]='t'+sig
assert len(set(names.values()))==len(names)
catalogue=['module','prelude','public import TupleLiteralSharing','','@[expose] public section',
    'set_option maxHeartbeats 0','set_option maxRecDepth 100000','namespace Papers.RationalityTen.ResidualBatch.TupleCatalogue',
    'open Papers.RationalityTen.ResidualBatch.TupleSharing','']
for t,n in sorted(names.items(),key=lambda x:x[1]):
    catalogue.extend(['def '+n+' : GraphPureGeometry.Cell := ⟨'+', '.join(map(str,t))+'⟩',
        f'theorem {n}_facts : TupleFacts {n} := tupleFacts_of_check _ (by decide +kernel)',''])
catalogue+=['end Papers.RationalityTen.ResidualBatch.TupleCatalogue']
encode('TupleCatalogue',catalogue)
pilot=['module','prelude','public import SharedRecord','public import TupleCatalogue','public import '+root,'',
    '@[expose] public section','set_option maxHeartbeats 0','set_option maxRecDepth 100000',
    'namespace Papers.RationalityTen.ResidualBatch.TuplePilot','open TupleSharing TupleCatalogue',
    'open Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094','']
for i,cells in enumerate(records):
    n=f'{i:03}';cs=[names[t] for t in cells]
    pilot.append(f'private def cells{n} : List GraphPureGeometry.Cell := ['+', '.join(cs)+']')
    pilot.extend([f'private theorem alignment{n} : PackedAlignment record{n} cells{n} :=',
        '  ⟨rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel,',
        '   by decide +kernel, by decide +kernel⟩'])
    cert='Certified.nil'
    for name in reversed(cs):cert='(Certified.cons '+name+'_facts '+cert+')'
    pilot.extend([f'private theorem cert{n} : Certified cells{n} :=', '  '+cert,
        f'theorem literal{n} : RawGraphSemanticCertificate.LiteralFacts record{n}.data :=',
        f'  literal_of_packed record{n} cells{n} alignment{n} cert{n} (by decide +kernel) (by decide +kernel)',''])
pilot+=['end Papers.RationalityTen.ResidualBatch.TuplePilot']
encode('TuplePilot',pilot)
mod='GraphCompactBlock0528';path=spec['paths'][mod+'.lean'];block=checked(path).decode();original_pure_hash=sha256(block.encode()).hexdigest()
block=block.replace('public import PureGeometryProbe','public import PureGeometryProbe\npublic import TuplePilot')
for i in range(18):
    old=f'private theorem sideVerified{i:02} : Interval sideVerifiedTest {i} {i+1} :=\n  interval_of_check _ {i} 1 (by decide +kernel)'
    new=f'''private theorem sideVerified{i:02} : Interval sideVerifiedTest {i} {i+1} := by
  intro k lo hi
  have key : k = {i} := by omega
  subst k
  exact TupleSharing.side_of_shared (packets (Fin.ofNat 18 {i}))
    TuplePilot.literal{i:03} (by decide +kernel)'''
    assert block.count(old)==1
    block=block.replace(old,new)
put(mod,block.encode())
allmods={rel[:-5].replace('/','.') for rel in spec['paths'] if rel.endswith('.lean')}
imports=re.compile(r'^(?:public )?(?:meta )?import (?:all )?(\S+)\s*$',re.M)
ext=set()
for rel,path in spec['paths'].items():
    if rel.endswith('.lean'):ext.update(set(imports.findall(checked(path).decode()))-allmods)
spec.update(module_count=len(allmods),external_imports=sorted(ext),source_and_data_bytes=sum(m['files'][x]['bytes'] for x in spec['paths'].values()))
# Extend the paired raw/pure data and endpoint rescans with export-format counts.
runner='diagnostic/run.py'
code=checked(runner).decode()
edits=[
    ('    nat_count = 0\n', '    nat_count = 0\n    expr_total = 0\n    expr_kinds = {}\n'),
    ('            digest.update(line)\n', '''            digest.update(line)
            if b'"ie":' in line:
                record = json.loads(line)
                if 'ie' in record:
                    kinds = [k for k in record if k != 'ie']
                    if len(kinds) != 1:
                        raise ValueError(f'Unrecognized expression record keys: {kinds!r}')
                    kind = kinds[0]
                    expr_total += 1
                    expr_kinds[kind] = expr_kinds.get(kind, 0) + 1
'''),
    ("'nat_value_records':nat_count", "'expressions':expr_total,'expression_kinds':expr_kinds,'nat_value_records':nat_count"),
]
for old,new in edits:
    assert code.count(old)==1
    code=code.replace(old,new,1)
binary=code.encode()
(base/runner).write_bytes(binary)
m['files'][runner]={'bytes':len(binary),'sha256':sha256(binary).hexdigest()}
m['tuple_diagnostic']={'input_manifest':expected,'records':len(records),'selected_slots':sum(map(len,records)),'unique_tuples':len(names),'index':root,'original_pure_block_sha256':original_pure_hash,'scope':'18 records of Block 21816 21834; every former sideCheck remains a theorem of the same predicate'}
manifest.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(m['tuple_diagnostic'])
print('generated_manifest_sha256',sha256(manifest.read_bytes()).hexdigest())
