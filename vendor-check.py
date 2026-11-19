from pathlib import Path
import json,os,subprocess
p=Path.cwd()
out=p.parent/'vendor-check';out.mkdir()
c=json.loads((p/'comparator.json').read_text())
names=[n for n in c['theorem_names']+c['definition_names'] if n.startswith(('TauCeti.','Matrix.','Quaternion.','selfAdjoint.'))]
assert len(set(names))==len(names) and len(names)>=12
mods=['TauCeti.Probability.Distributions.Wishart.Inverse.Basic','TauCeti.Probability.Distributions.Wishart.Basic','TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence','TauCeti.Algebra.Quaternion.ComplexMatrix']
(o:=p/'VendorOriginal.lean').write_text('module\n'+''.join('public import '+m+'\n' for m in mods))
def run(args,env=None,log=None):
 print(' '.join(map(str,args)),flush=True)
 if log is None:subprocess.run(args,check=True,env=env)
 else:
  with log.open('wb') as f:subprocess.run(args,stdout=f,check=True,env=env)
run(['lake','build',*['+'+m for m in mods]])
for m in ['VendorOriginal','Challenge']:
 run(['lake','env','lean','-j1','-DElab.async=false','-Ddebug.skipKernelTC=false','-o',m+'.olean',m+'.lean'],log=out/(m+'.log'))
prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
env={**os.environ,'LEAN_PATH':str(p)+os.pathsep+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()}
for m in ['VendorOriginal','Challenge']:
 run([prefix/'bin/leanexport',m,'--',*names],env,out/(m+'.export'))
(out/'choice.json').write_text(json.dumps({'theorem_names':names,'definition_names':[]}))
run([prefix/'bin/lean','-M4096','--load-dynlib='+str(prefix/'lib/lean/libLake_shared.so'),'--run',p.parent/'AuditShift.lean',out/'Challenge.export',out/'VendorOriginal.export',out/'choice.json'],log=out/'comparison.log')
mismatch=[]
for line in (out/'comparison.log').read_text().splitlines():
 if line.startswith('{'):
  d=json.loads(line)
  if d['kind']=='PRINCIPAL_TYPE_SUMMARY' and not d['type_equal']:mismatch.append(d['name'])
print('Mismatched exact types',mismatch,flush=True)
