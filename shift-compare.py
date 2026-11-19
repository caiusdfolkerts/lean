"""Compare alternative local instance scopes against one exact proof theorem."""
from pathlib import Path
import json, os, subprocess
root=Path.cwd()
out=root.parent/'shift-check'
out.mkdir()
target='WishartVerification.proportional_shift_product_inequalities'
claims=[target,'TauCeti.Probability.nonsingularWishartMeasure','WishartVerification.shiftedMoment']
(out/'selection.json').write_text(json.dumps({'theorem_names':claims,'definition_names':[]}))
source_mod='wishart.verified.proportionate_shifts01'
def run(args, env=None, log=None):
    print(' '.join(map(str,args)),flush=True)
    if log is None:
        subprocess.run(args,env=env,check=True)
    else:
        with log.open('wb') as f:
            subprocess.run(args,env=env,stdout=f,check=True)
run(['lake','build','+'+source_mod])
prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
env={**os.environ,'LEAN_PATH':str(root)+os.pathsep+paths}
run([prefix/'bin/leanexport',source_mod,'--',*claims],env,out/'source.export')
path=root/'Challenge.lean';original=path.read_text()
anchor='/-- Section 4.1: both inequalities'
pos=original.index(anchor)
end=original.index(':=by sorry',pos)+len(':=by sorry')
group=original.index('/-- Literal shiftedMomentIntegrand') if '/-- Literal shiftedMomentIntegrand' in original else original.index('def shiftedMomentIntegrand')
for arm in ['submitted','theorem','shifted_definitions']:
    modified=original
    if arm!='submitted':
        start=pos if arm=='theorem' else group
        modified=original[:start]+'section\nattribute [local instance 4100] Matrix.instStarModule\n'+original[start:end]+'\nend\n'+original[end:]
    path.write_text(modified)
    run(['lake','env','lean','-j1','-DElab.async=false','-Ddebug.skipKernelTC=false','-o','Challenge.olean','Challenge.lean'],log=out/(arm+'-build.log'))
    run([prefix/'bin/leanexport','Challenge','--',*claims],env,out/'challenge.export')
    run([prefix/'bin/lean','-M4096','--load-dynlib='+str(prefix/'lib/lean/libLake_shared.so'),'--run',
         root.parent/'AuditShift.lean',out/'challenge.export',out/'source.export',out/'selection.json'],log=out/(arm+'-compare.log'))
    for line in (out/(arm+'-compare.log')).read_text().splitlines():
        if line.startswith('{'):
            d=json.loads(line)
            if d.get('kind')=='PRINCIPAL_TYPE_SUMMARY':print(arm,d['name'],d['type_equal'],flush=True)
path.write_text(original)
