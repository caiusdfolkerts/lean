"""Share the exact initial clauses between geometric proof construction and RUP replay."""
from pathlib import Path
import hashlib,json,re,sys
base,out=map(Path,sys.argv[1:3]);out.mkdir(exist_ok=False,parents=True)
def replace_one(s,old,new):
 if s.count(old)!=1: raise ValueError(old)
 return s.replace(old,new)
rup=(base/'RupProofTerm.lean').read_text()
a=rup.index('def mkRefutation (cnf');b=rup.index('  let steps ← match parseLrat',a)
old=rup[a:b]
rup=rup[:a]+'''def mkRefutationFromClauses (initial : Array Clause) (lrat : String)
    (inlineSteps : Bool := true) : MetaM Expr := do
  let started ← IO.monoMsNow
'''+rup[b:]
wrapper=old[:old.index('  let started')]+old[old.index('  let initial'):]+'''  mkRefutationFromClauses initial lrat inlineSteps

'''
rup=replace_one(rup,'syntax (name := rupProof)',wrapper+'syntax (name := rupProof)')
(out/'RupProofTerm.lean').write_text(rup)
sat=(base/'FacetSatInitials.lean').read_text()
sat=replace_one(sat,'runRefutation (namespaceText manifestText cnf lrat : String)','runRefutation (namespaceText manifestText lrat : String) (cnf : Option String)')
sat=replace_one(sat,'let refutation ← RupProofTerm.mkRefutation cnf lrat','''let refutation ← match cnf with
      | some text => RupProofTerm.mkRefutation text lrat
      | none => RupProofTerm.mkRefutationFromClauses clauses lrat''')
sat=replace_one(sat,'runRefutation namespaceText manifestText cnf lrat)','runRefutation namespaceText manifestText lrat (some cnf))')
end='end Papers.RationalityTen.FacetSatInitials'
sat=replace_one(sat,end,'''/-- Use the validated manifest clauses for geometric hypotheses and the RUP proof. -/
syntax (name := facetRefutationShared) "facet_refute_shared% " str str str : command

@[command_elab facetRefutationShared] def elabFacetRefutationShared : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some manifestText := stx[2].isStrLit? | throwUnsupportedSyntax
  let some lrat := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM (runRefutation namespaceText manifestText lrat none)

'''+end)
(out/'FacetSatInitials.lean').write_text(sat)
quoted=r'"(?:[^"\\]|\\.)*"'
command=re.compile(r'(?m)^facet_refute% ('+quoted+r') ('+quoted+r')\n  ('+quoted+r')\n  ('+quoted+r')')
seen=set();entries=0;saved=0;files=0
def share(m):
 global entries
 ns,manifest,dimacs,lrat=map(json.loads,m.groups()); obj=json.loads(manifest)
 assert ns==obj['namespace'] and ns not in seen and lrat
 lines=dimacs.splitlines();header=lines[0].split()
 assert header==['p','cnf',str(len(obj['atoms'])),str(len(obj['clauses']))]
 rows=[list(map(int,row.split())) for row in lines[1:]]
 assert all(row and row[-1]==0 and 0 not in row[:-1] for row in rows)
 assert [row[:-1] for row in rows]==obj['clauses']
 seen.add(ns);entries+=len(rows)
 return 'facet_refute_shared% '+m[1]+' '+m[2]+'\n  '+m[4]
for path in sorted(base.glob('*Structural*.lean')):
 s=path.read_text();t,n=command.subn(share,s)
 assert n==s.count('\nfacet_refute% '),path
 if n:
  (out/path.name).write_text(t)
  saved+=len(s.encode())-len(t.encode());files+=1
assert len(seen)==1937
print(json.dumps(dict(verified_manifests=len(seen),clause_rows=entries,files=files,bytes_saved=saved)))
