"""Give empty structural branches a direct geometric contradiction."""
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
def change(file, old, new, count=1):
    path = root / file
    body = path.read_text()
    if body.count(old) != count:
        raise ValueError(f"{file}: expected {count} occurrences of {old[:50]}")
    path.write_text(body.replace(old, new))

anchor = 'end Papers.RationalityTen.GraphCaseCertificate'
change('GraphDirectCore.lean', anchor, '''/-- A checked contradiction excludes the actual boundary before any leaf relabeling. -/
structure BoundaryEvidence (D : RawData) : Prop where
  matrix : MatrixGraphProblem.Checked D.data
  valid : GraphGrowthInputs.Valid D.inputs
  literal : RawGraphSemanticCertificate.LiteralFacts D.data
  disposition : DirectCore D ∨ ∀ B : List (Fin D.n),
    GraphGrowthConstraints.Target (D.inputs.problem valid) B → False

theorem BoundaryEvidence.ofDirect {D : RawData} (C : DirectCore D) : BoundaryEvidence D :=
  ⟨C.matrix, C.valid, C.literal, Or.inl C⟩

''' + anchor)
change('GraphCaseCertificate.lean', '∃ D : RawData, DirectCore D ∧', '∃ D : RawData, BoundaryEvidence D ∧', 2)
geometry='GraphDirectCoverage.lean'
body=(root/geometry).read_text()
literal = body[body.index('theorem literal ('):body.index('theorem exists_frame')]
terminal=body[body.index('theorem hasTerminal ('):body.index(' := by\n  apply GraphFamilyClosure.hasTerminal_of_encoding')+len(' := by\n')]
new = literal.replace('theorem literal (','theorem literalOfEvidence (').replace('C : DirectCore D','C : BoundaryEvidence D')
new += terminal.replace('theorem hasTerminal (','theorem hasTerminalOfEvidence (').replace('C : DirectCore D','C : BoundaryEvidence D')
new += '''  rcases C.disposition with core | excluded
  · exact hasTerminal P hP hnonsimple D core hwell lab E htarget hquota
  · exact (excluded E.family.toList htarget).elim

'''
marker='end Papers.RationalityTen.DirectGraphGeometry'
change(geometry,marker,new+marker)
change(geometry,'have HL := DirectGraphGeometry.literal D C','have HL := DirectGraphGeometry.literalOfEvidence D C',2)
change(geometry,'apply DirectGraphGeometry.hasTerminal P','apply DirectGraphGeometry.hasTerminalOfEvidence P',2)
counts = {'clique':0,'empty_sat':0,'nonempty_sat':0}
for path in sorted(root.glob('GraphInputs*Structural*.lean')):
    original = path.read_text()
    def adapt(match):
        block=match[0]
        position=block.index('theorem direct_core :')
        prefix, constructor=block[:position],block[position:]
        signature, fields=constructor.split(' where\n',1)
        if 'theorem local_excluded ' in prefix:
            route='fun B H => local_excluded _ _ B H'
            counts['clique']+=1
        elif 'def leafCount : Nat := 0\n' in prefix:
            route='fun B H => by\n    obtain ⟨j, _⟩ := local_coverage _ _ B H\n    exact Fin.elim0 j'
            counts['empty_sat']+=1
            prefix=prefix[:prefix.index('def originalLeaf ')]
        else:
            counts['nonempty_sat']+=1
            return block.replace('theorem direct_core :','theorem direct_core :',1)
        valid=re.search(r'^  valid := (.+)$',fields,re.M)[1]
        matrix=re.search(r'^  matrix := (.+)$',fields,re.M)[1]
        route=route.replace('_ _ B H',f'{valid} {matrix} B H')
        return prefix+signature.replace('DirectCore','BoundaryEvidence')+' where\n'+fields[:fields.index('  leaf_nodup :=')]+'  disposition := Or.inr ('+route+')\n'
    pattern=r'(?ms)^namespace Papers\.RationalityTen\.StructuralGraphCases\.\S+\n.*?(?=^end Papers\.RationalityTen\.StructuralGraphCases\.)'
    final=re.sub(pattern,adapt,original)
    # Nonempty orbit lists retain their checked DirectCore and its frames.
    for ns in re.findall(r'^namespace (Papers\.RationalityTen\.StructuralGraphCases\.\S+)$', final,re.M):
        part=final.split('namespace '+ns+'\n',1)[1].split('\nend '+ns,1)[0]
        if re.search(r'theorem direct_core : (?:GraphCaseCertificate\.)?DirectCore ',part):
            pattern2=r'(theorem direct_core : (?:GraphCaseCertificate\.)?)DirectCore (.+?) where\n'
            altered,n=re.subn(pattern2,r'\1BoundaryEvidence \2 := GraphCaseCertificate.BoundaryEvidence.ofDirect (D := \2) {\n',part,count=1)
            if n!=1: raise ValueError(ns)
            altered=altered.rstrip()+'\n}\n'
            final=final.replace(part,altered,1)
    if final!=original: path.write_text(final)
assert counts=={'clique':811,'empty_sat':1778,'nonempty_sat':159},counts
print(counts)
