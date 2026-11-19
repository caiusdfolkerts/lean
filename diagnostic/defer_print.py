"""For timing only, remove repetitive console queries while retaining proof declarations."""
from pathlib import Path
import re,sys,collections,json
p=Path(sys.argv[1])
counts=collections.Counter()
for path in p.rglob('*.lean'):
 if '.lake' in path.parts:continue
 text=path.read_text()
 cleaned,n=re.subn(r"(?m)^#print axioms [\w.']+\r?\n",'',text)
 counts['literal_commands']+=n
 if path.name=='GraphCases.lean':
  line='  let auditCmd ← `(command| #print axioms $result)\n'
  arr='#[coreCmd,parametersCmd,coverageCmd,resultCmd,auditCmd]'
  assert cleaned.count(line)==cleaned.count(arr)==1
  cleaned=cleaned.replace(line,'').replace(arr,arr.replace(',auditCmd',''))
 if path.name=='GraphNodes.lean':
  line='    commands := commands.push (← `(command| #print axioms $finalId))\n'
  assert cleaned.count(line)==1
  cleaned=cleaned.replace(line,'')
 if cleaned!=text:
  path.write_text(cleaned)
  counts['changed_files']+=1
print(json.dumps(counts))
