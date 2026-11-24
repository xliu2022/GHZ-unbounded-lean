#!/usr/bin/env python3
"""Generate proof composition, never an unchecked axiom or native reduction."""
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
data=json.loads((R/'scripts/periodic_config_data.json').read_text())
def fs(chosen):
 return '{'+', '.join(map(str,reversed(chosen)))+'}' if chosen else '∅'
def lst(start,N):return '['+', '.join(map(str,range(start,N)))+']'
for name in ['eleven','ten']:
 ns=name.capitalize();rows=data[name]['edges'];N=len(rows)
 source=(R/f'RigidGHZ/Supplement/Periodic/{ns}.lean').read_text()
 prefix=source[:source.index('set_option maxRecDepth 100000 in\n theorem finite_certificate')]
 (R/f'RigidGHZ/Supplement/Periodic/{ns}Data.lean').write_text(prefix+'\nend RigidGHZ.Supplement.Periodic.'+ns+'\n')
 states=[]
 def visit(start,chosen,loc,out):
  for i in range(start,N):
   e,o=rows[i];l=e^o
   if not(loc&l or out&o): visit(i+1,chosen+[i],loc|l,out|o)
  states.append((start,chosen,loc,out))
 visit(0,[],0,0)
 ids={tuple(c):i for i,(k,c,l,o) in enumerate(states)}
 blocks=[]
 for idx,(start,chosen,loc,out) in enumerate(states):
  text=f'''private theorem node_{idx} :
    (scheme.enumerateFrom {lst(start,N)} {fs(chosen)}).all
      (fun A => decide (Certificate A)) = true := by
'''
  # Include branch uses an already checked theorem; skip branch continues.
  depth=2
  for k in range(start,N):
   e,o=rows[k];l=e^o; indent=' '*depth
   if not(loc&l or out&o):
    text+=indent+'apply scheme.check_enumeration_split _ _ _ Certificate (by decide)\n'
    text+=indent+f'  ?_ node_{ids[tuple(chosen+[k])]}\n'
   else:
    text+=indent+'apply scheme.check_enumeration_skip _ _ _ Certificate (by decide)\n'
  text+=' '*depth+'decide\n\n'
  blocks.append(text)
 # Keep 32 state declarations per module so kernel memory is bounded.
 chunks=[]
 for lo in range(0,len(blocks),32):
  num=len(chunks);mod=f'{ns}Check{num:02}'
  importmod=chunks[-1] if chunks else ns+'Data'
  code='module\n\npublic import RigidGHZ.Supplement.Periodic.'+importmod+'\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\nnamespace RigidGHZ.Supplement.Periodic.'+ns+'\n\n'
  # Cross-module node references must be public names.
  code+=''.join(blocks[lo:lo+32]).replace('private theorem','theorem')
  code+='end RigidGHZ.Supplement.Periodic.'+ns+'\n'
  (R/f'RigidGHZ/Supplement/Periodic/{mod}.lean').write_text(code)
  chunks.append(mod)
 suffix=source[source.index('theorem certificate {'):]
 final='module\n\npublic import RigidGHZ.Supplement.Periodic.'+chunks[-1]+'\n\n@[expose] public section\n\nnamespace RigidGHZ.Supplement.Periodic.'+ns+'\n\n'
 final+=f'''theorem finite_certificate :
    (scheme.enumerateFrom (List.finRange {N}) ∅).all (fun A => decide (Certificate A)) = true := by
  exact node_{len(states)-1}

'''+suffix
 (R/f'RigidGHZ/Supplement/Periodic/{ns}.lean').write_text(final)
 print(name,len(states),'states,',len(chunks),'modules')
