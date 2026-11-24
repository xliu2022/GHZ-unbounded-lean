#!/usr/bin/env python3
"""Numerical state maps, certified on short lists by the Lean kernel."""
import json,re
from pathlib import Path
P=Path(__file__).resolve().parents[1];B=P/'RigidGHZ/Supplement/Periodic'
s=(B/'ElevenCatalogueData.lean').read_text().split('def catalogueList')[1].split(':=')[1].split('\nend ')[0]
C=[[int(x) for x in a.split(',')]for a in re.findall(r'\{([0-9, ]+)\}',s)]
E=json.loads((P/'scripts/periodic_config_data.json').read_text())['eleven']['edges']
def pair(A):
 L=O=0
 for i in A:
  e,o=E[i];L|=e^o;O|=o
 return (511^L,O)
def fs(A):return '{'+', '.join(map(str,A))+'}'if A else'∅'
def cfgs(C):return '['+', '.join(map(fs,C))+']'
def pairs(C):return '['+', '.join('('+str(pair(A)[0])+', '+str(pair(A)[1])+')'for A in C)+']'
chunks=[C[i:i+56]for i in range(0,len(C),56)]
head='module\n\npublic import RigidGHZ.Supplement.Periodic.ElevenCatalogue\npublic import RigidGHZ.Supplement.Periodic.SmallCodes\n\n@[expose] public section\n\nset_option maxRecDepth 100000\n\nnamespace RigidGHZ.Supplement.Periodic.Eleven\n\n'
text=head
for j,c in enumerate(chunks):
 text+=f'def configurationChunk{j:02d} : List (Finset (Fin 33)) :=\n  {cfgs(c)}\n\n'
 text+=f'def pairCodeChunk{j:02d} : List (ℕ × ℕ) :=\n  {pairs(c)}\n\n'
concat=' ++ '.join(f'configurationChunk{j:02d}'for j in range(len(chunks)))
text+=f'theorem catalogue_chunk_decomposition : catalogueList = {concat} := by rfl\n\n'
text+='def cataloguePairCodes : List (ℕ × ℕ) :=\n  '+' ++ '.join(f'pairCodeChunk{j:02d}'for j in range(len(chunks)))+'\n\n'
text+='end RigidGHZ.Supplement.Periodic.Eleven\n';(B/'ElevenCodeData.lean').write_text(text)
for j in range(len(chunks)):
 imp='RigidGHZ.Supplement.Periodic.ElevenCodeData'if j==0 else f'RigidGHZ.Supplement.Periodic.ElevenCodeCheck{j-1:02d}'
 text=f'''module

public import {imp}

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem pair_code_chunk{j:02d} :
    configurationChunk{j:02d}.map (fun A => finitePairCode (scheme.input A, scheme.output A)) =
      pairCodeChunk{j:02d} := by decide

end RigidGHZ.Supplement.Periodic.Eleven
''';(B/f'ElevenCodeCheck{j:02d}.lean').write_text(text)
text=f'''module

public import RigidGHZ.Supplement.Periodic.ElevenCodeCheck{len(chunks)-1:02d}

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem catalogue_pair_codes :
    catalogueList.map (fun A => finitePairCode (scheme.input A, scheme.output A)) =
      cataloguePairCodes := by
  rw [catalogue_chunk_decomposition]
  simp only [List.map_append, cataloguePairCodes, '''+', '.join(f'pair_code_chunk{j:02d}'for j in range(len(chunks)))+''']

theorem catalogue_input_codes :
    catalogueList.map (fun A => finiteSetCode (scheme.input A)) = cataloguePairCodes.map Prod.fst := by
  simpa only [List.map_map, Function.comp_def, finitePairCode] using
    congrArg (List.map Prod.fst) catalogue_pair_codes

theorem catalogue_output_codes :
    catalogueList.map (fun A => finiteSetCode (scheme.output A)) = cataloguePairCodes.map Prod.snd := by
  simpa only [List.map_map, Function.comp_def, finitePairCode] using
    congrArg (List.map Prod.snd) catalogue_pair_codes

end RigidGHZ.Supplement.Periodic.Eleven
''';(B/'ElevenPairCodes.lean').write_text(text)
print(len(C),'configurations;',len(chunks),'state-map checks')
