#!/usr/bin/env python3
"""Kernel certificates for the Latin row search, split after three rows."""
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
rows=json.loads((R/'scripts/periodic_config_data.json').read_text())['latin']['edges']
cutoff=3
states=[]
def visit(a,chosen,loc,out):
 if a<cutoff:
  for b in range(8):
   e,o=rows[8*a+b];l=e^o
   if not(loc&l or out&o):visit(a+1,chosen+[8*a+b],loc|l,out|o)
 states.append((a,chosen,loc,out))
visit(0,[],0,0)
ids={tuple(c):i for i,(a,c,l,o)in enumerate(states)}
def fs(ch):return '{'+', '.join(map(str,reversed(ch)))+'}'if ch else'∅'
def gs(a):return '['+', '.join('['+', '.join(map(str,range(8*r,8*r+8)))+']'for r in range(a,8))+']'
blocks=[]
for idx,(a,ch,loc,out) in enumerate(states):
 s=f'''theorem row_node_{idx} :
    (scheme.enumerateGroups {gs(a)} {fs(ch)}).all
      (fun A => decide (Certificate A)) = true := by
'''
 if a==cutoff:s+='  decide\n\n'
 else:
  s+='  apply scheme.check_group_cons _ _ _ Certificate\n'
  s+='  intro e he hc\n'
  s+='  simp only [List.mem_cons, List.not_mem_nil, or_false] at he\n'
  s+='  rcases he with '+' | '.join(['rfl']*8)+'\n'
  for b in range(8):
   i=8*a+b;e,o=rows[i];l=e^o
   if not(loc&l or out&o):s+=f'  · exact row_node_{ids[tuple(ch+[i])]}\n'
   else:s+=f'  · exact False.elim ((by decide : ¬scheme.Compatible {fs(ch)} {i}) hc)\n'
  s+='\n'
 blocks.append(s)
mods=[]
for lo in range(0,len(blocks),16):
 mod=f'LatinCheck{len(mods):02}';prev=mods[-1]if mods else'LatinData'
 s=f'''module

public import RigidGHZ.Supplement.Periodic.{prev}

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

'''+''.join(blocks[lo:lo+16])+'''end RigidGHZ.Supplement.Periodic.Latin
'''
 (R/f'RigidGHZ/Supplement/Periodic/{mod}.lean').write_text(s)
 mods.append(mod)
s=f'''module

public import RigidGHZ.Supplement.Periodic.{mods[-1]}

/-! The eight prescribed transversal lifts are all perfect matchings at every
positive odd period. The resulting ordinary hypergraph is linear and balanced. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Latin

theorem finite_certificate :
    (scheme.enumerateGroups groups ∅).all (fun A => decide (Certificate A)) = true :=
  row_node_{len(states)-1}

theorem certificate {{A : Finset (Fin 64)}} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_group_enumeration groups groups_pairwise groups_cover
    (fun B hB => groups_unique hB) Certificate finite_certificate hA

noncomputable def rigidFamily {{q : ℕ}} (hq : 0 < q) (hodd : Odd q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin 8) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.odd_configurations_complete hq hodd color height x y (by decide)
      class_inputs_injective (fun A hA => (certificate hA).2.2) class_inputs_avoid
      (fun A hA => (certificate hA).1) (fun A hA => (certificate hA).2.1))

theorem uniform (q : ℕ) : Uniform (scheme.graph (finRotate q)) 3 :=
  scheme.graph_uniform (finRotate q) (by decide)

theorem edge_count (q : ℕ) : (scheme.graph (finRotate q)).card = 64 * q := by
  simpa using scheme.graph_card (finRotate q)

theorem balanced (q : ℕ) : BalancedPartite (scheme.graph (finRotate q)) 3 (8 * q) := by
  simpa using scheme.graph_balanced (finRotate q) part part_size edge_part

theorem linear (q : ℕ) : IsLinear (scheme.graph (finRotate q)) :=
  scheme.graph_linear (finRotate q) base_linear

end RigidGHZ.Supplement.Periodic.Latin
'''
(R/'RigidGHZ/Supplement/Periodic/Latin.lean').write_text(s)
print(len(states),'proof nodes in',len(mods),'modules')
