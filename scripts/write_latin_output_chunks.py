#!/usr/bin/env python3
import json
from pathlib import Path
P=Path(__file__).resolve().parents[1];D=json.loads((P/'scripts/periodic_config_data.json').read_text())['latin'];E=D['edges'];U=0;F=(1<<24)-1
for e,o in E:U|=o
leaves=[];nodes=[];counter=0
def outputs(k,A,L,O):
 if k==8:return [A]if L|U==F else[]
 out=[]
 for i in range(8*k,8*k+8):
  e,o=E[i];ll=e^o
  if not(L&ll or O&o):out+=outputs(k+1,[i]+A,L|ll,O|o)
 return out
def tree(k,A,L,O):
 global counter
 ix=counter;counter+=1;name=f'output_{ix:03d}';out=outputs(k,A,L,O)
 if k==2:leaves.append((name,k,A,L,O,out));return name
 children=[]
 for i in range(8*k,8*k+8):
  e,o=E[i];ll=e^o
  children.append(tree(k+1,[i]+A,L|ll,O|o) if not(L&ll or O&o)else None)
 nodes.append((name,k,A,L,O,out,children));return name
root=tree(0,[],0,0)
def fs(A):return '{'+', '.join(map(str,A))+'}'if A else'∅'
def ls(A):return '['+', '.join(map(fs,A))+']'
def gs(k):return '['+', '.join('['+', '.join(map(str,range(8*r,8*r+8)))+']'for r in range(k,8))+']'
def expr(k,A,L,O):return f'bits.enumerate {gs(k)} {fs(A)} {L} {O}'
base=P/'RigidGHZ/Supplement/Periodic'
for part in range((len(leaves)+3)//4):
 imp='RigidGHZ.Supplement.Periodic.LatinBitData'if part==0 else f'RigidGHZ.Supplement.Periodic.LatinOutput{part-1:02d}'
 text=f'module\n\npublic import {imp}\npublic import RigidGHZ.Supplement.Periodic.BitOutput\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\nnamespace RigidGHZ.Supplement.Periodic.Latin\n\n'
 for name,k,A,L,O,out in leaves[part*4:(part+1)*4]:text+=f'theorem {name} : {expr(k,A,L,O)} = {ls(out)} := by decide\n\n'
 text+='end RigidGHZ.Supplement.Periodic.Latin\n';(base/f'LatinOutput{part:02d}.lean').write_text(text)
last=f'RigidGHZ.Supplement.Periodic.LatinOutput{(len(leaves)-1)//4:02d}'
text=f'module\n\npublic import {last}\npublic import RigidGHZ.Supplement.Periodic.LatinCatalogueData\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\nnamespace RigidGHZ.Supplement.Periodic.Latin\n\n'
for name,k,A,L,O,out,children in nodes:
 text+=f'theorem {name} : {expr(k,A,L,O)} = {ls(out)} := by\n'
 for j,child in enumerate(children):
  i=8*k+j;cond=f'{L} &&& bits.localMask {i} = 0 ∧ {O} &&& bits.outMask {i} = 0'
  if child is None:cond='¬('+cond+')'
  text+=f'  have hc{j} : {cond} := by decide\n'
 for j,child in enumerate(children):
  if child:
   i=8*k+j;e,o=E[i];ll=e^o
   text+=f'  have ha{j} : (insert {i} {fs(A)} : Finset (Fin 64)) = {fs([i]+A)} := by decide\n'
   text+=f'  have hl{j} : bits.localMask {i} ||| {L} = {L|ll} := by decide\n'
   text+=f'  have ho{j} : bits.outMask {i} ||| {O} = {O|o} := by decide\n'
 row='['+', '.join(map(str,range(8*k,8*k+8)))+']'
 text+=f'  rw [bits.enumerate_cons {row} {gs(k+1)} {fs(A)} {L} {O}]\n'
 text+='  simp only [List.flatMap_cons, List.flatMap_nil, '+', '.join('hc'+str(j)for j in range(8))+', ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]\n'
 norms=[tag+str(j) for j,child in enumerate(children) if child for tag in ['ha','hl','ho']]
 if norms:text+='  simp only ['+', '.join(norms)+']\n'
 cs=[child for child in children if child]
 if cs:text+='  rw ['+', '.join(cs)+']\n'
 text+='  rfl\n\n'
text+=f'theorem enumeration_eq_list : bits.enumerate groups ∅ 0 0 = catalogueList := by\n  exact {root}\n\nend RigidGHZ.Supplement.Periodic.Latin\n'
(base/'LatinEnumerationOutput.lean').write_text(text)
print(len(leaves),'leaves;',len(nodes),'composition nodes')
