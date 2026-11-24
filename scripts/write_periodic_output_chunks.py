#!/usr/bin/env python3
"""Generate small kernel-checkable search output equalities, with explicit arguments."""
import json
from pathlib import Path
P=Path(__file__).resolve().parents[1];import sys; NAME=sys.argv[1] if len(sys.argv)>1 else 'Eleven';D=json.loads((P/'scripts/periodic_config_data.json').read_text())[NAME.lower()];E=D['edges'];N=len(E);U=0;F=(1<<D['vertices'])-1
for e,o in E:U|=o
nodes=[]; leaves=[]
def outputs(k,A,L,O):
 if k==N:return [A]if L|U==F else[]
 out=outputs(k+1,A,L,O);e,o=E[k];ll=e^o
 if not (L&ll or O&o):out+=outputs(k+1,[k]+A,L|ll,O|o)
 return out
from functools import lru_cache
@lru_cache(None)
def search_nodes(k,L,O):
 if k==N:return 1
 e,o=E[k];ll=e^o
 return 1+search_nodes(k+1,L,O)+(search_nodes(k+1,L|ll,O|o) if not(L&ll or O&o) else 0)
counter=0
def tree(k,A,L,O):
 global counter
 ix=counter;counter+=1;name=f'output_{ix:03d}'
 outs=outputs(k,A,L,O)
 if k>=6 and search_nodes(k,L,O)<=600:
  leaf=(name,k,A,L,O,outs);leaves.append(leaf);return name
 skip=tree(k+1,A,L,O);e,o=E[k];ll=e^o
 incl=tree(k+1,[k]+A,L|ll,O|o)if not(L&ll or O&o)else None
 nodes.append((name,k,A,L,O,outs,skip,incl))
 return name
root=tree(0,[],0,0)
def fs(A):return '{'+', '.join(map(str,A))+'}'if A else'∅'
def ls(A):return '['+', '.join(map(fs,A))+']'
def es(k):return '['+', '.join(map(str,range(k,N)))+']'
def expr(k,A,L,O):return f'bits.enumerateFrom {es(k)} {fs(A)} {L} {O}'
base=P/'RigidGHZ/Supplement/Periodic'
for part in range((len(leaves)+3)//4):
 imp=f'RigidGHZ.Supplement.Periodic.{NAME}BitData' if part==0 else f'RigidGHZ.Supplement.Periodic.{NAME}Output{part-1:02d}'
 text=f'module\n\npublic import {imp}\npublic import RigidGHZ.Supplement.Periodic.BitOutput\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\nnamespace RigidGHZ.Supplement.Periodic.{NAME}\n\n'
 for name,k,A,L,O,out in leaves[part*4:(part+1)*4]:text+=f'theorem {name} : {expr(k,A,L,O)} = {ls(out)} := by decide\n\n'
 text+=f'end RigidGHZ.Supplement.Periodic.{NAME}\n';(base/f'{NAME}Output{part:02d}.lean').write_text(text)
last=f'RigidGHZ.Supplement.Periodic.{NAME}Output{(len(leaves)-1)//4:02d}'
text=f'module\n\npublic import {last}\npublic import RigidGHZ.Supplement.Periodic.{NAME}CatalogueData\n\n@[expose] public section\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\nnamespace RigidGHZ.Supplement.Periodic.{NAME}\n\n'
for name,k,A,L,O,out,skip,inc in nodes:
 text+=f'theorem {name} : {expr(k,A,L,O)} = {ls(out)} := by\n'
 if inc:
  e,o=E[k];ll=e^o
  text+=f'  rw [bits.enumerateFrom_split_values {k} {es(k+1)} {fs(A)} {fs([k]+A)} {L} {O} {L|ll} {O|o} (by decide) (by decide) (by decide) (by decide), {skip}, {inc}]\n'
  text+='  rfl\n\n'
 else:text+=f'  exact (bits.enumerateFrom_skip {k} {es(k+1)} {fs(A)} {L} {O} (by decide)).trans {skip}\n\n'
text+=f'theorem enumeration_eq_list : bits.enumerateFrom (List.finRange {N}) ∅ 0 0 = catalogueList := by\n  exact {root}\n\nend RigidGHZ.Supplement.Periodic.{NAME}\n'
(base/(NAME+'EnumerationOutput.lean')).write_text(text)
print(len(leaves),'leaf chunks;',len(nodes),'composition nodes')
