#!/usr/bin/env python3
"""Emit explicit ordered search outputs; Lean proves the search-output equality."""
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
D=json.loads((R/'scripts/periodic_config_data.json').read_text())
def fs(a):return '{'+', '.join(map(str,a))+'}'if a else'∅'
for name in ['eleven','ten','latin']:
 data=D[name];ns=name.capitalize();n=data['vertices'];rows=data['edges'];N=len(rows);U=0;F=(1<<n)-1
 for e,o in rows:U|=o
 chosen_sets=[]
 if name=='latin':
  def dfs(a,A,L,O):
   if a==8:
    if L|U==F:chosen_sets.append(A)
    return
   for b in range(8):
    e,o=rows[8*a+b];l=e^o
    if not(L&l or O&o):dfs(a+1,[8*a+b]+A,L|l,O|o)
  dfs(0,[],0,0)
 else:
  def dfs(k,A,L,O):
   if k==N:
    if L|U==F:chosen_sets.append(A)
    return
   dfs(k+1,A,L,O)
   e,o=rows[k];l=e^o
   if not(L&l or O&o):dfs(k+1,[k]+A,L|l,O|o)
  dfs(0,[],0,0)
 assert len(chosen_sets)==len(data['configurations'])
 states={s for s,t,w in data['arcs']}|{t for s,t,w in data['arcs']}
 maxsize={'eleven':5,'ten':4,'latin':8}[name]
 sizes=[sum(len(a)==k for a in chosen_sets)for k in range(maxsize+1)]
 source=f'''module

public import RigidGHZ.Supplement.Periodic.{ns}BitData
public import RigidGHZ.Supplement.Periodic.EnumerationStats

/-! Exact finite configuration statistics from Supplement S2. The literal list
is certified equal to the proved-complete search output. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace RigidGHZ.Supplement.Periodic.{ns}

def catalogueList : List (Finset (Fin {N})) :=
  ['''+',\n    '.join(fs(a)for a in chosen_sets)+''']

theorem catalogueList_nodup : catalogueList.Nodup := by decide

def catalogue : Finset (Finset (Fin '''+str(N)+''')) :=
  ⟨catalogueList, by simpa only [Multiset.coe_nodup] using catalogueList_nodup⟩

theorem catalogue_toFinset : catalogueList.toFinset = catalogue := by
  ext A
  simp [catalogue]

'''
 if name=='latin':
  source+='''theorem enumeration_eq_list : bits.enumerate groups ∅ 0 0 = catalogueList := by decide

theorem catalogue_correct : catalogue = scheme.configurationSet := by
  rw [← catalogue_toFinset, ← enumeration_eq_list,
    bits.enumerate_eq groups ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateGroups_finset groups groups_pairwise groups_cover
    (fun A hA => groups_unique hA)

'''
 else:
  source+=f'''theorem enumeration_eq_list : bits.enumerateFrom (List.finRange {N}) ∅ 0 0 = catalogueList := by decide

theorem catalogue_correct : catalogue = scheme.configurationSet := by
  rw [← catalogue_toFinset, ← enumeration_eq_list,
    bits.enumerateFrom_eq (List.finRange {N}) ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateFrom_finset (List.finRange {N}) (List.nodup_finRange _) (by simp)

'''
 source+=f'''theorem configuration_count : scheme.configurationSet.card = {len(chosen_sets)} := by
  rw [← catalogue_correct]
  decide

theorem configurations_count : Fintype.card scheme.Configurations = {len(chosen_sets)} := by
  rw [scheme.configurations_card, configuration_count]

theorem transition_count : scheme.transitions.card = {len(data['arcs'])} := by
  rw [Scheme.transitions, ← catalogue_correct]
  decide

theorem state_count : scheme.states.card = {len(states)} := by
  unfold Scheme.states Scheme.transitions
  rw [← catalogue_correct]
  decide

theorem size_distribution :
    (List.range {maxsize+1}).map (fun k => (scheme.configurationSet.filter (fun A => A.card = k)).card) =
      {sizes} := by
  rw [← catalogue_correct]
  decide

'''
 if name!='latin':
  total=sum(__import__('math').comb(N,k)for k in range(maxsize+1))
  source+=f'''theorem candidate_count : (∑ k ∈ Finset.range {maxsize+1}, Nat.choose {N} k) = {total} := by decide

'''
 else:
  def decode(m):return fs([i for i in range(n) if m>>i&1])
  source+='''def weightedArcs : List ((Finset (Fin 24) × Finset (Fin 24)) × ℕ) :=
  ['''+',\n    '.join(f'(({decode(s)}, {decode(t)}), {w})'for s,t,w in data['arcs'])+''']

theorem weightedArcs_support : scheme.transitions = (weightedArcs.map Prod.fst).toFinset := by
  rw [Scheme.transitions, ← catalogue_correct]
  decide

theorem weightedArcs_counts : ∀ p ∈ weightedArcs,
    scheme.transferMatrix p.1.1 p.1.2 = p.2 := by
  have hcheck : ∀ p ∈ weightedArcs,
      (catalogue.filter (fun A => scheme.input A = p.1.1 ∧ scheme.output A = p.1.2)).card = p.2 := by
    decide
  intro p hp
  rw [scheme.transferMatrix_eq_filter, ← catalogue_correct]
  exact hcheck p hp

'''
 source+='end RigidGHZ.Supplement.Periodic.'+ns+'\n'
 (R/f'RigidGHZ/Supplement/Periodic/{ns}Statistics.lean').write_text(source)
 print(ns,len(chosen_sets),'configurations')
