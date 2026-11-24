#!/usr/bin/env python3
from pathlib import Path
import re
P=Path(__file__).resolve().parents[1]/'RigidGHZ/Supplement/Periodic'
for name,N in [('Ten',20),('Latin',64)]:
 p=P/(name+'Statistics.lean');s=p.read_text();start=s.index('def catalogueList');i=s.index('theorem catalogueList_nodup');j=s.index('theorem enumeration_eq_list');k=s.index('theorem catalogue_correct');header=s[:start];end='\nend RigidGHZ.Supplement.Periodic.'+name+'\n';data=s[start:i];nums=[]
 for a in re.findall(r'\{([0-9, ]+)\}',data):nums.append(sum(2**int(x) for x in a.split(',')))
 # Ten's empty configuration must retain its position (it is the first skip-only output).
 if name=='Ten':
  body=data.split(':=')[1].strip();tokens=re.findall(r'\{[0-9, ]+\}|∅',body)
  nums=[0 if a=='∅'else sum(2**int(x)for x in a[1:-1].split(','))for a in tokens]
 (P/(name+'CatalogueData.lean')).write_text(header+data+end)
 chead=header.replace('public import RigidGHZ.Supplement.Periodic.'+name+'BitData','public import RigidGHZ.Supplement.Periodic.'+name+'CatalogueData')
 code='def catalogueCodes : List ℕ :=\n  '+str(nums)+'\n\n'
 code+=f'''theorem catalogue_code_map :
    catalogueList.map (fun A => ∑ e ∈ A, 2 ^ e.val) = catalogueCodes := by decide

def sortedCatalogueCodes : List ℕ :=
  {sorted(nums)}

theorem catalogueCodes_sorted : catalogueCodes.mergeSort = sortedCatalogueCodes := by
  rw [List.mergeSort_eq_mergeSortTR]
  decide

theorem sortedCatalogueCodes_chain : sortedCatalogueCodes.IsChain (· < ·) := by decide

theorem catalogueCodes_nodup : catalogueCodes.Nodup := by
  have hp : sortedCatalogueCodes.Pairwise (· < ·) :=
    List.isChain_iff_pairwise.mp sortedCatalogueCodes_chain
  have hn : sortedCatalogueCodes.Nodup := hp.imp (fun h => Nat.ne_of_lt h)
  have he := List.mergeSort_perm catalogueCodes (fun a b => decide (a ≤ b))
  rw [catalogueCodes_sorted] at he
  exact he.nodup_iff.mp hn

theorem catalogueList_nodup : catalogueList.Nodup := by
  apply List.Nodup.of_map (f := fun A : Finset (Fin {N}) => ∑ e ∈ A, 2 ^ e.val)
  rw [catalogue_code_map]
  exact catalogueCodes_nodup

'''
 code+=s[s.index('def catalogue :'):j]
 (P/(name+'Catalogue.lean')).write_text(chead+code+end)
 ehead=header.replace('public import RigidGHZ.Supplement.Periodic.'+name+'BitData','public import RigidGHZ.Supplement.Periodic.'+name+'Catalogue')
 (P/(name+'EnumerationOutput.lean')).write_text(ehead+s[j:k]+end)
 p.write_text(header.replace('public import RigidGHZ.Supplement.Periodic.'+name+'BitData','public import RigidGHZ.Supplement.Periodic.'+name+'EnumerationOutput')+s[k:])
 print(name,len(nums))
