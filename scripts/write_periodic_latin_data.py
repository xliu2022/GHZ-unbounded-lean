#!/usr/bin/env python3
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
D=json.loads((R/'scripts/periodic_config_data.json').read_text())['latin']
trans=[[0,2,3,1,5,7,4,6],[1,3,2,0,4,6,5,7],[2,0,1,3,7,5,6,4],
[3,1,0,2,6,4,7,5],[4,6,7,5,0,3,1,2],[5,7,6,4,1,2,0,3],
[6,4,5,7,3,0,2,1],[7,5,4,6,2,1,3,0]]
colors=[next(i for i in range(8) if trans[i][a]==b) for a in range(8) for b in range(8)]
def fs(m):
 vs=[str(i)for i in range(24)if m>>i&1]
 return '{'+', '.join(vs)+'}'if vs else'∅'
s='''module

public import RigidGHZ.Supplement.Periodic.GroupedEnumeration
public import RigidGHZ.Supplement.Periodic.Rigidity
public import RigidGHZ.Supplement.Periodic.Geometry

/-! Exact Latin-square and outgoing-set data from Supplement S2. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

def edges : Fin 64 → Finset (Fin 24) :=
  !['''+',\n    '.join(fs(e)for e,o in D['edges'])+''']

def outgoing : Fin 64 → Finset (Fin 24) :=
  !['''+',\n    '.join(fs(o)for e,o in D['edges'])+''']

def scheme : Scheme (Fin 24) (Fin 64) where
  edge := edges
  outgoing := outgoing
  outgoing_subset := by decide
  local_nonempty := by decide
  edge_injective := by decide

def color : Fin 64 → Fin 8 :=
  !['''+', '.join(map(str,colors))+''']

def groups : List (List (Fin 64)) :=
  ['''+',\n    '.join('['+', '.join(map(str,range(8*a,8*a+8)))+']'for a in range(8))+''']

def stateMask (X : Finset (Fin 24)) : ℕ :=
  (if 8 ∈ X then 1 else 0) + (if 10 ∈ X then 2 else 0) +
  (if 11 ∈ X then 4 else 0) + (if 20 ∈ X then 8 else 0)

def height (X : Finset (Fin 24)) : ℕ :=
  if stateMask X ∈ ([4, 5, 10, 11, 12] : List ℕ) then 1 else
  if stateMask X ∈ ([1, 14] : List ℕ) then 2 else 0

def x : Finset (Fin 24) := {8, 10}
def y : Finset (Fin 24) := {10, 11}

theorem classes_local : ∀ i : Fin 8, scheme.LocalConfig (colorClass color i) := by decide

theorem classes_loop : ∀ i : Fin 8,
    scheme.output (colorClass color i) = scheme.input (colorClass color i) := by decide

theorem class_inputs_injective : Function.Injective
    (fun i : Fin 8 => scheme.input (colorClass color i)) := by decide

theorem class_inputs_avoid : ∀ i : Fin 8,
    scheme.input (colorClass color i) ≠ x ∧ scheme.input (colorClass color i) ≠ y := by decide

theorem groups_pairwise : groups.Pairwise (fun g h => Disjoint g.toFinset h.toFinset) := by decide

theorem groups_cover : ∀ e : Fin 64, e ∈ groups.flatten := by decide

theorem group_anchor : ∀ g ∈ groups, ∃ v : Fin 24, v ∉ scheme.allOutgoing ∧
    ∀ e : Fin 64, e ∈ g ↔ v ∈ scheme.localPart e := by decide

theorem groups_unique {B : Finset (Fin 64)} (hB : scheme.LocalConfig B) :
    ∀ g ∈ groups, ∃! e, e ∈ g ∧ e ∈ B := by
  intro g hg
  obtain ⟨v, hv, he⟩ := group_anchor g hg
  exact scheme.local_group_unique hB g v hv he

def Certificate (A : Finset (Fin 64)) : Prop :=
  height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = x ∧ scheme.output A = y) ∨
    (scheme.input A = y ∧ scheme.output A = x)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 8, A = colorClass color i)

instance (A : Finset (Fin 64)) : Decidable (Certificate A) := inferInstanceAs (Decidable
  (height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = x ∧ scheme.output A = y) ∨
    (scheme.input A = y ∧ scheme.output A = x)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 8, A = colorClass color i)))

def part (v : Fin 24) : Fin 3 := ⟨v.val / 8, by omega⟩

theorem part_size : ∀ i, (Finset.univ.filter (fun v => part v = i)).card = 8 := by decide

theorem edge_part : ∀ e i, ((scheme.edge e).filter (fun v => part v = i)).card = 1 := by decide

theorem base_linear : ∀ e f, e ≠ f → ((scheme.edge e) ∩ (scheme.edge f)).card ≤ 1 := by decide

end RigidGHZ.Supplement.Periodic.Latin
'''
(R/'RigidGHZ/Supplement/Periodic/LatinData.lean').write_text(s)
