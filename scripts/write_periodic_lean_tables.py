#!/usr/bin/env python3
"""Write explicit input tables; all claims are checked in Lean's kernel."""
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
data=json.loads((R/'scripts/periodic_config_data.json').read_text())
heights={
 'eleven':{1:[0,136,384,424],2:[36,38,100,132,162,172,224],3:[40,46,104,160,164,170,232,288,416],4:[12,42,108,140,256,290,352],5:[8,32,168],6:[4,44,166,228,296],7:[128]},
 'ten':{1:[4,10,31,37,47,56,61,62],2:[13,25,32,36,41,44],3:[0,9,29,30,40,57,58,63],4:[5,12,14,15,26,42,46,52,53,60],5:[16,20,21,48],6:[45]}}
def fs(mask,n):
 vals=[str(i) for i in range(n) if mask>>i&1]
 return '{'+', '.join(vals)+'}' if vals else '∅'
for name,N,d in [('eleven',33,11),('ten',20,10)]:
 D=data[name]; n=D['vertices']; ns=name.capitalize()
 code=f'''module

public import RigidGHZ.Supplement.Periodic.Enumeration
public import RigidGHZ.Supplement.Periodic.Rigidity
public import Mathlib.Data.List.FinRange

/-! The explicit {name}-matching periodic scheme from Supplement S2.
All local-configuration certificates use kernel reduction of a proved exact search. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.{ns}

def edges : Fin {N} → Finset (Fin {n}) :=
  !['''+',\n    '.join(fs(e,n) for e,o in D['edges'])+''']

def outgoing : Fin '''+str(N)+''' → Finset (Fin '''+str(n)+''') :=
  !['''+',\n    '.join(fs(o,n) for e,o in D['edges'])+f''']

def scheme : Scheme (Fin {n}) (Fin {N}) where
  edge := edges
  outgoing := outgoing
  outgoing_subset := by decide
  local_nonempty := by decide
  edge_injective := by decide

'''
 if name=='eleven':
  code+='''def color (e : Fin 33) : Fin 11 := ⟨e.val / 3, by omega⟩
'''
 else:
  code+='''def color (e : Fin 20) : Fin 10 :=
  ⟨if e.val < 10 then e.val else 19 - e.val, by split_ifs <;> omega⟩
'''
 code+=f'''
def stateMask (X : Finset (Fin {n})) : ℕ := ∑ v ∈ X, 2 ^ v.val

def height (X : Finset (Fin {n})) : ℕ :=
'''
 for h,masks in heights[name].items():
  code+='  if stateMask X ∈ ('+str(masks)+' : List ℕ) then '+str(h)+' else\n'
 code+='  0\n\n'
 code+=f'''theorem classes_local : ∀ i : Fin {d}, scheme.LocalConfig (colorClass color i) := by decide

theorem classes_loop : ∀ i : Fin {d},
    scheme.output (colorClass color i) = scheme.input (colorClass color i) := by decide

theorem class_inputs_injective : Function.Injective
    (fun i : Fin {d} => scheme.input (colorClass color i)) := by decide

'''
 if name=='eleven':
  code+=f'''def Certificate (A : Finset (Fin {N})) : Prop :=
  (scheme.input A = scheme.output A ∨ height (scheme.input A) < height (scheme.output A)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin {d}, A = colorClass color i)

instance (A : Finset (Fin {N})) : Decidable (Certificate A) := inferInstanceAs (Decidable
  ((scheme.input A = scheme.output A ∨ height (scheme.input A) < height (scheme.output A)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin {d}, A = colorClass color i)))

set_option maxRecDepth 100000 in
 theorem finite_certificate :
    (scheme.enumerateFrom (List.finRange {N}) ∅).all (fun A => decide (Certificate A)) = true := by
  decide

theorem certificate {{A : Finset (Fin {N})}} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_enumeration (List.finRange {N}) (List.nodup_finRange _) (by simp)
    Certificate finite_certificate hA

noncomputable def rigidFamily {{q : ℕ}} (hq : 0 < q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin {d}) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.strict_configurations_complete hq color height class_inputs_injective
      (fun A hA => (certificate hA).2) (fun A hA => (certificate hA).1))
'''
 else:
  code+=f'''theorem class_inputs_avoid : ∀ i : Fin {d},
    scheme.input (colorClass color i) ≠ ∅ ∧ scheme.input (colorClass color i) ≠ Finset.univ := by
  decide

def Certificate (A : Finset (Fin {N})) : Prop :=
  height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ∨
    (scheme.input A = Finset.univ ∧ scheme.output A = ∅)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin {d}, A = colorClass color i)

instance (A : Finset (Fin {N})) : Decidable (Certificate A) := inferInstanceAs (Decidable
  (height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ∨
    (scheme.input A = Finset.univ ∧ scheme.output A = ∅)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin {d}, A = colorClass color i)))

set_option maxRecDepth 100000 in
 theorem finite_certificate :
    (scheme.enumerateFrom (List.finRange {N}) ∅).all (fun A => decide (Certificate A)) = true := by
  decide

theorem certificate {{A : Finset (Fin {N})}} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_enumeration (List.finRange {N}) (List.nodup_finRange _) (by simp)
    Certificate finite_certificate hA

noncomputable def rigidFamily {{q : ℕ}} (hq : 0 < q) (hodd : Odd q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin {d}) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.odd_configurations_complete hq hodd color height ∅ Finset.univ (by decide)
      class_inputs_injective (fun A hA => (certificate hA).2.2) class_inputs_avoid
      (fun A hA => (certificate hA).1) (fun A hA => (certificate hA).2.1))
'''
 code+=f'''
theorem uniform (q : ℕ) : Uniform (scheme.graph (finRotate q)) 3 :=
  scheme.graph_uniform (finRotate q) (by decide)

theorem edge_count (q : ℕ) : (scheme.graph (finRotate q)).card = {N} * q := by
  simpa using scheme.graph_card (finRotate q)

end RigidGHZ.Supplement.Periodic.{ns}
'''
 (R/f'RigidGHZ/Supplement/Periodic/{ns}.lean').write_text(code)
