module

public import RigidGHZ.Supplement.Periodic.Enumeration
public import RigidGHZ.Supplement.Periodic.Rigidity
public import Mathlib.Data.List.FinRange

/-! The explicit ten-matching periodic scheme from Supplement S2.
All local-configuration certificates use kernel reduction of a proved exact search. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

def edges : Fin 20 → Finset (Fin 6) :=
  ![{0, 1, 2},
    {0, 1, 3},
    {0, 1, 4},
    {0, 1, 5},
    {0, 2, 3},
    {0, 2, 4},
    {0, 2, 5},
    {0, 3, 4},
    {0, 3, 5},
    {0, 4, 5},
    {1, 2, 3},
    {1, 2, 4},
    {1, 2, 5},
    {1, 3, 4},
    {1, 3, 5},
    {1, 4, 5},
    {2, 3, 4},
    {2, 3, 5},
    {2, 4, 5},
    {3, 4, 5}]

def outgoing : Fin 20 → Finset (Fin 6) :=
  ![{0, 2},
    {0, 3},
    {4},
    ∅,
    {2, 3},
    {4},
    {0, 2},
    ∅,
    {3, 5},
    {4},
    {1, 3},
    ∅,
    {2, 5},
    ∅,
    {3, 5},
    {4},
    {2},
    ∅,
    {4, 5},
    {5}]

def scheme : Scheme (Fin 6) (Fin 20) where
  edge := edges
  outgoing := outgoing
  outgoing_subset := by decide
  local_nonempty := by decide
  edge_injective := by decide

def color (e : Fin 20) : Fin 10 :=
  ⟨if e.val < 10 then e.val else 19 - e.val, by split_ifs <;> omega⟩

def stateMask (X : Finset (Fin 6)) : ℕ := ∑ v ∈ X, 2 ^ v.val

def height (X : Finset (Fin 6)) : ℕ :=
  if stateMask X ∈ ([4, 10, 31, 37, 47, 56, 61, 62] : List ℕ) then 1 else
  if stateMask X ∈ ([13, 25, 32, 36, 41, 44] : List ℕ) then 2 else
  if stateMask X ∈ ([0, 9, 29, 30, 40, 57, 58, 63] : List ℕ) then 3 else
  if stateMask X ∈ ([5, 12, 14, 15, 26, 42, 46, 52, 53, 60] : List ℕ) then 4 else
  if stateMask X ∈ ([16, 20, 21, 48] : List ℕ) then 5 else
  if stateMask X ∈ ([45] : List ℕ) then 6 else
  0

theorem classes_local : ∀ i : Fin 10, scheme.LocalConfig (colorClass color i) := by decide

theorem classes_loop : ∀ i : Fin 10,
    scheme.output (colorClass color i) = scheme.input (colorClass color i) := by decide

theorem class_inputs_injective : Function.Injective
    (fun i : Fin 10 => scheme.input (colorClass color i)) := by decide

theorem class_inputs_avoid : ∀ i : Fin 10,
    scheme.input (colorClass color i) ≠ ∅ ∧ scheme.input (colorClass color i) ≠ Finset.univ := by
  decide

def xyConfigurations : Finset (Finset (Fin 20)) := {{0, 9, 10, 19}, {2, 6, 10, 19}}

def yxConfigurations : Finset (Finset (Fin 20)) := {∅}

def Certificate (A : Finset (Fin 20)) : Prop :=
  height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ∨
    (scheme.input A = Finset.univ ∧ scheme.output A = ∅)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 10, A = colorClass color i) ∧
  ((scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ↔ A ∈ xyConfigurations) ∧
  ((scheme.input A = Finset.univ ∧ scheme.output A = ∅) ↔ A ∈ yxConfigurations)

instance (A : Finset (Fin 20)) : Decidable (Certificate A) := inferInstanceAs (Decidable
  (height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ∨
    (scheme.input A = Finset.univ ∧ scheme.output A = ∅)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 10, A = colorClass color i) ∧
  ((scheme.input A = ∅ ∧ scheme.output A = Finset.univ) ↔ A ∈ xyConfigurations) ∧
  ((scheme.input A = Finset.univ ∧ scheme.output A = ∅) ↔ A ∈ yxConfigurations)))


end RigidGHZ.Supplement.Periodic.Ten
