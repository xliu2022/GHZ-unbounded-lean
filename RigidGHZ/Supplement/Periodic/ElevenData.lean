module

public import RigidGHZ.Supplement.Periodic.Enumeration
public import RigidGHZ.Supplement.Periodic.Rigidity
public import Mathlib.Data.List.FinRange

/-! The explicit eleven-matching periodic scheme from Supplement S2.
All local-configuration certificates use kernel reduction of a proved exact search. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

def edges : Fin 33 → Finset (Fin 9) :=
  ![{0, 1, 2},
    {3, 4, 5},
    {6, 7, 8},
    {0, 1, 7},
    {2, 5, 8},
    {3, 4, 6},
    {0, 1, 8},
    {2, 4, 5},
    {3, 6, 7},
    {0, 2, 3},
    {1, 6, 8},
    {4, 5, 7},
    {0, 2, 6},
    {1, 3, 5},
    {4, 7, 8},
    {0, 3, 4},
    {1, 2, 7},
    {5, 6, 8},
    {0, 3, 6},
    {1, 5, 8},
    {2, 4, 7},
    {0, 3, 8},
    {1, 5, 7},
    {2, 4, 6},
    {0, 4, 8},
    {1, 3, 7},
    {2, 5, 6},
    {0, 5, 6},
    {1, 2, 4},
    {3, 7, 8},
    {0, 6, 7},
    {1, 4, 8},
    {2, 3, 5}]

def outgoing : Fin 33 → Finset (Fin 9) :=
  ![{2},
    ∅,
    ∅,
    {7},
    ∅,
    {3},
    ∅,
    ∅,
    ∅,
    {2, 3},
    ∅,
    ∅,
    {2},
    {5},
    ∅,
    {3},
    ∅,
    {5, 6},
    {3},
    {1, 5},
    {2},
    {3},
    {5},
    {2},
    {8},
    ∅,
    ∅,
    {5},
    {2},
    {7},
    {7},
    ∅,
    {3, 5}]

def scheme : Scheme (Fin 9) (Fin 33) where
  edge := edges
  outgoing := outgoing
  outgoing_subset := by decide
  local_nonempty := by decide
  edge_injective := by decide

def color (e : Fin 33) : Fin 11 := ⟨e.val / 3, by omega⟩

def stateMask (X : Finset (Fin 9)) : ℕ := ∑ v ∈ X, 2 ^ v.val

def height (X : Finset (Fin 9)) : ℕ :=
  if stateMask X ∈ ([0, 136, 384, 424] : List ℕ) then 1 else
  if stateMask X ∈ ([36, 38, 100, 132, 162, 172, 224] : List ℕ) then 2 else
  if stateMask X ∈ ([40, 46, 104, 160, 164, 170, 232, 288, 416] : List ℕ) then 3 else
  if stateMask X ∈ ([12, 42, 108, 140, 256, 290, 352] : List ℕ) then 4 else
  if stateMask X ∈ ([8, 32, 168] : List ℕ) then 5 else
  if stateMask X ∈ ([4, 44, 166, 228, 296] : List ℕ) then 6 else
  if stateMask X ∈ ([128] : List ℕ) then 7 else
  0

theorem classes_local : ∀ i : Fin 11, scheme.LocalConfig (colorClass color i) := by decide

theorem classes_loop : ∀ i : Fin 11,
    scheme.output (colorClass color i) = scheme.input (colorClass color i) := by decide

theorem class_inputs_injective : Function.Injective
    (fun i : Fin 11 => scheme.input (colorClass color i)) := by decide

def Certificate (A : Finset (Fin 33)) : Prop :=
  (scheme.input A = scheme.output A ∨ height (scheme.input A) < height (scheme.output A)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 11, A = colorClass color i)

instance (A : Finset (Fin 33)) : Decidable (Certificate A) := inferInstanceAs (Decidable
  ((scheme.input A = scheme.output A ∨ height (scheme.input A) < height (scheme.output A)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 11, A = colorClass color i)))


end RigidGHZ.Supplement.Periodic.Eleven
