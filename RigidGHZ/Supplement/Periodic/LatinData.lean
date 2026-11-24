module

public import RigidGHZ.Supplement.Periodic.GroupedEnumeration
public import RigidGHZ.Supplement.Periodic.Rigidity
public import RigidGHZ.Supplement.Periodic.Geometry

/-! Exact Latin-square and outgoing-set data from Supplement S2. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

def edges : Fin 64 → Finset (Fin 24) :=
  ![{0, 8, 23},
    {0, 9, 16},
    {0, 10, 18},
    {0, 11, 20},
    {0, 12, 17},
    {0, 13, 19},
    {0, 14, 21},
    {0, 15, 22},
    {1, 8, 16},
    {1, 9, 23},
    {1, 10, 19},
    {1, 11, 18},
    {1, 12, 20},
    {1, 13, 17},
    {1, 14, 22},
    {1, 15, 21},
    {2, 8, 22},
    {2, 9, 21},
    {2, 10, 20},
    {2, 11, 17},
    {2, 12, 19},
    {2, 13, 16},
    {2, 14, 18},
    {2, 15, 23},
    {3, 8, 21},
    {3, 9, 22},
    {3, 10, 17},
    {3, 11, 19},
    {3, 12, 16},
    {3, 13, 20},
    {3, 14, 23},
    {3, 15, 18},
    {4, 8, 19},
    {4, 9, 17},
    {4, 10, 21},
    {4, 11, 22},
    {4, 12, 23},
    {4, 13, 18},
    {4, 14, 16},
    {4, 15, 20},
    {5, 8, 17},
    {5, 9, 20},
    {5, 10, 22},
    {5, 11, 21},
    {5, 12, 18},
    {5, 13, 23},
    {5, 14, 19},
    {5, 15, 16},
    {6, 8, 20},
    {6, 9, 18},
    {6, 10, 23},
    {6, 11, 16},
    {6, 12, 21},
    {6, 13, 22},
    {6, 14, 17},
    {6, 15, 19},
    {7, 8, 18},
    {7, 9, 19},
    {7, 10, 16},
    {7, 11, 23},
    {7, 12, 22},
    {7, 13, 21},
    {7, 14, 20},
    {7, 15, 17}]

def outgoing : Fin 64 → Finset (Fin 24) :=
  ![{8},
    ∅,
    ∅,
    {11},
    ∅,
    ∅,
    ∅,
    ∅,
    {8},
    ∅,
    {10},
    ∅,
    {20},
    ∅,
    ∅,
    ∅,
    {8},
    ∅,
    {20},
    {11},
    ∅,
    ∅,
    ∅,
    ∅,
    {8},
    ∅,
    {10},
    {11},
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    {10},
    {11},
    ∅,
    ∅,
    ∅,
    ∅,
    {8},
    {20},
    {10},
    {11},
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    {8},
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    {20},
    ∅]

def firstLabel (e : Fin 64) : Fin 24 := ⟨e.val / 8, by omega⟩
def secondLabel (e : Fin 64) : Fin 24 := ⟨8 + e.val % 8, by omega⟩

theorem first_slice : ∀ e, (edges e).filter (fun v => v.val < 8) = {firstLabel e} := by decide

theorem second_slice : ∀ e, (edges e).filter (fun v => 8 ≤ v.val ∧ v.val < 16) = {secondLabel e} := by decide

theorem edges_injective : Function.Injective edges := by
  intro e f h
  have hr := congrArg (fun X : Finset (Fin 24) => X.filter (fun v => v.val < 8)) h
  rw [first_slice, first_slice] at hr
  have hc := congrArg (fun X : Finset (Fin 24) => X.filter (fun v => 8 ≤ v.val ∧ v.val < 16)) h
  rw [second_slice, second_slice] at hc
  have he := congrArg Fin.val (Finset.singleton_injective hr)
  have hf := congrArg Fin.val (Finset.singleton_injective hc)
  change e.val / 8 = f.val / 8 at he
  change 8 + e.val % 8 = 8 + f.val % 8 at hf
  have h1 := Nat.mod_add_div e.val 8
  have h2 := Nat.mod_add_div f.val 8
  apply Fin.ext
  omega

def scheme : Scheme (Fin 24) (Fin 64) where
  edge := edges
  outgoing := outgoing
  outgoing_subset := by decide
  local_nonempty := by decide
  edge_injective := edges_injective


def color : Fin 64 → Fin 8 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 2, 3, 0, 1, 6, 7, 4, 5, 3, 2, 1, 0, 7, 6, 5, 4, 1, 0, 3, 2, 5, 4, 7, 6, 4, 5, 7, 6, 1, 0, 3, 2, 6, 7, 5, 4, 3, 2, 1, 0, 5, 4, 6, 7, 0, 1, 2, 3, 7, 6, 4, 5, 2, 3, 0, 1]

def classes : Fin 8 → Finset (Fin 64) :=
  ![{0, 10, 19, 25, 37, 47, 52, 62},
    {1, 11, 18, 24, 36, 46, 53, 63},
    {2, 8, 17, 27, 39, 45, 54, 60},
    {3, 9, 16, 26, 38, 44, 55, 61},
    {4, 14, 23, 29, 32, 43, 49, 58},
    {5, 15, 22, 28, 33, 42, 48, 59},
    {6, 12, 21, 31, 35, 40, 50, 57},
    {7, 13, 20, 30, 34, 41, 51, 56}]

theorem classes_eq : ∀ i : Fin 8, colorClass color i = classes i := by
  intro i
  fin_cases i <;> decide

def groups : List (List (Fin 64)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
    [8, 9, 10, 11, 12, 13, 14, 15],
    [16, 17, 18, 19, 20, 21, 22, 23],
    [24, 25, 26, 27, 28, 29, 30, 31],
    [32, 33, 34, 35, 36, 37, 38, 39],
    [40, 41, 42, 43, 44, 45, 46, 47],
    [48, 49, 50, 51, 52, 53, 54, 55],
    [56, 57, 58, 59, 60, 61, 62, 63]]

def stateMask (X : Finset (Fin 24)) : ℕ :=
  (if 8 ∈ X then 1 else 0) + (if 10 ∈ X then 2 else 0) +
  (if 11 ∈ X then 4 else 0) + (if 20 ∈ X then 8 else 0)

def height (X : Finset (Fin 24)) : ℕ :=
  if stateMask X ∈ ([4, 5, 10, 11, 12] : List ℕ) then 1 else
  if stateMask X ∈ ([1, 14] : List ℕ) then 2 else 0

def x : Finset (Fin 24) := {8, 10}
def y : Finset (Fin 24) := {10, 11}

theorem classes_local : ∀ i : Fin 8, scheme.LocalConfig (colorClass color i) := by
  simp_rw [classes_eq]
  intro i
  fin_cases i <;> decide


theorem classes_loop : ∀ i : Fin 8,
    scheme.output (colorClass color i) = scheme.input (colorClass color i) := by
  simp_rw [classes_eq]
  decide


theorem class_inputs_injective : Function.Injective
    (fun i : Fin 8 => scheme.input (colorClass color i)) := by
  simpa only [classes_eq] using (by decide : Function.Injective (fun i : Fin 8 => scheme.input (classes i)))


theorem class_inputs_avoid : ∀ i : Fin 8,
    scheme.input (colorClass color i) ≠ x ∧ scheme.input (colorClass color i) ≠ y := by
  simp_rw [classes_eq]
  decide


theorem groups_pairwise : groups.Pairwise (fun g h => Disjoint g.toFinset h.toFinset) := by decide


theorem groups_cover : ∀ e : Fin 64, e ∈ groups.flatten := by decide


theorem group_anchor : ∀ g ∈ groups, ∃ v : Fin 24, v ∉ scheme.allOutgoing ∧
    ∀ e : Fin 64, e ∈ g ↔ v ∈ scheme.localPart e := by decide


theorem groups_unique {B : Finset (Fin 64)} (hB : scheme.LocalConfig B) :
    ∀ g ∈ groups, ∃! e, e ∈ g ∧ e ∈ B := by
  intro g hg
  obtain ⟨v, hv, he⟩ := group_anchor g hg
  exact scheme.local_group_unique hB g v hv he


def xyConfigurations : Finset (Finset (Fin 64)) := {{1, 13, 22, 27, 39, 42, 52, 59}, {1, 14, 19, 29, 34, 44, 55, 59}, {3, 11, 17, 26, 38, 45, 55, 60}, {4, 9, 22, 27, 39, 42, 51, 61}, {5, 9, 22, 26, 39, 43, 51, 60}}

def yxConfigurations : Finset (Finset (Fin 64)) := {{5, 14, 17, 26, 36, 47, 48, 56}}

def Certificate (A : Finset (Fin 64)) : Prop :=
  height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = x ∧ scheme.output A = y) ∨
    (scheme.input A = y ∧ scheme.output A = x)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 8, A = classes i) ∧
  ((scheme.input A = x ∧ scheme.output A = y) ↔ A ∈ xyConfigurations) ∧
  ((scheme.input A = y ∧ scheme.output A = x) ↔ A ∈ yxConfigurations)

instance (A : Finset (Fin 64)) : Decidable (Certificate A) := inferInstanceAs (Decidable
  (height (scheme.input A) ≤ height (scheme.output A) ∧
  (height (scheme.input A) = height (scheme.output A) →
    scheme.input A = scheme.output A ∨
    (scheme.input A = x ∧ scheme.output A = y) ∨
    (scheme.input A = y ∧ scheme.output A = x)) ∧
  (scheme.input A = scheme.output A → ∃ i : Fin 8, A = classes i) ∧
  ((scheme.input A = x ∧ scheme.output A = y) ↔ A ∈ xyConfigurations) ∧
  ((scheme.input A = y ∧ scheme.output A = x) ↔ A ∈ yxConfigurations)))

def part (v : Fin 24) : Fin 3 := ⟨v.val / 8, by omega⟩

theorem part_size : ∀ i, (Finset.univ.filter (fun v => part v = i)).card = 8 := by decide


theorem edge_part : ∀ e i, ((scheme.edge e).filter (fun v => part v = i)).card = 1 := by decide


theorem base_linear : ∀ e f, e ≠ f → ((scheme.edge e) ∩ (scheme.edge f)).card ≤ 1 := by
  intro e
  fin_cases e <;> decide


end RigidGHZ.Supplement.Periodic.Latin
