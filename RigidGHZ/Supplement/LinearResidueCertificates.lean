module

public import RigidGHZ.Supplement.ThresholdArithmetic

/-! Exact residue representatives and decompositions from Supplement S7.
Every congruence, maximum bound and use of an allowed increment is checked
by the Lean kernel on the displayed finite tables. -/

@[expose] public section

namespace RigidGHZ.Supplement.LinearResidues

def rows8 : Fin 7 → List ℕ :=
  ![[], [29], [23], [38], [25], [19], [20]]

def increments8 : Finset ℕ := {7, 19, 20, 23, 25, 29, 38}

theorem rows8_mod : ∀ i, (rows8 i).sum % 7 = i.val := by decide +kernel

theorem rows8_max : ∀ i, (rows8 i).sum ≤ 38 := by decide +kernel

theorem rows8_attains_max : ∃ i, (rows8 i).sum = 38 := by decide +kernel

theorem rows8_allowed : ∀ i, (rows8 i).toFinset ⊆ increments8 := by decide +kernel

def rows9 : Fin 21 → List ℕ :=
  ![[], [43], [65], [45], [25], [68], [32, 37], [25, 45], [50], [51], [73], [32], [33], [76], [56], [57], [37], [38], [81], [61], [25, 37]]

def increments9 : Finset ℕ := {21, 25, 32, 33, 37, 38, 43, 45, 50, 51, 56, 57, 61, 65, 68, 73, 76, 81}

theorem rows9_mod : ∀ i, (rows9 i).sum % 21 = i.val := by decide +kernel

theorem rows9_max : ∀ i, (rows9 i).sum ≤ 81 := by decide +kernel

theorem rows9_attains_max : ∃ i, (rows9 i).sum = 81 := by decide +kernel

theorem rows9_allowed : ∀ i, (rows9 i).toFinset ⊆ increments9 := by decide +kernel

def rows10 : Fin 25 → List ℕ :=
  ![[], [51], [77], [33, 45], [54], [37, 43], [56], [32], [33], [84], [85], [61], [37], [38], [64], [65], [33, 33], [67], [43], [32, 37], [45], [33, 38], [32, 65], [73], [37, 37]]

def increments10 : Finset ℕ := {25, 32, 33, 37, 38, 43, 45, 51, 54, 56, 61, 64, 65, 67, 73, 77, 84, 85}

theorem rows10_mod : ∀ i, (rows10 i).sum % 25 = i.val := by decide +kernel

theorem rows10_max : ∀ i, (rows10 i).sum ≤ 97 := by decide +kernel

theorem rows10_attains_max : ∃ i, (rows10 i).sum = 97 := by decide +kernel

theorem rows10_allowed : ∀ i, (rows10 i).toFinset ⊆ increments10 := by decide +kernel

def rows11 : Fin 37 → List ℕ :=
  ![[], [38], [38, 38], [77], [115], [116], [56, 61], [57, 61], [45], [38, 45], [57, 64], [45, 77], [86], [38, 86], [51], [38, 51], [90], [91], [92], [56], [57], [38, 57], [45, 51], [57, 77], [61], [38, 61], [137], [64], [38, 64], [103], [38, 103], [68], [38, 68], [51, 56], [51, 57], [45, 64], [56, 91]]

def increments11 : Finset ℕ := {37, 38, 45, 51, 56, 57, 61, 64, 68, 77, 86, 90, 91, 92, 103, 115, 116, 137}

theorem rows11_mod : ∀ i, (rows11 i).sum % 37 = i.val := by decide +kernel

theorem rows11_max : ∀ i, (rows11 i).sum ≤ 147 := by decide +kernel

theorem rows11_attains_max : ∃ i, (rows11 i).sum = 147 := by decide +kernel

theorem rows11_allowed : ∀ i, (rows11 i).toFinset ⊆ increments11 := by decide +kernel

def rows12 : Fin 38 → List ℕ :=
  ![[], [77], [116], [56, 61], [57, 61], [51, 68], [45, 75], [45], [45, 77], [123], [86], [57, 68], [51, 75], [51], [90], [91], [92], [45, 86], [56], [57], [45, 51], [45, 90], [45, 91], [61], [61, 77], [45, 56], [64], [103], [142], [51, 92], [68], [51, 56], [51, 57], [45, 64], [45, 103], [57, 92], [51, 61], [75]]

def increments12 : Finset ℕ := {38, 45, 51, 56, 57, 61, 64, 68, 75, 77, 86, 90, 91, 92, 103, 116, 123, 142}

theorem rows12_mod : ∀ i, (rows12 i).sum % 38 = i.val := by decide +kernel

theorem rows12_max : ∀ i, (rows12 i).sum ≤ 149 := by decide +kernel

theorem rows12_attains_max : ∃ i, (rows12 i).sum = 149 := by decide +kernel

theorem rows12_allowed : ∀ i, (rows12 i).toFinset ⊆ increments12 := by decide +kernel

end RigidGHZ.Supplement.LinearResidues
