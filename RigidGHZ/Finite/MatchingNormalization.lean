module

public import RigidGHZ.Finite.NineEnumeration
public import RigidGHZ.Finite.PairNormalization

/-!
# Normalizing the matching through edge 012

The following small tables fix vertices 0,1,2 and independently permute the
remaining pair-completion vertices and their complement. All table facts,
including the matching images, are checked by ordinary kernel `decide`.
-/

@[expose] public section

namespace RigidGHZ.Finite

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem partition012_first : ∀ j : Fin 280,
    ({0, 1, 2} : Finset (Fin 9)) ∈ ninePartition j → j.val < 10 := by
  decide

def matchingMap4 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,7,6,8],
  ![0,1,2,3,4,5,7,8,6],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,3,5,4,7,6,8],
  ![0,1,2,3,5,4,7,8,6],
  ![0,1,2,5,3,4,7,8,6],
  ![0,1,2,5,3,4,7,6,8],
  ![0,1,2,5,3,4,6,7,8]]

def matchingInv4 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,7,6,8],
  ![0,1,2,3,4,5,8,6,7],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,3,5,4,7,6,8],
  ![0,1,2,3,5,4,8,6,7],
  ![0,1,2,4,5,3,8,6,7],
  ![0,1,2,4,5,3,7,6,8],
  ![0,1,2,4,5,3,6,7,8]]

theorem matchingInverse4 : ∀ j : Fin 10,
    (∀ x, matchingInv4 j (matchingMap4 j x) = x) ∧
    (∀ x, matchingMap4 j (matchingInv4 j x) = x) := by
  decide

def matchingPerm4 (j : Fin 10) : Equiv.Perm (Fin 9) where
  toFun := matchingMap4 j
  invFun := matchingInv4 j
  left_inv := (matchingInverse4 j).1
  right_inv := (matchingInverse4 j).2

theorem matchingPerm4_facts : ∀ j : Fin 10,
    matchingPerm4 j 0 = 0 ∧ matchingPerm4 j 1 = 1 ∧ matchingPerm4 j 2 = 2 ∧
    (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 6) ↔
      (2 ≤ (matchingPerm4 j x).val ∧ (matchingPerm4 j x).val < 6)) ∧
    (relabelHypergraph (matchingPerm4 j) (ninePartition ⟨j.val, by omega⟩) = {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}} ∨
     relabelHypergraph (matchingPerm4 j) (ninePartition ⟨j.val, by omega⟩) = {{0, 1, 2}, {3, 4, 6}, {5, 7, 8}}) := by
  decide

theorem normalize_matching4 {H M : Hypergraph (Fin 9)}
    (hH : Uniform H 3) (hM : PerfectMatching H M)
    (h012 : ({0, 1, 2} : Finset (Fin 9)) ∈ M) :
    ∃ g : Equiv.Perm (Fin 9), g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 ∧
      (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 6) ↔
        (2 ≤ (g x).val ∧ (g x).val < 6)) ∧
      (relabelHypergraph g M = {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}} ∨
       relabelHypergraph g M = {{0, 1, 2}, {3, 4, 6}, {5, 7, 8}}) := by
  obtain ⟨j, rfl⟩ := ninePartition_complete hH hM
  let j' : Fin 10 := ⟨j.val, partition012_first j h012⟩
  have h := matchingPerm4_facts j'
  refine ⟨matchingPerm4 j', ?_⟩
  simpa only [j'] using h

def matchingMap5 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,4,5,6,3,7,8],
  ![0,1,2,4,5,3,6,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,6,8,7],
  ![0,1,2,4,3,5,6,7,8],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,3,5,4,6,8,7],
  ![0,1,2,3,5,6,4,7,8],
  ![0,1,2,3,5,6,4,8,7],
  ![0,1,2,3,4,5,6,7,8]]

def matchingInv5 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,6,3,4,5,7,8],
  ![0,1,2,5,3,4,6,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,3,4,5,6,8,7],
  ![0,1,2,4,3,5,6,7,8],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,3,5,4,6,8,7],
  ![0,1,2,3,6,4,5,7,8],
  ![0,1,2,3,6,4,5,8,7],
  ![0,1,2,3,4,5,6,7,8]]

theorem matchingInverse5 : ∀ j : Fin 10,
    (∀ x, matchingInv5 j (matchingMap5 j x) = x) ∧
    (∀ x, matchingMap5 j (matchingInv5 j x) = x) := by
  decide

def matchingPerm5 (j : Fin 10) : Equiv.Perm (Fin 9) where
  toFun := matchingMap5 j
  invFun := matchingInv5 j
  left_inv := (matchingInverse5 j).1
  right_inv := (matchingInverse5 j).2

theorem matchingPerm5_facts : ∀ j : Fin 10,
    matchingPerm5 j 0 = 0 ∧ matchingPerm5 j 1 = 1 ∧ matchingPerm5 j 2 = 2 ∧
    (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 7) ↔
      (2 ≤ (matchingPerm5 j x).val ∧ (matchingPerm5 j x).val < 7)) ∧
    (relabelHypergraph (matchingPerm5 j) (ninePartition ⟨j.val, by omega⟩) = {{0, 1, 2}, {3, 7, 8}, {4, 5, 6}} ∨
     relabelHypergraph (matchingPerm5 j) (ninePartition ⟨j.val, by omega⟩) = {{0, 1, 2}, {3, 4, 7}, {5, 6, 8}}) := by
  decide

theorem normalize_matching5 {H M : Hypergraph (Fin 9)}
    (hH : Uniform H 3) (hM : PerfectMatching H M)
    (h012 : ({0, 1, 2} : Finset (Fin 9)) ∈ M) :
    ∃ g : Equiv.Perm (Fin 9), g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 ∧
      (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 7) ↔
        (2 ≤ (g x).val ∧ (g x).val < 7)) ∧
      (relabelHypergraph g M = {{0, 1, 2}, {3, 7, 8}, {4, 5, 6}} ∨
       relabelHypergraph g M = {{0, 1, 2}, {3, 4, 7}, {5, 6, 8}}) := by
  obtain ⟨j, rfl⟩ := ninePartition_complete hH hM
  let j' : Fin 10 := ⟨j.val, partition012_first j h012⟩
  have h := matchingPerm5_facts j'
  refine ⟨matchingPerm5 j', ?_⟩
  simpa only [j'] using h

def matchingMap6 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,5,6,7,3,4,8],
  ![0,1,2,5,6,3,7,4,8],
  ![0,1,2,5,6,3,4,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,5,3,6,7,4,8],
  ![0,1,2,5,3,6,4,7,8],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,5,3,4,6,7,8],
  ![0,1,2,3,5,6,4,7,8],
  ![0,1,2,3,5,6,7,4,8]]

def matchingInv6 : Fin 10 → Fin 9 → Fin 9 :=
  ![![0,1,2,6,7,3,4,5,8],
  ![0,1,2,5,7,3,4,6,8],
  ![0,1,2,5,6,3,4,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![0,1,2,4,7,3,5,6,8],
  ![0,1,2,4,6,3,5,7,8],
  ![0,1,2,3,5,4,6,7,8],
  ![0,1,2,4,5,3,6,7,8],
  ![0,1,2,3,6,4,5,7,8],
  ![0,1,2,3,7,4,5,6,8]]

theorem matchingInverse6 : ∀ j : Fin 10,
    (∀ x, matchingInv6 j (matchingMap6 j x) = x) ∧
    (∀ x, matchingMap6 j (matchingInv6 j x) = x) := by
  decide

def matchingPerm6 (j : Fin 10) : Equiv.Perm (Fin 9) where
  toFun := matchingMap6 j
  invFun := matchingInv6 j
  left_inv := (matchingInverse6 j).1
  right_inv := (matchingInverse6 j).2

theorem matchingPerm6_facts : ∀ j : Fin 10,
    matchingPerm6 j 0 = 0 ∧ matchingPerm6 j 1 = 1 ∧ matchingPerm6 j 2 = 2 ∧
    (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 8) ↔
      (2 ≤ (matchingPerm6 j x).val ∧ (matchingPerm6 j x).val < 8)) ∧
    (relabelHypergraph (matchingPerm6 j) (ninePartition ⟨j.val, by omega⟩) = {{0, 1, 2}, {3, 4, 8}, {5, 6, 7}}) := by
  decide

theorem normalize_matching6 {H M : Hypergraph (Fin 9)}
    (hH : Uniform H 3) (hM : PerfectMatching H M)
    (h012 : ({0, 1, 2} : Finset (Fin 9)) ∈ M) :
    ∃ g : Equiv.Perm (Fin 9), g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 ∧
      (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 8) ↔
        (2 ≤ (g x).val ∧ (g x).val < 8)) ∧
      (relabelHypergraph g M = {{0, 1, 2}, {3, 4, 8}, {5, 6, 7}}) := by
  obtain ⟨j, rfl⟩ := ninePartition_complete hH hM
  let j' : Fin 10 := ⟨j.val, partition012_first j h012⟩
  have h := matchingPerm6_facts j'
  refine ⟨matchingPerm6 j', ?_⟩
  simpa only [j'] using h

end RigidGHZ.Finite
