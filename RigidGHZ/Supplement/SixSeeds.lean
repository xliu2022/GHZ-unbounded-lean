module

public import RigidGHZ.Finite.TripartiteSix
public import RigidGHZ.Finite.RowChoiceCertificate
public import RigidGHZ.UpperBounds.ShadowCombinatorics

/-!
Finite seeds for Supplementary Theorem S1.4.  Grafting the part-size-three
seed repeatedly to either seed proves every part size at least three.
The part-size-four table is the paper's construction with the cycle
`(0,2,1,3)`.  Every finite check uses kernel-reduced `decide`.
-/

@[expose] public section

namespace RigidGHZ.Supplement.SixSeeds

open UpperBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem three_pair_bound (X : Finset (Fin 9)) (hX : X.card = 2) :
    codegree Finite.sixGraph X ≤ 2 := by
  have h : ∀ X : Finset (Fin 9), X.card = 2 → codegree Finite.sixGraph X ≤ 2 := by
    decide
  exact h X hX

def fourCoordinates : Fin 6 → Fin 3 → Fin 4 → Fin 4 := ![
  ![![0,1,2,3], ![3,0,1,2], ![0,1,2,3]],
  ![![0,1,2,3], ![3,0,1,2], ![2,3,1,0]],
  ![![0,1,2,3], ![0,1,2,3], ![3,0,1,2]],
  ![![0,1,2,3], ![0,1,2,3], ![0,2,3,1]],
  ![![0,1,2,3], ![1,2,3,0], ![1,2,3,0]],
  ![![0,1,2,3], ![1,2,3,0], ![3,1,0,2]]]

def fourGraph : Hypergraph (Fin 3 × Fin 4) := coordinateHypergraph fourCoordinates

theorem four_bijective : ∀ i a, Function.Bijective (fourCoordinates i a) := by decide

theorem four_root : ∀ i w, fourCoordinates i 0 w = w := by decide

theorem four_separate : ∀ i j, i ≠ j → ∀ w,
    ∃ a, fourCoordinates i a w ≠ fourCoordinates j a w := by decide

theorem four_certificate : ∀ c : Fin 4 → Fin 6,
    (∀ a, Function.Injective (fun w => fourCoordinates (c w) a w)) →
    ∃ i, ∀ w a, fourCoordinates (c w) a w = fourCoordinates i a w := by decide

noncomputable def fourFamily : RigidFamily fourGraph (Fin 6) :=
  Finite.rigidFamily_of_row_certificate 0 fourCoordinates four_bijective four_root
    four_separate four_certificate

theorem four_rigid : IsRigid fourGraph 6 := ⟨fourFamily⟩

theorem four_uniform : Uniform fourGraph 3 := coordinateHypergraph_uniform fourCoordinates

theorem four_balanced : BalancedPartite fourGraph 3 4 :=
  coordinateHypergraph_balanced_card fourCoordinates

theorem four_pair_certificate : ∀ a b : Fin 3 × Fin 4, a ≠ b →
    codegree fourGraph {a, b} ≤ 2 := by decide

theorem four_pair_bound (X : Finset (Fin 3 × Fin 4)) (hX : X.card = 2) :
    codegree fourGraph X ≤ 2 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hX
  exact four_pair_certificate a b hab

theorem four_edge_count : fourGraph.card = 24 := by decide

end RigidGHZ.Supplement.SixSeeds
