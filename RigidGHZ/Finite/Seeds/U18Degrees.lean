module

public import RigidGHZ.Finite.Seeds.U18Data
public import RigidGHZ.Finite.ExactCoverDegrees

/-! Actual edge counts and maximum pair-codegree of the printed U18 seed. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.U18
open RigidGHZ.UpperBounds RigidGHZ.Supplement
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem edge_count : data.host.card = 78 := by
  rw [ExactCoverData.host, Finset.card_image_of_injective _ valid.injective]
  simp

theorem matching_edge_count (r : Fin 13) : (data.matching r).card = 6 := by
  have h := (valid.perfect r).card_mul_eq uniform
  simp only [Fintype.card_fin] at h
  omega

theorem pair_index_0 : ∀ b : Fin 18, (0 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({0,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_1 : ∀ b : Fin 18, (1 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({1,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_2 : ∀ b : Fin 18, (2 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({2,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_3 : ∀ b : Fin 18, (3 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({3,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_4 : ∀ b : Fin 18, (4 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({4,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_5 : ∀ b : Fin 18, (5 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({5,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_6 : ∀ b : Fin 18, (6 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({6,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_7 : ∀ b : Fin 18, (7 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({7,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_8 : ∀ b : Fin 18, (8 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({8,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_9 : ∀ b : Fin 18, (9 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({9,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_10 : ∀ b : Fin 18, (10 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({10,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_11 : ∀ b : Fin 18, (11 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({11,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_12 : ∀ b : Fin 18, (12 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({12,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_13 : ∀ b : Fin 18, (13 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({13,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_14 : ∀ b : Fin 18, (14 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({14,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_15 : ∀ b : Fin 18, (15 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({15,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_16 : ∀ b : Fin 18, (16 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({16,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_index_17 : ∀ b : Fin 18, (17 : Fin 18) ≠ b →
    ((Finset.univ : Finset (Fin 78)).filter
      (fun i => ({17,b} : Finset (Fin 18)) ⊆ data.edge i)).card ≤ 4 := by
  decide +kernel

theorem pair_certificate (a b : Fin 18) (hab : a ≠ b) :
    codegree data.host {a,b} ≤ 4 := by
  rw [exactCover_codegree_of_indices data valid.injective]
  revert b
  fin_cases a
  · exact pair_index_0
  · exact pair_index_1
  · exact pair_index_2
  · exact pair_index_3
  · exact pair_index_4
  · exact pair_index_5
  · exact pair_index_6
  · exact pair_index_7
  · exact pair_index_8
  · exact pair_index_9
  · exact pair_index_10
  · exact pair_index_11
  · exact pair_index_12
  · exact pair_index_13
  · exact pair_index_14
  · exact pair_index_15
  · exact pair_index_16
  · exact pair_index_17

theorem max_pair : maxDegree data.host 2 = 4 := by
  apply Nat.le_antisymm
  · apply maxDegree_le
    intro X hX
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hX
    exact pair_certificate a b hab
  · have hc : codegree data.host ({0,10} : Finset (Fin 18)) = 4 := by
      rw [exactCover_codegree_of_indices data valid.injective]
      decide +kernel
    have hcard : ({0,10} : Finset (Fin 18)).card = 2 := by decide
    have h := codegree_le_maxDegree data.host ({0,10} : Finset (Fin 18))
    simpa only [hc,hcard] using h

end RigidGHZ.Finite.Seeds.U18
