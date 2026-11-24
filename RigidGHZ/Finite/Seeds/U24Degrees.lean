module

public import RigidGHZ.Finite.Seeds.U24Data
public import RigidGHZ.Finite.ExactCoverDegrees

/-! Actual edge counts and maximum pair-codegree of the printed U24 seed. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.U24
open RigidGHZ.UpperBounds RigidGHZ.Supplement
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem edge_count : data.host.card = 80 := by
  rw [ExactCoverData.host, Finset.card_image_of_injective _ valid.injective]
  simp

theorem matching_edge_count (r : Fin 10) : (data.matching r).card = 8 := by
  have h := (valid.perfect r).card_mul_eq uniform
  simp only [Fintype.card_fin] at h
  omega

theorem pair_index_0 : ∀ b : Fin 24, (0 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({0,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_1 : ∀ b : Fin 24, (1 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({1,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_2 : ∀ b : Fin 24, (2 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({2,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_3 : ∀ b : Fin 24, (3 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({3,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_4 : ∀ b : Fin 24, (4 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({4,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_5 : ∀ b : Fin 24, (5 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({5,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_6 : ∀ b : Fin 24, (6 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({6,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_7 : ∀ b : Fin 24, (7 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({7,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_8 : ∀ b : Fin 24, (8 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({8,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_9 : ∀ b : Fin 24, (9 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({9,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_10 : ∀ b : Fin 24, (10 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({10,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_11 : ∀ b : Fin 24, (11 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({11,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_12 : ∀ b : Fin 24, (12 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({12,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_13 : ∀ b : Fin 24, (13 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({13,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_14 : ∀ b : Fin 24, (14 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({14,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_15 : ∀ b : Fin 24, (15 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({15,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_16 : ∀ b : Fin 24, (16 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({16,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_17 : ∀ b : Fin 24, (17 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({17,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_18 : ∀ b : Fin 24, (18 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({18,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_19 : ∀ b : Fin 24, (19 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({19,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_20 : ∀ b : Fin 24, (20 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({20,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_21 : ∀ b : Fin 24, (21 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({21,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_22 : ∀ b : Fin 24, (22 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({22,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_index_23 : ∀ b : Fin 24, (23 : Fin 24) ≠ b →
    ((Finset.univ : Finset (Fin 80)).filter
      (fun i => ({23,b} : Finset (Fin 24)) ⊆ data.edge i)).card ≤ 3 := by
  decide +kernel

theorem pair_certificate (a b : Fin 24) (hab : a ≠ b) :
    codegree data.host {a,b} ≤ 3 := by
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
  · exact pair_index_18
  · exact pair_index_19
  · exact pair_index_20
  · exact pair_index_21
  · exact pair_index_22
  · exact pair_index_23

theorem max_pair : maxDegree data.host 2 = 3 := by
  apply Nat.le_antisymm
  · apply maxDegree_le
    intro X hX
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hX
    exact pair_certificate a b hab
  · have hc : codegree data.host ({4,6} : Finset (Fin 24)) = 3 := by
      rw [exactCover_codegree_of_indices data valid.injective]
      decide +kernel
    have hcard : ({4,6} : Finset (Fin 24)).card = 2 := by decide
    have h := codegree_le_maxDegree data.host ({4,6} : Finset (Fin 24))
    simpa only [hc,hcard] using h

end RigidGHZ.Finite.Seeds.U24
