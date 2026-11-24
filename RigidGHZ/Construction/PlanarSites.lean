module

public import RigidGHZ.Construction.PlanarOwners

/-! Projection vertices, the remaining tag count, and the positive private budget. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

def sourceWithRemainder (w h ρ : ℕ) : Finset Lattice :=
  box 0 w 0 h ∪ box 0 ρ h (h + 1)

theorem sourceWithRemainder_full (w h ρ : ℕ) : box 0 w 0 h ⊆ sourceWithRemainder w h ρ :=
  Finset.subset_union_left

theorem sourceWithRemainder_subset {w h ρ : ℕ} (hρ : ρ ≤ w) :
    sourceWithRemainder w h ρ ⊆ projectionEnvelope w h := by
  intro x hx
  simp only [sourceWithRemainder, projectionEnvelope, box, Finset.mem_union,
    Finset.mem_product, Finset.mem_Ico] at hx ⊢
  rcases hx with hx | hx <;> omega

theorem sourceWithRemainder_card (w h ρ : ℕ) : (sourceWithRemainder w h ρ).card = w * h + ρ := by
  have hd : Disjoint (box 0 w 0 h) (box 0 ρ h (h + 1)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  have hi : ((sourceWithRemainder w h ρ).card : ℤ) = w * h + ρ := by
    rw [sourceWithRemainder, Finset.card_union_of_disjoint hd, Nat.cast_add,
      box_card_int (by omega) (by omega), box_card_int (by omega) (by omega)]
    ring
  exact_mod_cast hi

theorem privateBudget_identity {k T : ℕ} (hk : 1 ≤ k) :
    privateBudget k T + 1 = (T + 1) * gamma T + width k T := by
  have hw := width_pos (T := T) hk
  unfold privateBudget
  omega

theorem private_remainder_positive {k T ρ : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T) (hρ : ρ < width k T) :
    0 < privateBudget k T - ρ ∧
      privateBudget k T - ρ + ρ + 1 = (T + 1) * gamma T + width k T := by
  have hγ : 1 ≤ gamma T := by
    have h := gamma_mono hT
    change gamma 2 ≤ gamma T at h
    exact h
  have hb := privateBudget_identity (T := T) hk
  have hm := Nat.mul_le_mul_left (T + 1) hγ
  have hρb : ρ ≤ privateBudget k T := by nlinarith
  have hs := Nat.sub_add_cancel hρb
  exact ⟨by omega, by omega⟩

theorem holeEnvelope_subset_projection (w h T : ℕ) : holeEnvelope w h T ⊆ projectionEnvelope w h := by
  intro x hx
  simp only [holeEnvelope, projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

theorem remaining_tags_card {p h T ρ : ℕ} (hT : 2 ≤ T) (hp : 1 ≤ p)
    (hw : 4 * T ≤ p * (T + 1)) (hh : 4 * gamma T + auxiliaryHeight T ≤ h)
    (Z : Finset Lattice) (hZ : Z ⊆ privatePool p h T)
    (hZR : Z.card + ρ + 1 = (T + 1) * gamma T + p * (T + 1)) :
    (tagRegion (p * (T + 1)) h T \ (primaryOne (p * (T + 1)) h T ∪ primaryTwo T ∪ Z)).card =
      p * (T + 1) * h + ρ + 1 := by
  let w := p * (T + 1)
  have hwpos : 1 ≤ w := by dsimp [w]; nlinarith
  have hd12 : Disjoint (primaryOne w h T) (primaryTwo T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact primary_families_separate hw hh
      ⟨0, by omega, mem_inverseSet.mpr (by simpa [translate] using hx)⟩
      ⟨0, by omega, mem_inverseSet.mpr (by simpa [translate] using hy)⟩
  have hdZ : Disjoint (primaryOne w h T ∪ primaryTwo T) Z := by
    apply Finset.disjoint_left.mpr
    intro x hx hz
    have hz' : translate 0 x ∈ privatePool p h T := by simpa [translate] using hZ hz
    rcases Finset.mem_union.mp hx with hx | hx
    · exact private_avoids_first (b := 0) (c := 0) hT (by omega) (by omega) hh hz' (by simpa [translate] using hx)
    · exact private_avoids_second (b := 0) (c := 0) hT (by omega) (by omega) hh hz' (by simpa [translate] using hx)
  have hsub : primaryOne w h T ∪ primaryTwo T ∪ Z ⊆ tagRegion w h T := by
    intro x hx
    have henv : x ∈ holeEnvelope w h T := by
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact primaryOne_subset_holeEnvelope (by omega) (by omega) hx
        · exact primaryTwo_subset_holeEnvelope hw (by omega) hx
      · exact privatePool_subset_holeEnvelope hT hh (hZ hx)
    have hhx := translate_envelope_mem (T := T) (b := 0) (by omega)
      (holeEnvelope_subset_projection w h T henv)
    simpa [translate] using hhx
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint hdZ, Finset.card_union_of_disjoint hd12] at hc
  have hc' : ((tagRegion w h T \ (primaryOne w h T ∪ primaryTwo T ∪ Z)).card : ℤ) +
      ((primaryOne w h T).card + (primaryTwo T).card + (Z.card : ℤ)) = (tagRegion w h T).card := by
    exact_mod_cast hc
  rw [primaryOne_card (by omega) (by omega), primaryTwo_card,
    tagRegion_card hwpos (by have he := geometric_height hT hh; omega)] at hc'
  have hwm1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
  push_cast at hc'
  rw [hwm1] at hc'
  have hg : 2 * (gamma T : ℤ) + T = (T : ℤ) * T := by exact_mod_cast gamma_quadratic T
  have hB : (auxiliaryHeight T : ℤ) = 2 * gamma T - T + 2 := by
    unfold auxiliaryHeight
    have hpred : ((T - 1 : ℕ) : ℤ) = (T : ℤ) - 1 := by omega
    push_cast
    rw [hpred]
    nlinarith
  have hZr : (Z.card : ℤ) + ρ + 1 = (T + 1) * gamma T + w := by exact_mod_cast hZR
  rw [hB] at hc'
  have he : ((tagRegion w h T \ (primaryOne w h T ∪ primaryTwo T ∪ Z)).card : ℤ) =
      (w : ℤ) * h + ρ + 1 := by nlinarith
  exact_mod_cast he

end RigidGHZ.Planar
