module

public import RigidGHZ.Construction.PlanarBlockModel

/-! Count the actual active support in the planar hypergraph assembly. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

theorem liftLatticeSet_card_le (X S : Finset Lattice) : (liftLatticeSet X S).card ≤ S.card := by
  simp only [liftLatticeSet, Finset.card_map, Finset.card_subtype]
  exact Finset.card_filter_le _ _

theorem owners_subset_envelopes {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    owners w h p ⊆ firstOwnerEnvelope w h T ∪ secondOwnerEnvelope T := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨b, hb, hx⟩ := leftOwners_hit p hx
    apply Finset.mem_union_left
    apply primaryOne_owners_subset (by omega) (by omega)
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_range.mpr (by omega), hx⟩
  · obtain ⟨b, hb, hx⟩ := rightOwners_hit p hx
    apply Finset.mem_union_right
    apply primaryTwo_owners_subset (w := w) (h := h) hw (by omega)
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_range.mpr (by omega), hx⟩

def privateOwnerUnion (Z : Finset Lattice) (T : ℕ) : Finset Lattice :=
  (Finset.univ : Finset (Fin (T + 1))).biUnion (fun b => inverseSet Z b.val)

theorem privateOwnerUnion_card_le (Z : Finset Lattice) (T : ℕ) :
    (privateOwnerUnion Z T).card ≤ (T + 1) * Z.card := by
  have hc := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin (T + 1))))
    (t := fun b => inverseSet Z b.val)
  simpa [privateOwnerUnion] using hc

theorem physicalSupport_card_le {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (X Z : Finset Lattice) :
    (physicalSupport w h T X Z).card ≤
      2 * T * h + 2 * gamma T * (w - T) + 2 * T * auxiliaryHeight T + (T + 1) * Z.card + 1 := by
  let S := firstOwnerEnvelope w h T ∪ secondOwnerEnvelope T ∪ privateOwnerUnion Z T
  have hsub : physicalSupport w h T X Z ⊆ insert none (liftLatticeSet X S) := by
    intro x hx
    obtain ⟨v, hv, hx⟩ := Finset.mem_biUnion.mp hx
    change x ∈ indexedBlocks w h X Z (blockKeyEquiv T v) at hx
    cases hk : blockKeyEquiv T v with
    | none =>
      rw [hk] at hx
      have he : x = none := Finset.mem_singleton.mp hx
      rw [he]
      exact Finset.mem_insert_self _ _
    | some a =>
      rw [hk] at hx
      cases a with
      | inl q =>
        cases x with
        | none => exact Finset.mem_insert_self _ _
        | some x =>
          apply Finset.mem_insert_of_mem
          apply (some_mem_liftLatticeSet X S x).mpr
          exact Finset.mem_union_left _ (owners_subset_envelopes hw hh q ((some_mem_liftLatticeSet X _ x).mp hx))
      | inr b =>
        cases x with
        | none => exact Finset.mem_insert_self _ _
        | some x =>
          apply Finset.mem_insert_of_mem
          apply (some_mem_liftLatticeSet X S x).mpr
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, (some_mem_liftLatticeSet X _ x).mp hx⟩
  have hc : (physicalSupport w h T X Z).card ≤
      (firstOwnerEnvelope w h T).card + (secondOwnerEnvelope T).card + (T + 1) * Z.card + 1 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le none (liftLatticeSet X S)
    have h3 := liftLatticeSet_card_le X S
    have h4 := Finset.card_union_le (firstOwnerEnvelope w h T ∪ secondOwnerEnvelope T) (privateOwnerUnion Z T)
    have h5 := Finset.card_union_le (firstOwnerEnvelope w h T) (secondOwnerEnvelope T)
    have h6 := privateOwnerUnion_card_le Z T
    dsimp [S] at h1 h2 h3
    omega
  have hc' : ((physicalSupport w h T X Z).card : ℤ) ≤
      (firstOwnerEnvelope w h T).card + (secondOwnerEnvelope T).card + (T + 1) * (Z.card : ℤ) + 1 := by
    exact_mod_cast hc
  rw [firstOwnerEnvelope_card (by omega), secondOwnerEnvelope_card] at hc'
  have hwT : ((w - T : ℕ) : ℤ) = (w : ℤ) - T := by omega
  suffices ((physicalSupport w h T X Z).card : ℤ) ≤
      (2 * T * h + 2 * gamma T * (w - T) + 2 * T * auxiliaryHeight T + (T + 1) * Z.card + 1 : ℕ) by
    exact_mod_cast this
  push_cast
  rw [hwT]
  nlinarith

theorem physicalSupport_small {k h T m : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hTupper : T ≤ 224 ^ 2) (hh : 4 * gamma T + auxiliaryHeight T ≤ h)
    (hm : (128 * k ^ 3) ^ 2 * T ^ 7 < m ^ 2) (hsize : width k T * h < m)
    (X Z : Finset Lattice) (hZ : Z.card ≤ privateBudget k T) :
    k * (physicalSupport (width k T) h T X Z).card < m := by
  have hw : 4 * T ≤ width k T := by unfold width multiplier; nlinarith
  have hc := physicalSupport_card_le hw hh X Z
  have hbudget := Nat.mul_le_mul_left (T + 1) hZ
  have hu : ((physicalSupport (width k T) h T X Z).card : ℝ) ≤
      2 * (T : ℝ) * h + PlanarEstimates.supportRest k T := by
    have hc' : ((physicalSupport (width k T) h T X Z).card : ℝ) ≤
        2 * T * h + 2 * (gamma T : ℝ) * (width k T - T : ℕ) +
          2 * T * (auxiliaryHeight T : ℝ) + (T + 1) * (privateBudget k T : ℝ) + 1 := by
      exact_mod_cast (hc.trans (by omega))
    have hwsub : ((width k T - T : ℕ) : ℝ) = (width k T : ℝ) - T := by
      rw [Nat.cast_sub (by omega)]
    rw [hwsub, width_cast, gamma_cast_real, auxiliaryHeight_cast (by omega), privateBudget_cast hk] at hc'
    simpa only [PlanarEstimates.supportRest, add_assoc] using hc'
  have hs : PlanarEstimates.width k T * (h : ℝ) < m := by
    rw [← width_cast]
    exact_mod_cast hsize
  have hf := PlanarEstimates.active_support_lt (by exact_mod_cast hk) (by exact_mod_cast hT)
    (by exact_mod_cast hTupper) (Nat.cast_nonneg h) hs (growthScale_lt_of_squared hm) hu
  exact_mod_cast hf

end RigidGHZ.Planar
