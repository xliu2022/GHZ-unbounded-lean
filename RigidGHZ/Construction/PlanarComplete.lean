module

public import RigidGHZ.Construction.PlanarFactor
public import RigidGHZ.Construction.PlanarSites
public import RigidGHZ.Construction.PlanarSupport
public import RigidGHZ.Construction.GrowthAssembly
public import RigidGHZ.RelabelGround

/-! The unconditional planar factor and its support product. -/

@[expose] public section

namespace RigidGHZ.Planar

open Rectangle

def SupportedPlanarFactor (k T m : ℕ) : Prop :=
  ∃ H : Hypergraph (Fin 3 × Fin m), ∃ U : Finset (Fin m),
    Uniform H 3 ∧ BalancedPartite H 3 m ∧ Nonempty (RigidFamily H (Fin (T + 1))) ∧
    (∀ e ∈ H, ∃ x : Fin 3 → Fin m, e = tupleEdge x) ∧
    (∀ x : Fin 3 → Fin m, tupleEdge x ∈ H →
      (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) ∧ k * U.card ≤ m

/-- Proposition A.3 with an equivalent squared integral size hypothesis. -/
theorem planar_factor {k T m : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T) (hTupper : T ≤ 224 ^ 2)
    (hm : (128 * k ^ 3) ^ 2 * T ^ 7 < m ^ 2) : SupportedPlanarFactor k T m := by
  classical
  let w := width k T
  let h := (m - 1) / w
  let ρ := (m - 1) % w
  have hchoice := choose_box_height hk hT hTupper hm
  have hheight : minimumHeight k T ≤ h := hchoice.1
  have hρ : ρ < w := hchoice.2.1
  have hsize : w * h + ρ + 1 = m := hchoice.2.2
  have hh : 4 * gamma T + auxiliaryHeight T ≤ h := minimumHeight_lower hheight
  have hw : 4 * T ≤ w := by dsimp [w, width, multiplier]; nlinarith
  let R := privateBudget k T - ρ
  have hR := private_remainder_positive hk hT hρ
  have hRpos : 0 < R := hR.1
  obtain ⟨Z, hZ, hZcard⟩ := choose_private_holes hk hT hheight (Nat.sub_le (privateBudget k T) ρ)
  have hZpos : Z.Nonempty := Finset.card_pos.mp (by rw [hZcard]; exact hRpos)
  let X := sourceWithRemainder w h ρ
  have hfull : box 0 (32 * k * (T + 1)) 0 h ⊆ X := sourceWithRemainder_full w h ρ
  have hX : X ⊆ projectionEnvelope (32 * k * (T + 1)) h := sourceWithRemainder_subset hρ.le
  have hZR : Z.card + ρ + 1 = (T + 1) * gamma T + 32 * k * (T + 1) := by
    rw [hZcard]
    exact hR.2
  have hcard : (tagRegion (32 * k * (T + 1)) h T \ (primaryOne (32 * k * (T + 1)) h T ∪ primaryTwo T ∪ Z)).card = X.card + 1 := by
    rw [remaining_tags_card (p := 32 * k) hT (by omega) hw hh Z hZ hZR]
    rw [show X.card = w * h + ρ from sourceWithRemainder_card w h ρ]
    rfl
  obtain ⟨H, hU, hP, ⟨G⟩, htrans, hsupp⟩ := planar_factor_of_arrangement hT hw hh X Z hfull hX hZ hZpos hcard
  let U := physicalSupport w h T X Z
  have harea : w * h < m := by omega
  have hbound : k * U.card ≤ m := by
    apply Nat.le_of_lt
    exact physicalSupport_small hk hT hTupper hh hm harea X Z (by rw [hZcard]; exact Nat.sub_le _ _)
  have hcW : Fintype.card (Option ↥X) = m := by
    simpa only [Fintype.card_option, Fintype.card_coe, X, sourceWithRemainder_card] using hsize
  let f : Option ↥X ≃ Fin m := Fintype.equivOfCardEq (hcW.trans (Fintype.card_fin m).symm)
  let e := Equiv.prodCongr (Equiv.refl (Fin 3)) f
  let H' := relabelHypergraph e H
  let U' := relabelEdge f U
  have ht' := ground_relabel_transversal f H htrans
  refine ⟨H', U', hU.relabel e, ?_, ⟨G.relabel e⟩, ht', ground_relabel_support f H U hsupp, ?_⟩
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal H' ht'
  · simpa only [U', relabelEdge_card] using hbound

theorem planar_product {k T m : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T) (hTupper : T ≤ 224 ^ 2)
    (hm : (128 * k ^ 3) ^ 2 * T ^ 7 < m ^ 2) :
    Growth.ExistsRigid (k + 2) m ((T + 1) ^ k) := by
  obtain ⟨H, U, hU, hP, ⟨G⟩, htrans, hsupp, hbound⟩ := planar_factor hk hT hTupper hm
  exact Growth.product_of_factor_card (by simp) (by simp) H G U hbound htrans hsupp

end RigidGHZ.Planar
