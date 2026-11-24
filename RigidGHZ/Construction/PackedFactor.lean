module

public import RigidGHZ.Construction.PackedSupport
public import RigidGHZ.Construction.PackedDemands
public import RigidGHZ.RelabelGround

/-! Complete geometric realization of the rectangular factor from natural
packing, demand, and exact area data. -/

@[expose] public section

namespace RigidGHZ.Rectangle.PackedLayout

open RectangleAnchors

variable {T B H : ℕ} (s : PackedLayout T B H)

 theorem holes_disjoint_private (Z : Finset Point3)
    (hafter : ∀ z ∈ Z, (s.totalLevels * (T + 1) : ℕ) + (T : ℤ) + 1 ≤ z.1) :
    Disjoint (primaryHoles s.rectangles) Z := by
  apply Finset.disjoint_left.mpr
  intro x hx hz
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
  have hplane := s.plane_upper a
  have hafter := hafter x hz
  simp only [PrimaryRectangle.hole, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico] at hxa
  omega

/-- Finite geometric construction of the rectangular factor. The inputs are
only explicit natural inequalities and exact area balance; all graph, matching,
anchor, and support conclusions are constructed and proved. -/
theorem factor_of_counts {A Px Py R ρ : ℕ}
    (hT : 1 ≤ T) (hB : 2 * T < B) (hH : 3 * gamma T < H)
    (hL : s.ns ≠ 0 → gamma T ≤ s.L)
    (hnh : 0 < s.nh) (hnf : 0 < s.nf)
    (hA : s.totalLevels * (T + 1) < A)
    (hx : Px * (T + 1) < A) (hy : Py * (T + 1) < B)
    (hR : 0 < R) (hRcap : R ≤ (Px - s.totalLevels) * Py * (H - 2 * gamma T))
    (hρ : ρ ≤ A * B)
    (hfull : s.fullDemand ≤ T * B * H + A * B * gamma T)
    (hproper : ∀ l : Fin T, s.properDemand l.val ≤ A * H + A * B * l.val)
    (hbalance : (A + T) * (B + T) * (H + 2 * gamma T + 1) =
      s.area + R + (A * B * H + ρ + 1)) :
    ∃ G : Hypergraph (Fin 3 × Fin (A * B * H + ρ + 1)),
      ∃ U : Finset (Fin (A * B * H + ρ + 1)),
      Uniform G 3 ∧ BalancedPartite G 3 (A * B * H + ρ + 1) ∧
      Nonempty (RigidFamily G (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ G, ∃ x : Fin 3 → Fin (A * B * H + ρ + 1), e = tupleEdge x) ∧
      (∀ x : Fin 3 → Fin (A * B * H + ρ + 1), tupleEdge x ∈ G →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) ∧
      U.card ≤ 1 + (T + 1) * s.totalLevels * B * H + (T + 1) ^ 2 * R := by
  classical
  obtain ⟨X, hfullX, hXenv, hXcard⟩ := source_with_remainder (H := H) hρ
  obtain ⟨Z, hZcard, hZbox, hgrid, hafter⟩ := private_holes_exist hx hy hRcap
  have hZpos : Z.Nonempty := Finset.card_pos.mp (by rwa [hZcard])
  have hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock s.rectangles i p ⊆ X := by
    intro i p x hx
    apply hfullX
    have hb := s.ownerBlock_in_box hA i p hx
    simp only [fullSourceBox, box, Finset.mem_product, Finset.mem_Ico]
    tauto
  have hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X := by
    intro i b
    exact (privateBlock_subset_fullSource Z hZbox i b).trans hfullX
  have hholes : primaryHoles s.rectangles ∪ Z ⊆ holeBox A B H T :=
    Finset.union_subset (s.holes_in_box hA) hZbox
  have hdisj := s.holes_disjoint_private Z hafter
  have hcard : (tagBox A B H T \ (primaryHoles s.rectangles ∪ Z)).card = X.card + 1 := by
    rw [Finset.card_sdiff_of_subset (hholes.trans (holeBox_subset_tagBox A B H T)),
      tagBox_card, Finset.card_union_of_disjoint hdisj, s.holes_card, hZcard, hXcard]
    omega
  obtain ⟨G, hUG, hPG, ⟨RG⟩, htrans, hsupport⟩ := rectangular_factor_of_arrangement
    s.rectangles X Z s.plane_multiple s.separated hgrid s.plane_upper hafter
    hownerX hprivateX (s.ownerBlock_nonempty hT hB hH hnh hnf) hZpos hXenv hholes
    (s.anchor_capacity hT hB.le hH.le hL hfull hproper) hcard
  let f : (Option ↥X) ≃ Fin (A * B * H + ρ + 1) :=
    Fintype.equivFinOfCardEq (by simp only [Fintype.card_option, Fintype.card_coe, hXcard])
  let e := Equiv.prodCongr (Equiv.refl (Fin 3)) f
  let G' := relabelHypergraph e G
  let U' := relabelEdge f (physicalSupport (T := T) s.rectangles X Z)
  have htrans' : ∀ e ∈ G', ∃ x : Fin 3 → Fin (A * B * H + ρ + 1), e = tupleEdge x :=
    ground_relabel_transversal f G htrans
  refine ⟨G', U', hUG.relabel e, ?_, ⟨RG.relabel e⟩, htrans', ?_, ?_⟩
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal G' htrans'
  · exact ground_relabel_support f G _ hsupport
  · change (relabelEdge f (physicalSupport (T := T) s.rectangles X Z)).card ≤ _
    rw [relabelEdge_card]
    simpa only [hZcard] using s.physicalSupport_card_le X Z hgrid

end RigidGHZ.Rectangle.PackedLayout
