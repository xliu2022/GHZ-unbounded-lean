module

public import RigidGHZ.Construction.PackedSupport

/-! Exact cardinalities of the physical owner blocks and the active support. -/

@[expose] public section

namespace RigidGHZ.Rectangle

open Selector Selector.DoubleComb

 theorem owner_patterns_cover (W J T : ℕ) :
    (Finset.univ : Finset (Pattern T)).biUnion (fun p => p.owners W J) =
      rectangleUnion W J T := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hx
    exact p.owners_subset_union hp
  · intro hx
    obtain ⟨p, hp, _⟩ := owner_pattern_unique hx
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hp⟩

 theorem owner_patterns_card (W J T : ℕ) :
    (∑ p : Pattern T, (p.owners W J).card) = (rectangleUnion W J T).card := by
  rw [← owner_patterns_cover W J T]
  symm
  apply Finset.card_biUnion
  intro p hp q hq hpq
  exact Pattern.owners_disjoint hpq

variable {K : Type*} [Fintype K] [DecidableEq K] {T : ℕ}
    (r : K → PrimaryRectangle) (X Z : Finset Point3)

/-- Every vertex in the displayed support belongs to exactly one actual chain
block. This formula counts that support itself, including the hub. -/
theorem physicalSupport_card
    (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    {P : ℕ} (hplanes : ∀ k, (r k).plane ≤ P)
    (hZafter : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock r i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X) :
    (physicalSupport (T := T) r X Z).card =
      1 + (T + 1) * (∑ k, (rectangleUnion (r k).width (r k).height T).card) +
        (T + 1) ^ 2 * Z.card := by
  have hd : (↑(Finset.univ : Finset (Vertex (Fin (T + 1)) T)) :
      Set (Vertex (Fin (T + 1)) T)).PairwiseDisjoint (physicalBlocks r X Z) := by
    intro v hv w hw hvw
    exact physicalBlocks_disjoint r X Z hprimary hsep hgrid hplanes hZafter hvw
  rw [physicalSupport, Finset.card_biUnion hd]
  change (∑ v, (indexedBlocks r X Z (blockKeyEquiv T v)).card) = _
  rw [(blockKeyEquiv T).sum_comp (fun a => (indexedBlocks r X Z a).card)]
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type,
    indexedBlocks, Finset.card_singleton, liftLatticeSet_card X _ (hownerX _ _),
    liftLatticeSet_card X _ (hprivateX _ _), privateBlock_card]
  simp_rw [ownerBlock_card r hprimary hsep]
  have hs :
      (∑ p : Pattern T, ∑ k, (p.owners (r k).width (r k).height).card) =
        ∑ k, (rectangleUnion (r k).width (r k).height T).card := by
    rw [Finset.sum_comm]
    simp_rw [owner_patterns_card]
  simp_rw [hs]
  simp [pow_two, mul_assoc, add_comm, add_left_comm, add_assoc]

 theorem physicalSupport_card_formula
    (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    {P : ℕ} (hplanes : ∀ k, (r k).plane ≤ P)
    (hZafter : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock r i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X)
    (hW : ∀ k, 1 ≤ (r k).width) (hJ : ∀ k, T ≤ (r k).height + 1) :
    (physicalSupport (T := T) r X Z).card =
      1 + (T + 1) * (∑ k, (((r k).width + T) * (r k).height +
        ((r k).width - 1) * gamma T)) + (T + 1) ^ 2 * Z.card := by
  rw [physicalSupport_card r X Z hprimary hsep hgrid hplanes hZafter hownerX hprivateX]
  simp_rw [rectangleUnion_card _ _ _ (hW _) (hJ _)]

namespace PackedLayout

variable {T B H : ℕ} (s : PackedLayout T B H)

/-- Sum of the owner counts of the four actual rectangle types. -/
def ownerCount : ℕ :=
  s.nh * ((T + T) * (H - 2 * gamma T) + (T - 1) * gamma T) +
  s.nv * ((B - T + T) * gamma T + (B - T - 1) * gamma T) +
  s.nf * ((B - T + T) * (H - 2 * gamma T) + (B - T - 1) * gamma T) +
  s.ns * ((B - T + T) * s.L + (B - T - 1) * gamma T)

 theorem sum_owner_formula :
    (∑ a : s.Index, (((s.rectangles a).width + T) * (s.rectangles a).height +
      ((s.rectangles a).width - 1) * gamma T)) = s.ownerCount := by
  simp [Fintype.sum_sum_type, rectangles, ownerCount, add_assoc]

 theorem physicalSupport_card_exact (X Z : Finset Point3)
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    (hZafter : ∀ z ∈ Z, (s.totalLevels * (T + 1) : ℕ) + (T : ℤ) + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock s.rectangles i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X)
    (hW : ∀ a, 1 ≤ (s.rectangles a).width)
    (hJ : ∀ a, T ≤ (s.rectangles a).height + 1) :
    (physicalSupport (T := T) s.rectangles X Z).card =
      1 + (T + 1) * s.ownerCount + (T + 1) ^ 2 * Z.card := by
  rw [physicalSupport_card_formula s.rectangles X Z s.plane_multiple s.separated
    hgrid s.plane_upper hZafter hownerX hprivateX hW hJ, s.sum_owner_formula]

end PackedLayout
end RigidGHZ.Rectangle
