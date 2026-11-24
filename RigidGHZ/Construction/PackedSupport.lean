module

public import RigidGHZ.Construction.RectangleSites

/-! Finite active-support bound for the concrete rectangular placement. -/

@[expose] public section

namespace RigidGHZ.Rectangle

open RectangleAnchors Selector Selector.DoubleComb

 theorem liftLatticeSet_card_le (X S : Finset Point3) :
    (liftLatticeSet X S).card ≤ S.card := by
  simp only [liftLatticeSet, Finset.card_map, Finset.card_subtype]
  exact Finset.card_filter_le _ _

 theorem liftLatticeSet_mono (X : Finset Point3) {S U : Finset Point3} (h : S ⊆ U) :
    liftLatticeSet X S ⊆ liftLatticeSet X U := by
  intro x hx
  cases x with
  | none => exact (none_not_mem_liftLatticeSet X S hx).elim
  | some x =>
    apply (some_mem_liftLatticeSet X U x).mpr
    exact h ((some_mem_liftLatticeSet X S x).mp hx)

/-- All primary owner vertices lie in this narrow band. -/
def primarySupportBand (P B H : ℕ) : Finset Point3 := box 1 (P + 1) 0 B 0 H

@[simp] theorem primarySupportBand_card (P B H : ℕ) :
    (primarySupportBand P B H).card = P * B * H := by
  simp [primarySupportBand, box, Finset.card_product, Int.card_Ico, mul_assoc]

def allPrivateOwners (T : ℕ) (Z : Finset Point3) : Finset Point3 :=
  (Finset.univ : Finset (Fin (T + 1) × Fin (T + 1))).biUnion
    (fun ib => privateBlock Z ib.1.val ib.2.val)

 theorem allPrivateOwners_card {T : ℕ} (Z : Finset Point3)
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0) :
    (allPrivateOwners T Z).card = (T + 1) ^ 2 * Z.card := by
  have hd : (↑(Finset.univ : Finset (Fin (T + 1) × Fin (T + 1))) :
      Set (Fin (T + 1) × Fin (T + 1))).PairwiseDisjoint
      (fun (ib : Fin (T + 1) × Fin (T + 1)) => privateBlock Z ib.1.val ib.2.val) := by
    intro i hi j hj hij
    exact privateBlocks_disjoint Z hgrid hij
  rw [allPrivateOwners, Finset.card_biUnion hd]
  simp [pow_two, mul_assoc]

namespace PackedLayout

variable {T B H : ℕ} (s : PackedLayout T B H)

 theorem ownerBlock_in_band (i : Fin (T + 1)) (p : Pattern T) :
    ownerBlock s.rectangles i p ⊆ primarySupportBand (s.totalLevels * (T + 1)) B H := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  have hown := owner_map_subset s.rectangles a i p hx
  have hb := s.owners_in_box (A := s.totalLevels * (T + 1) + 1) (by omega) a i hown
  have hfirst := ((s.rectangles a).owner_bounds (Nat.le_of_lt_succ i.isLt) hown).1
  have hlow := s.plane_lower a
  simp only [primarySupportBand, box, Finset.mem_product, Finset.mem_Ico]
  omega

 theorem physicalSupport_subset (X Z : Finset Point3) :
    physicalSupport (T := T) s.rectangles X Z ⊆ {none} ∪
      liftLatticeSet X (primarySupportBand (s.totalLevels * (T + 1)) B H ∪ allPrivateOwners T Z) := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := Finset.mem_biUnion.mp hw
  change w ∈ indexedBlocks s.rectangles X Z (blockKeyEquiv T v) at hw
  generalize blockKeyEquiv T v = key at hw
  cases key with
  | none => exact Finset.mem_union_left _ hw
  | some key =>
    cases key with
    | inl ip =>
      apply Finset.mem_union_right
      exact liftLatticeSet_mono X ((s.ownerBlock_in_band ip.1 ip.2).trans
        Finset.subset_union_left) hw
    | inr ib =>
      apply Finset.mem_union_right
      apply liftLatticeSet_mono X (S := privateBlock Z ib.1.val ib.2.val) _ hw
      intro x hx
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨ib, Finset.mem_univ _, hx⟩)

/-- This is the combinatorial estimate used in the support-packing calculation. -/
theorem physicalSupport_card_le (X Z : Finset Point3)
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0) :
    (physicalSupport (T := T) s.rectangles X Z).card ≤
      1 + (T + 1) * s.totalLevels * B * H + (T + 1) ^ 2 * Z.card := by
  have hsub := Finset.card_le_card (s.physicalSupport_subset X Z)
  have hunion := Finset.card_union_le
    ({none} : Finset (Option ↥X))
    (liftLatticeSet X (primarySupportBand (s.totalLevels * (T + 1)) B H ∪ allPrivateOwners T Z))
  have hlift := liftLatticeSet_card_le X
    (primarySupportBand (s.totalLevels * (T + 1)) B H ∪ allPrivateOwners T Z)
  have hlarge := Finset.card_union_le (primarySupportBand (s.totalLevels * (T + 1)) B H)
    (allPrivateOwners T Z)
  rw [primarySupportBand_card, allPrivateOwners_card Z hgrid] at hlarge
  simp only [Finset.card_singleton] at hunion
  nlinarith

end PackedLayout
end RigidGHZ.Rectangle
