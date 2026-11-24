module

public import RigidGHZ.Construction.PlanarOwners
public import RigidGHZ.Selector.RealizedPlanarComb

@[expose] public section

namespace RigidGHZ.Planar

open Selector Selector.BlockExpansion
open scoped Finset

/-- Lift a lattice set into the finite source ground set, reserving `none` for the hub. -/
def liftLatticeSet (X S : Finset Lattice) : Finset (Option ↥X) :=
  (S.subtype (fun x => x ∈ X)).map Function.Embedding.some

@[simp] theorem some_mem_liftLatticeSet (X S : Finset Lattice) (x : ↥X) :
    some x ∈ liftLatticeSet X S ↔ x.val ∈ S := by
  simp [liftLatticeSet]

@[simp] theorem none_not_mem_liftLatticeSet (X S : Finset Lattice) :
    none ∉ liftLatticeSet X S := by
  simp [liftLatticeSet]

 theorem liftLatticeSet_card (X S : Finset Lattice) (hS : S ⊆ X) :
    (liftLatticeSet X S).card = S.card := by
  simp only [liftLatticeSet, Finset.card_map, Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr hS]

 theorem liftLatticeSet_nonempty (X S : Finset Lattice) (hS : S ⊆ X) (hp : S.Nonempty) :
    (liftLatticeSet X S).Nonempty := by
  apply Finset.card_pos.mp
  rw [liftLatticeSet_card X S hS]
  exact Finset.card_pos.mpr hp

 theorem liftLatticeSet_disjoint (X S U : Finset Lattice) (h : Disjoint S U) :
    Disjoint (liftLatticeSet X S) (liftLatticeSet X U) := by
  apply Finset.disjoint_left.mpr
  intro x hx hu
  cases x with
  | none => exact none_not_mem_liftLatticeSet X S hx
  | some x =>
    exact Finset.disjoint_left.mp h ((some_mem_liftLatticeSet X S x).mp hx)
      ((some_mem_liftLatticeSet X U x).mp hu)


abbrev BlockKey (T : ℕ) := Option (Pattern T ⊕ Fin (T + 1))

def blockKeyEquiv (T : ℕ) : PlanarComb.Vertex T ≃ BlockKey T where
  toFun v := match v.val with
    | .hub => none
    | .upper _ a => Fin.cases none (fun l => some (Sum.inl (.suffix l))) a
    | .branch _ b => some (Sum.inr b)
    | .lower _ a => some (Sum.inl (.prefix a))
  invFun
    | none => PlanarComb.hub T
    | some (Sum.inl p) => PlanarComb.ownerBlock p
    | some (Sum.inr b) => PlanarComb.branch b
  left_inv := by
    rintro ⟨v, hv⟩
    cases v with
    | hub => exact (hv rfl).elim
    | upper i a =>
      cases i
      revert hv
      refine Fin.cases ?_ (fun l => ?_) a <;> intro hv <;> rfl
    | branch i b => cases i; rfl
    | lower i a => cases i; rfl
  right_inv := by
    rintro (_ | (p | b))
    · rfl
    · cases p <;> rfl
    · rfl

@[simp] theorem blockKeyEquiv_hub (T : ℕ) : blockKeyEquiv T (PlanarComb.hub T) = none := rfl
@[simp] theorem blockKeyEquiv_pattern (T : ℕ) (p : Pattern T) :
    blockKeyEquiv T (PlanarComb.ownerBlock p) = some (Sum.inl p) := by cases p <;> rfl
@[simp] theorem blockKeyEquiv_branch (T : ℕ) (b : Fin (T + 1)) :
    blockKeyEquiv T (PlanarComb.branch b) = some (Sum.inr b) := rfl

def indexedBlocks (w h : ℕ) (X Z : Finset Lattice) {T : ℕ} : BlockKey T → Finset (Option ↥X)
  | none => {none}
  | some (Sum.inl p) => liftLatticeSet X (owners w h p)
  | some (Sum.inr b) => liftLatticeSet X (inverseSet Z b.val)

def physicalBlocks (w h : ℕ) (X Z : Finset Lattice) {T : ℕ}
    (v : PlanarComb.Vertex T) : Finset (Option ↥X) := indexedBlocks w h X Z (blockKeyEquiv T v)

@[simp] theorem physicalBlocks_hub (w h T : ℕ) (X Z : Finset Lattice) :
    physicalBlocks w h X Z (PlanarComb.hub T) = {none} := rfl

@[simp] theorem physicalBlocks_pattern (w h : ℕ) (X Z : Finset Lattice) {T : ℕ} (p : Pattern T) :
    physicalBlocks w h X Z (PlanarComb.ownerBlock p) = liftLatticeSet X (owners w h p) := by
  rw [physicalBlocks, blockKeyEquiv_pattern]
  rfl

@[simp] theorem physicalBlocks_branch (w h : ℕ) (X Z : Finset Lattice) {T : ℕ} (b : Fin (T + 1)) :
    physicalBlocks w h X Z (PlanarComb.branch b) = liftLatticeSet X (inverseSet Z b.val) := rfl

theorem inverseSet_mono {Z U : Finset Lattice} (hZU : Z ⊆ U) (b : ℕ) : inverseSet Z b ⊆ inverseSet U b := by
  intro x hx
  exact mem_inverseSet.mpr (hZU (mem_inverseSet.mp hx))

theorem physicalBlocks_disjoint {p h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ p * (T + 1))
    (hh : 4 * Rectangle.gamma T + auxiliaryHeight T ≤ h) (X Z : Finset Lattice)
    (hZ : Z ⊆ privatePool p h T) : Pairwise (fun v w : PlanarComb.Vertex T =>
      Disjoint (physicalBlocks (p * (T + 1)) h X Z v) (physicalBlocks (p * (T + 1)) h X Z w)) := by
  have hd : Pairwise (fun a b : BlockKey T =>
      Disjoint (indexedBlocks (p * (T + 1)) h X Z a) (indexedBlocks (p * (T + 1)) h X Z b)) := by
    intro a b hne
    cases a with
    | none =>
      cases b with
      | none => exact (hne rfl).elim
      | some b => cases b <;> simp [indexedBlocks, Finset.disjoint_singleton_left]
    | some a =>
      cases b with
      | none => cases a <;> simp [indexedBlocks, Finset.disjoint_singleton_right]
      | some b =>
        cases a with
        | inl a =>
          cases b with
          | inl b =>
            apply liftLatticeSet_disjoint
            apply owners_disjoint hw hh
            intro he; exact hne (congrArg (fun p => some (Sum.inl p)) he)
          | inr b => exact liftLatticeSet_disjoint X _ _ (private_owners_disjoint hT hh Z hZ b a).symm
        | inr a =>
          cases b with
          | inl b => exact liftLatticeSet_disjoint X _ _ (private_owners_disjoint hT hh Z hZ a b)
          | inr b =>
            apply liftLatticeSet_disjoint
            apply (private_inverse_disjoint (by omega) (by omega) ?_).mono (inverseSet_mono hZ a.val) (inverseSet_mono hZ b.val)
            intro he
            exact hne (congrArg (fun b => some (Sum.inr b)) (Fin.ext he))
  intro v w hvw
  apply hd
  intro he
  exact hvw ((blockKeyEquiv T).injective he)

theorem private_subset_box {p h T : ℕ} (hT : 2 ≤ T)
    (hh : 4 * Rectangle.gamma T + auxiliaryHeight T ≤ h) (Z : Finset Lattice)
    (hZ : Z ⊆ privatePool p h T) (b : Fin (T + 1)) :
    inverseSet Z b.val ⊆ box 0 (p * (T + 1)) 0 h := by
  intro x hx
  have he := (private_inverse_envelope hT (by omega) hh (hZ (mem_inverseSet.mp hx))).1
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using he

theorem physicalBlocks_nonempty {p h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ p * (T + 1))
    (hh : 4 * Rectangle.gamma T + auxiliaryHeight T ≤ h) (X Z : Finset Lattice)
    (hX : box 0 (p * (T + 1)) 0 h ⊆ X) (hZ : Z ⊆ privatePool p h T) (hZpos : Z.Nonempty) :
    ∀ v : PlanarComb.Vertex T, (physicalBlocks (p * (T + 1)) h X Z v).Nonempty := by
  intro v
  change (indexedBlocks (p * (T + 1)) h X Z (blockKeyEquiv T v)).Nonempty
  cases blockKeyEquiv T v with
  | none => simp [indexedBlocks]
  | some a =>
    cases a with
    | inl q => exact liftLatticeSet_nonempty X _ ((owners_subset_box hw hh q).trans hX) (owners_nonempty hT hw hh q)
    | inr b =>
      apply liftLatticeSet_nonempty X _ ((private_subset_box hT hh Z hZ b).trans hX)
      apply Finset.card_pos.mp
      rw [inverseSet_card]
      exact Finset.card_pos.mpr hZpos

def physicalSupport (w h T : ℕ) (X Z : Finset Lattice) : Finset (Option ↥X) :=
  Finset.univ.biUnion (physicalBlocks w h X Z : PlanarComb.Vertex T → Finset (Option ↥X))

end RigidGHZ.Planar
