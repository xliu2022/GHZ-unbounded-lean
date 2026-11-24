module

public import RigidGHZ.Construction.PlacedPatterns
public import RigidGHZ.Construction.PrivateOwners
public import RigidGHZ.Construction.DoubleCombPatterns
public import RigidGHZ.Selector.RealizeBlocks

@[expose] public section

namespace RigidGHZ.Rectangle

open Selector Selector.DoubleComb Selector.BlockExpansion

/-- Lift a lattice set into the finite source ground set, reserving `none` for the hub. -/
def liftLatticeSet (X S : Finset Point3) : Finset (Option ↥X) :=
  (S.subtype (fun x => x ∈ X)).map Function.Embedding.some

@[simp] theorem some_mem_liftLatticeSet (X S : Finset Point3) (x : ↥X) :
    some x ∈ liftLatticeSet X S ↔ x.val ∈ S := by
  simp [liftLatticeSet]

@[simp] theorem none_not_mem_liftLatticeSet (X S : Finset Point3) :
    none ∉ liftLatticeSet X S := by
  simp [liftLatticeSet]

 theorem liftLatticeSet_card (X S : Finset Point3) (hS : S ⊆ X) :
    (liftLatticeSet X S).card = S.card := by
  simp only [liftLatticeSet, Finset.card_map, Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr hS]

 theorem liftLatticeSet_nonempty (X S : Finset Point3) (hS : S ⊆ X) (hp : S.Nonempty) :
    (liftLatticeSet X S).Nonempty := by
  apply Finset.card_pos.mp
  rw [liftLatticeSet_card X S hS]
  exact Finset.card_pos.mpr hp

 theorem liftLatticeSet_disjoint (X S U : Finset Point3) (h : Disjoint S U) :
    Disjoint (liftLatticeSet X S) (liftLatticeSet X U) := by
  apply Finset.disjoint_left.mpr
  intro x hx hu
  cases x with
  | none => exact none_not_mem_liftLatticeSet X S hx
  | some x =>
    exact Finset.disjoint_left.mp h ((some_mem_liftLatticeSet X S x).mp hx)
      ((some_mem_liftLatticeSet X U x).mp hu)

abbrev BlockKey (T : ℕ) := Option ((Fin (T + 1) × Pattern T) ⊕ (Fin (T + 1) × Fin (T + 1)))

/-- Owner patterns and private routes index exactly the nonhub double-comb blocks. -/
def blockKeyEquiv (T : ℕ) : Vertex (Fin (T + 1)) T ≃ BlockKey T where
  toFun
    | .hub => none
    | .upper i a => Fin.cases (some (Sum.inl (i, Pattern.full)))
        (fun l => some (Sum.inl (i, Pattern.suffix l))) a
    | .branch i b => some (Sum.inr (i, b))
    | .lower i a => some (Sum.inl (i, Pattern.prefix a))
  invFun
    | none => .hub
    | some (Sum.inl (i, p)) => patternVertex i p
    | some (Sum.inr (i, b)) => .branch i b
  left_inv := by
    intro v
    cases v with
    | upper i a => refine Fin.cases ?_ (fun l => ?_) a <;> rfl
    | _ => rfl
  right_inv := by
    rintro (_ | (⟨i, p⟩ | ⟨i, b⟩))
    · rfl
    · cases p <;> rfl
    · rfl

@[simp] theorem blockKeyEquiv_pattern (T : ℕ) (i : Fin (T + 1)) (p : Pattern T) :
    blockKeyEquiv T (patternVertex i p) = some (Sum.inl (i, p)) := by
  cases p <;> rfl

variable {K : Type*} [Fintype K] [DecidableEq K] {T : ℕ}
    (r : K → PrimaryRectangle) (X Z : Finset Point3)

def indexedBlocks : BlockKey T → Finset (Option ↥X)
  | none => {none}
  | some (Sum.inl (i, p)) => liftLatticeSet X (ownerBlock r i p)
  | some (Sum.inr (i, b)) => liftLatticeSet X (privateBlock Z i.val b.val)

def physicalBlocks (v : Vertex (Fin (T + 1)) T) : Finset (Option ↥X) :=
  indexedBlocks r X Z (blockKeyEquiv T v)

@[simp] theorem physicalBlocks_hub : physicalBlocks r X Z (.hub : Vertex (Fin (T + 1)) T) = {none} := rfl

@[simp] theorem physicalBlocks_pattern (i : Fin (T + 1)) (p : Pattern T) :
    physicalBlocks r X Z (patternVertex i p) = liftLatticeSet X (ownerBlock r i p) := by
  rw [physicalBlocks, blockKeyEquiv_pattern]
  rfl

@[simp] theorem physicalBlocks_private (i b : Fin (T + 1)) :
    physicalBlocks r X Z (.branch i b) = liftLatticeSet X (privateBlock Z i.val b.val) := rfl

variable (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    {P : ℕ} (hplanes : ∀ k, (r k).plane ≤ P)
    (hZafter : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)

include hprimary hsep hgrid hplanes hZafter

 theorem private_ownerBlock_disjoint (i b j : Fin (T + 1)) (p : Pattern T) :
    Disjoint (privateBlock Z i.val b.val) (ownerBlock r j p) := by
  apply Finset.disjoint_left.mpr
  intro x hx ho
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp ho
  exact Finset.disjoint_left.mp (private_primary_disjoint Z hZafter (r k) (hplanes k) i b j)
    hx (owner_map_subset r k j p hk)

 theorem indexedBlocks_disjoint : Pairwise (fun a b : BlockKey T =>
    Disjoint (indexedBlocks r X Z a) (indexedBlocks r X Z b)) := by
  intro a b hne
  cases a with
  | none =>
    cases b with
    | none => exact (hne rfl).elim
    | some b =>
      cases b <;> simp [indexedBlocks, Finset.disjoint_singleton_left]
  | some a =>
    cases b with
    | none => cases a <;> simp [indexedBlocks, Finset.disjoint_singleton_right]
    | some b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          apply liftLatticeSet_disjoint
          apply ownerBlock_disjoint r hprimary hsep
          intro h; exact hne (congrArg (fun a => some (Sum.inl a)) h)
        | inr b =>
          exact liftLatticeSet_disjoint X _ _
            (private_ownerBlock_disjoint r Z hprimary hsep hgrid hplanes hZafter b.1 b.2 a.1 a.2).symm
      | inr a =>
        cases b with
        | inl b =>
          exact liftLatticeSet_disjoint X _ _
            (private_ownerBlock_disjoint r Z hprimary hsep hgrid hplanes hZafter a.1 a.2 b.1 b.2)
        | inr b =>
          apply liftLatticeSet_disjoint
          apply privateBlocks_disjoint Z hgrid
          intro h; exact hne (congrArg (fun a => some (Sum.inr a)) h)

 theorem physicalBlocks_disjoint : Pairwise (fun v w : Vertex (Fin (T + 1)) T =>
    Disjoint (physicalBlocks r X Z v) (physicalBlocks r X Z w)) := by
  intro v w hne
  apply indexedBlocks_disjoint r X Z hprimary hsep hgrid hplanes hZafter
  intro h
  exact hne ((blockKeyEquiv T).injective h)

omit hprimary hsep hgrid hplanes hZafter in
 theorem physicalBlocks_nonempty
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock r i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X)
    (howner : ∀ (i : Fin (T + 1)) (p : Pattern T), (ownerBlock r i p).Nonempty) (hZ : Z.Nonempty) :
    ∀ v : Vertex (Fin (T + 1)) T, (physicalBlocks r X Z v).Nonempty := by
  intro v
  change (indexedBlocks r X Z (blockKeyEquiv T v)).Nonempty
  cases blockKeyEquiv T v with
  | none => simp [indexedBlocks]
  | some a =>
    cases a with
    | inl a => exact liftLatticeSet_nonempty X _ (hownerX a.1 a.2) (howner a.1 a.2)
    | inr a =>
      exact liftLatticeSet_nonempty X _ (hprivateX a.1 a.2)
        (privateBlock_nonempty Z hZ a.1.val a.2.val)

end RigidGHZ.Rectangle
