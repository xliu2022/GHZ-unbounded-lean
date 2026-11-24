module

public import RigidGHZ.Supplement.CyclicLiftComplete
public import RigidGHZ.Supplement.CyclicLiftDegrees

/-! The supplementary marked cyclic-lift theorem, on ordinary simple
hypergraphs with standard perfect matchings and maximum pair codegree. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

variable {m L : ℕ} [NeZero m] [NeZero L]

/-- The cyclic lift with marked coordinates, including the `L = 1` case. -/
 theorem Seed.cyclic_lift {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S) (β : ℕ) :
    ∃ H : Hypergraph (Fin 3 × (ZMod m × ZMod L)),
      H = coordinateHypergraph (fun hs : Bool × S => liftMap (L := L) lam δ C β hs) ∧
      Uniform H 3 ∧ BalancedPartite H 3 (m * L) ∧ IsRigid H (2 * S.card) ∧ maxDegree H 2 ≤ 2 := by
  let H := coordinateHypergraph (fun hs : Bool × S => liftMap (L := L) lam δ C β hs)
  refine ⟨H, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using coordinateHypergraph_uniform (fun hs : Bool × S => liftMap (L := L) lam δ C β hs)
  · simpa using coordinateHypergraph_balanced (fun hs : Bool × S => liftMap (L := L) lam δ C β hs)
  · let e : Fin (2 * S.card) ≃ (Bool × S) :=
      (Fintype.equivFinOfCardEq (by simp)).symm
    exact ⟨(B.cyclicFamily hm hodd hcop δ hδ C β).reindex e⟩
  · exact maxDegree_le H 2 2 (lift_codegree lam δ C β)

end RigidGHZ.Supplement.Affine
