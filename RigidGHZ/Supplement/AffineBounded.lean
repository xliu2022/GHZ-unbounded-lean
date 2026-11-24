module

public import RigidGHZ.Supplement.AffineDegrees
public import RigidGHZ.Supplement.CyclicLift
public import RigidGHZ.Supplement.MarkedBinary
public import RigidGHZ.Supplement.BoundedHelpers

/-! Canonical bounded witnesses from the proved affine lift, with all marking
hypotheses supplied by the binary code construction. -/

@[expose] public section

namespace RigidGHZ.Supplement.Affine

variable {m L : ℕ} [NeZero m] [NeZero L]

theorem Seed.bounded_double {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) :
    BoundedRigid 3 m (2 * S.card) (pairBounds (2 * S.card) 2) := by
  obtain ⟨H, hU, hP, hR, hD⟩ := B.doubling hm hodd (1 : ZMod m) isUnit_one
  exact boundedRigid_of_pair_bound hU hP hR hD

theorem Seed.bounded_cyclic {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 4 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (hS : S.card ≤ 8) :
    BoundedRigid 3 (m * L) (2 * S.card) (pairBounds (2 * S.card) 2) := by
  obtain ⟨H, _, hU, hP, hR, hD⟩ := B.cyclic_lift (by omega) hodd hcop
    (1 : ZMod m) isUnit_one (Marking.binary hm hS) 0
  exact boundedRigid_of_pair_bound hU hP hR hD

end RigidGHZ.Supplement.Affine
