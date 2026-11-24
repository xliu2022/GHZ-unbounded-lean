module

public import RigidGHZ.Supplement.BalancedThresholds
public import RigidGHZ.Supplement.FreeSeedBank

/-! The unconditional unrestricted dimension-twelve threshold. -/

@[expose] public section

namespace RigidGHZ.Supplement.Thresholds

theorem twelve_unrestricted_bounded (m : ℕ) (hm : 21 ≤ m) :
    BoundedUnrestricted 3 m 12 (fun _ => 12) :=
  ThresholdAssembly.twelve_unrestricted FreeSeeds.at3_12 FreeSeeds.at4_12 FreeSeeds.at6_12
    BalancedSeeds.at13_12.forget_bounds BalancedSeeds.at19_12.forget_bounds
    BalancedSeeds.at23_12.forget_bounds BalancedSeeds.at29_12.forget_bounds m hm

/-- Supplementary Theorem S7.1: twelve branches on every `3m` vertices, `m≥21`. -/
theorem unrestricted_twelve (m : ℕ) (hm : 21 ≤ m) :
    ∃ H : Hypergraph (Fin (3 * m)), Uniform H 3 ∧ IsRigid H 12 := by
  obtain ⟨H, hU, hR, _⟩ := twelve_unrestricted_bounded m hm
  exact ⟨H, hU, hR⟩

end RigidGHZ.Supplement.Thresholds
