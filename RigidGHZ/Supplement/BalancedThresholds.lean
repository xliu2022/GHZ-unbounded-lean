module

public import RigidGHZ.Supplement.BalancedSeedBank
public import RigidGHZ.Finite.Seeds.A29Seed

/-! Unconditional balanced tripartite thresholds from certified finite seeds. -/

@[expose] public section

namespace RigidGHZ.Supplement

namespace BalancedSeeds

theorem at29_12 : ThresholdAssembly.PairSeed 29 12 := by
  have hc : Finite.Seeds.A29.shifts.card = 6 := by decide
  simpa only [hc] using Finite.Seeds.A29.seed.bounded_double (by decide) (by decide)

end BalancedSeeds

namespace Thresholds

open BalancedSeeds

theorem ten_bounded (m : ℕ) (hm : 31 ≤ m ∨ Odd m ∧ 17 ≤ m) :
    BoundedRigid 3 m 10 (pairBounds 10 2) := by
  rcases hm with hm | ⟨ho, hm⟩
  · exact ThresholdAssembly.ten at11_10 at13_10 at17_10 at19_10 at22_10 at26_10 m hm
  · exact ThresholdAssembly.ten_odd at11_10 at13_10 at17_10 at19_10 m hm ho

theorem twelve_bounded (m : ℕ) (hm : 43 ≤ m ∨ Odd m ∧ 35 ≤ m) :
    BoundedRigid 3 m 12 (pairBounds 12 2) := by
  rcases hm with hm | ⟨ho, hm⟩
  · exact ThresholdAssembly.twelve at13_12 at19_12 at23_12 at29_12 at39_12
      at26_12 at46_12 at52_12 m hm
  · exact ThresholdAssembly.twelve_odd at13_12 at19_12 at23_12 at29_12 at39_12 m hm ho

/-- Supplementary Theorem S7.1, target dimension ten, including its odd-size range. -/
theorem balanced_ten (m : ℕ) (hm : 31 ≤ m ∨ Odd m ∧ 17 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 10 ∧ maxDegree H 2 ≤ 2 := by
  obtain ⟨H, hU, hP, hR, hD⟩ := ten_bounded m hm
  exact ⟨H, hU, hP, hR, by simpa [pairBounds] using hD 2 (by decide)⟩

/-- Supplementary Theorem S7.1, target dimension twelve. -/
theorem balanced_twelve (m : ℕ) (hm : 43 ≤ m ∨ Odd m ∧ 35 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 12 ∧ maxDegree H 2 ≤ 2 := by
  obtain ⟨H, hU, hP, hR, hD⟩ := twelve_bounded m hm
  exact ⟨H, hU, hP, hR, by simpa [pairBounds] using hD 2 (by decide)⟩

end Thresholds
end RigidGHZ.Supplement
