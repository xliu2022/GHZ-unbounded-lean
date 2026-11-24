module

public import RigidGHZ.Supplement.BalancedSeedBank
public import RigidGHZ.Supplement.Periodic.Latin

/-! The dimension-eight threshold, using the actual linear Latin seed. -/

@[expose] public section

namespace RigidGHZ.Supplement

namespace BalancedSeeds

theorem at8_8 : ThresholdAssembly.PairSeed 8 8 := by
  have hR : IsRigid (Periodic.Latin.scheme.graph (finRotate 1)) 8 :=
    ⟨Periodic.Latin.rigidFamily (by decide) (by decide)⟩
  have hD : maxDegree (Periodic.Latin.scheme.graph (finRotate 1)) 2 ≤ 2 :=
    ((linear_iff_pair_bound _).mp (Periodic.Latin.linear 1)).trans (by decide)
  exact boundedRigid_of_pair_bound (Periodic.Latin.uniform 1) (Periodic.Latin.balanced 1) hR hD

end BalancedSeeds

namespace Thresholds

theorem eight_bounded (m : ℕ) (hm : 7 ≤ m) : BoundedRigid 3 m 8 (pairBounds 8 2) :=
  ThresholdAssembly.eight BalancedSeeds.at5_8 BalancedSeeds.at7_8
    BalancedSeeds.at8_8 BalancedSeeds.at10_8 m hm

/-- Supplementary Theorem S7.1: eight branches at every part size at least seven. -/
theorem balanced_eight (m : ℕ) (hm : 7 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ maxDegree H 2 ≤ 2 := by
  obtain ⟨H, hU, hP, hR, hD⟩ := eight_bounded m hm
  exact ⟨H, hU, hP, hR, by simpa [pairBounds] using hD 2 (by decide)⟩

end Thresholds
end RigidGHZ.Supplement
