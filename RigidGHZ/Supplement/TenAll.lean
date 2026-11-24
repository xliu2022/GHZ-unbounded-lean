module

public import RigidGHZ.Supplement.FreeSeedBank
public import RigidGHZ.Supplement.BalancedSeedBank
public import RigidGHZ.Supplement.Periodic.Families
public import RigidGHZ.Finite.SingleEdge

/-! The sharp uniform ten-branch guarantee for unrestricted triples. -/

@[expose] public section

namespace RigidGHZ.Supplement.Thresholds

theorem ten_initial : ∀ i : Fin 10, ThresholdAssembly.FreeSeed (2 + i.val) 10 := by
  intro i
  fin_cases i
  · exact FreeSeeds.at2_10
  · exact FreeSeeds.at3_10
  · exact FreeSeeds.at4_10
  · exact FreeSeeds.at5_10
  · exact FreeSeeds.at6_10
  · exact FreeSeeds.at7_10
  · exact FreeSeeds.at8_10
  · exact Periodic.eleven_nine.restrict (by decide) (by decide) (by decide)
  · exact Periodic.ten_ten
  · exact BalancedSeeds.at11_10.forget_bounds.to_unrestricted

theorem ten_unrestricted_bounded (m : ℕ) (hm : 2 ≤ m) :
    BoundedUnrestricted 3 m 10 (fun _ => 10) :=
  ThresholdAssembly.ten_unrestricted BalancedSeeds.at11_10.forget_bounds ten_initial m hm

/-- Supplementary Theorem S6.5: ten branches at every matching size at least two. -/
theorem unrestricted_ten (m : ℕ) (hm : 2 ≤ m) :
    ∃ H : Hypergraph (Fin (3 * m)), Uniform H 3 ∧ IsRigid H 10 := by
  obtain ⟨H, hU, hR, _⟩ := ten_unrestricted_bounded m hm
  exact ⟨H, hU, hR⟩

/-- The guaranteed dimension ten is best possible over all matching sizes at
least two, and the lower threshold two is sharp. This states the extrema using
attainment and universal upper bounds instead of an opaque maximum operator. -/
theorem ten_threshold_sharp :
    (∀ m : ℕ, 2 ≤ m → ∃ H : Hypergraph (Fin (3 * m)), Uniform H 3 ∧ IsRigid H 10) ∧
    (∀ (H : Hypergraph (Fin 6)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 10) ∧
    (∀ (H : Hypergraph (Fin 3)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 1) :=
  ⟨unrestricted_ten, fun _ _ hU hR => Finite.six_vertex_upper hU hR,
    fun _ _ hU hR => Finite.single_vertex_size_upper (by decide) hU hR⟩

end RigidGHZ.Supplement.Thresholds
