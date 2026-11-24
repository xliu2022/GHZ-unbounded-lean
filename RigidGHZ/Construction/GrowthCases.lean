module

public import RigidGHZ.Construction.GrowthAssembly

/-! Joining the elementary, planar, and rectangular parameter ranges. -/

@[expose] public section

namespace RigidGHZ.Growth

/-- The numerical end of the growth proof, with the two geometric construction
theorems supplied as explicit inputs. -/
theorem growth_of_factors {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (planar : ∀ T : ℕ, 2 ≤ T → T < 224 ^ 2 →
      (scale k) ^ 2 * T ^ 7 < m ^ 2 → ExistsRigid (k + 2) m ((T + 1) ^ k))
    (rectangular : ∀ T : ℕ, 224 ≤ T → scale k * T ^ 7 ≤ m →
      m < scale k * (T + 1) ^ 7 → ExistsRigid (k + 2) m ((T + 1) ^ (2 * k))) :
    ∃ d : ℕ, ExistsRigid (k + 2) m d ∧
      ((m : ℝ) / scale k) ^ (2 * (k : ℝ) / 7) ≤ d := by
  have hc := scale_pos hk
  by_cases hsmall : m ≤ scale k
  · refine ⟨1, one_matching (k + 2) m (by omega), ?_⟩
    apply real_growth_bound hc
    simpa using Nat.pow_le_pow_left hsmall (2 * k)
  · have hm2 : 2 ≤ m := by omega
    by_cases htwo : m ^ 2 ≤ (scale k) ^ 2 * 2 ^ 7
    · refine ⟨2 ^ (k + 1), ?_, ?_⟩
      · simpa using cyclic_baseline (r := k + 2) (by omega) hm2
      · apply real_growth_bound hc
        have h := bound_from_squared (k := k) htwo
        have h2 : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
        exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 7))
    · by_cases hlarge : scale k * 224 ^ 7 ≤ m
      · obtain ⟨hT, hlo, hhi⟩ := rectangular_window hk hlarge
        refine ⟨(rectangularScale k m + 1) ^ (2 * k), rectangular _ hT hlo hhi, ?_⟩
        exact real_growth_bound hc (bound_from_window hhi.le)
      · obtain ⟨hT, hT', hlo, hhi⟩ := planar_window hk (Nat.lt_of_not_ge htwo)
          (Nat.lt_of_not_ge hlarge)
        refine ⟨(planarScale k m + 1) ^ k, planar _ hT hT' hlo, ?_⟩
        exact real_growth_bound hc (bound_from_squared hhi)

/-- The same range assembly gives a natural power certificate, useful for an
independent audit of the rational exponent in the theorem statement. -/
theorem integer_growth_of_factors {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (planar : ∀ T : ℕ, 2 ≤ T → T < 224 ^ 2 →
      (scale k) ^ 2 * T ^ 7 < m ^ 2 → ExistsRigid (k + 2) m ((T + 1) ^ k))
    (rectangular : ∀ T : ℕ, 224 ≤ T → scale k * T ^ 7 ≤ m →
      m < scale k * (T + 1) ^ 7 → ExistsRigid (k + 2) m ((T + 1) ^ (2 * k))) :
    ∃ d : ℕ, ExistsRigid (k + 2) m d ∧ m ^ (2 * k) ≤ (scale k) ^ (2 * k) * d ^ 7 := by
  have hc := scale_pos hk
  by_cases hsmall : m ≤ scale k
  · refine ⟨1, one_matching (k + 2) m (by omega), ?_⟩
    simpa using Nat.pow_le_pow_left hsmall (2 * k)
  · have hm2 : 2 ≤ m := by omega
    by_cases htwo : m ^ 2 ≤ (scale k) ^ 2 * 2 ^ 7
    · refine ⟨2 ^ (k + 1), ?_, ?_⟩
      · simpa using cyclic_baseline (r := k + 2) (by omega) hm2
      · have h := bound_from_squared (k := k) htwo
        have h2 : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
        exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 7))
    · by_cases hlarge : scale k * 224 ^ 7 ≤ m
      · obtain ⟨hT, hlo, hhi⟩ := rectangular_window hk hlarge
        exact ⟨(rectangularScale k m + 1) ^ (2 * k), rectangular _ hT hlo hhi,
          bound_from_window hhi.le⟩
      · obtain ⟨hT, hT', hlo, hhi⟩ := planar_window hk (Nat.lt_of_not_ge htwo)
          (Nat.lt_of_not_ge hlarge)
        exact ⟨(planarScale k m + 1) ^ k, planar _ hT hT' hlo, bound_from_squared hhi⟩

end RigidGHZ.Growth
