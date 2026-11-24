module

public import RigidGHZ.UpperBounds.Corollaries
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! An explicit version of the path lower bound in Section 5:
`n ≥ (d log d / (2(r-1)))^(1/(r-1))` once `m ≥ max 5 r`.
The constant depends only on the source order. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

theorem dimension_log_le_power {r m d : ℕ} (hr : 2 ≤ r) (hm : 5 ≤ m)
    (hrm : r ≤ m) (hd : 1 ≤ d) {H : Hypergraph (Fin (r * m))}
    (hU : Uniform H r) (hR : IsRigid H d) :
    (d : ℝ) * Real.log (d : ℝ) ≤
      2 * ((r - 1 : ℕ) : ℝ) * ((r * m : ℕ) : ℝ) ^ (r - 1) := by
  have h := unrestricted_harmonic_shadow (m := m) hR hU hr (by simp)
  have hc : ((shadow H (r - 1)).card : ℝ) ≤ ((r * m : ℕ) : ℝ) ^ (r - 1) := by
    exact_mod_cast h.2.2.trans (Nat.choose_le_pow (r * m) (r - 1))
  have hprod : (d : ℝ) * beta m ≤ ((r * m : ℕ) : ℝ) ^ (r - 1) :=
    h.1.trans (h.2.1.trans hc)
  have hb : (1 : ℝ) ≤ beta m := by
    rw [beta_eq_harmonic hm]
    exact harmonic_ge_one (by omega)
  have hdpow : (d : ℝ) ≤ ((r * m : ℕ) : ℝ) ^ (r - 1) := by
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
  have hlogd : Real.log (d : ℝ) ≤
      ((r - 1 : ℕ) : ℝ) * Real.log ((r * m : ℕ) : ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) hdpow
    simpa only [Real.log_pow] using hh
  have hlm : Real.log (m : ℝ) ≤ beta m := by
    calc
      _ ≤ Real.log ((m : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by linarith)
      _ ≤ _ := logarithm_le_beta hm
  have hlr : Real.log (r : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < r)) (by exact_mod_cast hrm)
  have hlogn : Real.log ((r * m : ℕ) : ℝ) ≤ 2 * beta m := by
    rw [Nat.cast_mul, Real.log_mul
      (Nat.cast_ne_zero.mpr (by omega : r ≠ 0))
      (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))]
    linarith
  calc
    (d : ℝ) * Real.log (d : ℝ) ≤
        (d : ℝ) * (((r - 1 : ℕ) : ℝ) * Real.log ((r * m : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogd (Nat.cast_nonneg _)
    _ ≤ (d : ℝ) * (((r - 1 : ℕ) : ℝ) * (2 * beta m)) := by gcongr
    _ = (2 * ((r - 1 : ℕ) : ℝ)) * ((d : ℝ) * beta m) := by ring
    _ ≤ (2 * ((r - 1 : ℕ) : ℝ)) * ((r * m : ℕ) : ℝ) ^ (r - 1) := by gcongr

/-- A quantitative lower bound on paths, implying the paper's `Ω_r` bound. -/
theorem path_resource_lower {r m d : ℕ} (hr : 2 ≤ r) (hm : 5 ≤ m)
    (hrm : r ≤ m) (hd : 1 ≤ d) {H : Hypergraph (Fin (r * m))}
    (hU : Uniform H r) (hR : IsRigid H d) :
    ((d : ℝ) * Real.log (d : ℝ) / (2 * ((r - 1 : ℕ) : ℝ))) ^
        (1 / ((r - 1 : ℕ) : ℝ)) ≤ ((r * m : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hbase := dimension_log_le_power hr hm hrm hd hU hR
  have hdiv : (d : ℝ) * Real.log (d : ℝ) / (2 * ((r - 1 : ℕ) : ℝ)) ≤
      ((r * m : ℕ) : ℝ) ^ (r - 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbase
  have hnonneg : 0 ≤ (d : ℝ) * Real.log (d : ℝ) /
      (2 * ((r - 1 : ℕ) : ℝ)) := by
    apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hd)))
    positivity
  have hpow := Real.rpow_le_rpow hnonneg hdiv (show (0 : ℝ) ≤ 1 / ((r - 1 : ℕ) : ℝ) by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg (r * m)),
    mul_one_div_cancel hk.ne', Real.rpow_one] at hpow
  exact hpow

end RigidGHZ.UpperBounds
