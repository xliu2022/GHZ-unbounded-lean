module

public import RigidGHZ.Construction.PrescribedDimension
public import Mathlib.Analysis.Asymptotics.Defs

/-! Explicit polynomial resource bounds, including the natural ceiling. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Growth

open Asymptotics Filter

theorem prescribedSize_upper {k d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (prescribedSize k d : ℝ) ≤ ((scale k : ℝ) + 1) *
      (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (1 : ℝ) ≤ (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))) :=
    Real.one_le_rpow hdR (by positivity)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ (scale k : ℝ) * (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))) by positivity)
  change (prescribedSize k d : ℝ) < _ at hceil
  nlinarith

theorem prescribedSize_isBigO (k : ℕ) (hk : 1 ≤ k) :
    (fun d : ℕ => (prescribedSize k d : ℝ)) =O[atTop]
      (fun d : ℕ => (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ)))) := by
  apply IsBigO.of_bound ((scale k : ℝ) + 1)
  filter_upwards [eventually_ge_atTop 1] with d hd
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (prescribedSize k d : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)] using prescribedSize_upper hk hd

theorem prescribed_sources_upper {k d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ((d * prescribedSize k d : ℕ) : ℝ) ≤ ((scale k : ℝ) + 1) *
      (d : ℝ) ^ (1 + (7 : ℝ) / (2 * (k : ℝ))) := by
  have h := mul_le_mul_of_nonneg_left (prescribedSize_upper hk hd) (Nat.cast_nonneg d)
  rw [Nat.cast_mul]
  rw [Real.rpow_add (by exact_mod_cast (by omega : 0 < d)), Real.rpow_one]
  nlinarith

theorem prescribed_sources_isBigO (k : ℕ) (hk : 1 ≤ k) :
    (fun d : ℕ => ((d * prescribedSize k d : ℕ) : ℝ)) =O[atTop]
      (fun d : ℕ => (d : ℝ) ^ (1 + (7 : ℝ) / (2 * (k : ℝ)))) := by
  apply IsBigO.of_bound ((scale k : ℝ) + 1)
  filter_upwards [eventually_ge_atTop 1] with d hd
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ ((d * prescribedSize k d : ℕ) : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)] using prescribed_sources_upper hk hd

end RigidGHZ.Growth
