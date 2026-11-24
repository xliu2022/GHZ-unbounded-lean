module

public import RigidGHZ.Construction.ParameterChoice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Inverting the explicit polynomial growth bound, including the ceiling. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Growth

def prescribedSize (k d : ℕ) : ℕ :=
  ⌈(scale k : ℝ) * (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ)))⌉₊

theorem prescribedSize_pos {k d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) :
    0 < prescribedSize k d := by
  have hc : (0 : ℝ) < scale k := by exact_mod_cast scale_pos hk
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp := mul_pos hc (Real.rpow_pos_of_pos hd' ((7 : ℝ) / (2 * (k : ℝ))))
  have hceil := Nat.le_ceil ((scale k : ℝ) * (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))))
  unfold prescribedSize
  exact_mod_cast hp.trans_le hceil

theorem prescribedSize_suffices {k d m : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hm : prescribedSize k d ≤ m) :
    (d : ℝ) ≤ ((m : ℝ) / scale k) ^ (2 * (k : ℝ) / 7) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : (0 : ℝ) < scale k := by exact_mod_cast scale_pos hk
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hceil := Nat.le_ceil ((scale k : ℝ) * (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))))
  have hm' : (prescribedSize k d : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ))) ≤ (m : ℝ) / scale k := by
    apply (le_div_iff₀ hc).mpr
    change _ ≤ (prescribedSize k d : ℝ) at hceil
    nlinarith only [hceil, hm']
  have hexp : (0 : ℝ) ≤ 2 * (k : ℝ) / 7 := by positivity
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hd' _) hbase hexp
  rw [← Real.rpow_mul hd'] at hpow
  have he : (7 / (2 * (k : ℝ))) * (2 * (k : ℝ) / 7) = 1 := by
    field_simp
  simpa only [he, Real.rpow_one] using hpow

end RigidGHZ.Growth
