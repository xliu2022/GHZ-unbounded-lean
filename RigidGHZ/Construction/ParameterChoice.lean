module

public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Exact scale choices in the growth theorem

The strict threshold in the planar construction is implemented by taking the
integer seventh root of `(m²−1)/C²`. This also covers an integral boundary
without weakening the final lower bound.
-/

@[expose] public section

namespace RigidGHZ.Growth

def scale (k : ℕ) : ℕ := 128 * k ^ 3
def rectangularScale (k m : ℕ) : ℕ := Nat.nthRoot 7 (m / scale k)
def planarScale (k m : ℕ) : ℕ := Nat.nthRoot 7 ((m ^ 2 - 1) / (scale k) ^ 2)

theorem scale_pos {k : ℕ} (hk : 1 ≤ k) : 0 < scale k := by unfold scale; positivity

theorem rectangular_window {k m : ℕ} (hk : 1 ≤ k)
    (hm : scale k * 224 ^ 7 ≤ m) :
    224 ≤ rectangularScale k m ∧
      scale k * rectangularScale k m ^ 7 ≤ m ∧
      m < scale k * (rectangularScale k m + 1) ^ 7 := by
  have hc := scale_pos hk
  have hlo : rectangularScale k m ^ 7 ≤ m / scale k := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : m / scale k < (rectangularScale k m + 1) ^ 7 :=
    Nat.lt_pow_nthRoot_add_one (by decide) _
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_nthRoot_iff (by decide)).mpr
    exact (Nat.le_div_iff_mul_le hc).mpr (by simpa only [Nat.mul_comm] using hm)
  · have h := (Nat.le_div_iff_mul_le hc).mp hlo
    simpa only [Nat.mul_comm] using h
  · have h := (Nat.div_lt_iff_lt_mul hc).mp hhi
    simpa only [Nat.mul_comm] using h

theorem planar_window {k m : ℕ} (hk : 1 ≤ k)
    (hlo : (scale k) ^ 2 * 2 ^ 7 < m ^ 2)
    (hhi : m < scale k * 224 ^ 7) :
    2 ≤ planarScale k m ∧ planarScale k m < 224 ^ 2 ∧
      (scale k) ^ 2 * planarScale k m ^ 7 < m ^ 2 ∧
      m ^ 2 ≤ (scale k) ^ 2 * (planarScale k m + 1) ^ 7 := by
  have hc : 0 < (scale k) ^ 2 := pow_pos (scale_pos hk) _
  have hm : 0 < m ^ 2 := lt_of_le_of_lt (Nat.zero_le _) hlo
  have hroot : planarScale k m ^ 7 ≤ (m ^ 2 - 1) / (scale k) ^ 2 :=
    Nat.pow_nthRoot_le (Or.inl (by decide))
  have hnext : (m ^ 2 - 1) / (scale k) ^ 2 < (planarScale k m + 1) ^ 7 :=
    Nat.lt_pow_nthRoot_add_one (by decide) _
  have hstrict : (scale k) ^ 2 * planarScale k m ^ 7 < m ^ 2 := by
    have hb := (Nat.le_div_iff_mul_le hc).mp hroot
    rw [Nat.mul_comm] at hb
    omega
  have hupper : m ^ 2 ≤ (scale k) ^ 2 * (planarScale k m + 1) ^ 7 := by
    have hb := (Nat.div_lt_iff_lt_mul hc).mp hnext
    rw [Nat.mul_comm] at hb
    omega
  refine ⟨?_, ?_, hstrict, hupper⟩
  · apply (Nat.le_nthRoot_iff (by decide)).mpr
    apply (Nat.le_div_iff_mul_le hc).mpr
    rw [Nat.mul_comm]
    omega
  · have hbig : m ^ 2 < (scale k) ^ 2 * (224 ^ 2) ^ 7 := by
      calc
        m ^ 2 < (scale k * 224 ^ 7) ^ 2 := Nat.pow_lt_pow_left hhi (by decide)
        _ = _ := by ring
    by_contra h
    have hp := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 7
    have hmul := Nat.mul_le_mul_left ((scale k) ^ 2) hp
    omega

theorem bound_from_squared {C m q k : ℕ} (hm : m ^ 2 ≤ C ^ 2 * q ^ 7) :
    m ^ (2 * k) ≤ C ^ (2 * k) * (q ^ k) ^ 7 := by
  have h := Nat.pow_le_pow_left hm k
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm 7 k] using h

theorem bound_from_window {C m q k : ℕ} (hm : m ≤ C * q ^ 7) :
    m ^ (2 * k) ≤ C ^ (2 * k) * (q ^ (2 * k)) ^ 7 := by
  have h := Nat.pow_le_pow_left hm (2 * k)
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm 7 (2 * k)] using h

/-- Convert the integral growth certificate to the paper's real-power bound. -/
theorem real_growth_bound {C m d k : ℕ} (hC : 0 < C)
    (h : m ^ (2 * k) ≤ C ^ (2 * k) * d ^ 7) :
    ((m : ℝ) / C) ^ ((2 * (k : ℝ)) / 7) ≤ (d : ℝ) := by
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hb : (0 : ℝ) ≤ (m : ℝ) / C := div_nonneg (Nat.cast_nonneg _) hCr.le
  have hn : (m : ℝ) ^ (2 * k) ≤ (C : ℝ) ^ (2 * k) * (d : ℝ) ^ 7 := by exact_mod_cast h
  have hquot : ((m : ℝ) / C) ^ (2 * k) ≤ (d : ℝ) ^ 7 := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hCr _)).mpr (by simpa only [mul_comm] using hn)
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hb _) (Nat.cast_nonneg d)
    (show (0 : ℝ) < 7 by norm_num)).mp
  rw [← Real.rpow_mul hb]
  have he : 2 * (k : ℝ) / 7 * 7 = (2 * k : ℕ) := by push_cast; ring
  rw [he, Real.rpow_natCast, show (7 : ℝ) = (7 : ℕ) from rfl, Real.rpow_natCast]
  exact hquot

end RigidGHZ.Growth
