module

public import RigidGHZ.Construction.GrowthCases
public import RigidGHZ.Construction.RectangularComplete
public import RigidGHZ.Construction.PlanarComplete

/-! Theorem 3.1: the quantitative construction at every source order and part size. -/

@[expose] public section

namespace RigidGHZ.Growth

theorem balanced_growth_shifted {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ d : ℕ, ExistsRigid (k + 2) m d ∧
      ((m : ℝ) / scale k) ^ (2 * (k : ℝ) / 7) ≤ d := by
  apply growth_of_factors hk hm
  · intro T hT hTupper hsize
    exact Planar.planar_product hk hT hTupper.le (by simpa only [scale] using hsize)
  · intro T hT hlo hhi
    exact Rectangular.rectangular_product hk hT
      (by simpa only [scale] using hlo) (by simpa only [scale] using hhi)

/-- A balanced ordinary `d`-rigid `r`-graph exists with the explicit lower bound
from the article. The graph has exactly `r*m` vertices. -/
theorem balanced_growth (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ExistsRigid r m d ∧
      ((m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3)) ^
        (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d := by
  have h := balanced_growth_shifted (k := r - 2) (m := m) (by omega) hm
  simpa only [Nat.sub_add_cancel (show 2 ≤ r by omega), scale,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using h

/-- The same existence theorem with an exact natural-number power certificate. -/
theorem balanced_growth_integer (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ExistsRigid r m d ∧
      m ^ (2 * (r - 2)) ≤ (128 * (r - 2) ^ 3) ^ (2 * (r - 2)) * d ^ 7 := by
  have h : ∃ d : ℕ, ExistsRigid (r - 2 + 2) m d ∧
      m ^ (2 * (r - 2)) ≤ (scale (r - 2)) ^ (2 * (r - 2)) * d ^ 7 := by
    apply integer_growth_of_factors (by omega) hm
    · intro T hT hTupper hsize
      exact Planar.planar_product (by omega) hT hTupper.le (by simpa only [scale] using hsize)
    · intro T hT hlo hhi
      exact Rectangular.rectangular_product (by omega) hT
        (by simpa only [scale] using hlo) (by simpa only [scale] using hhi)
  simpa only [Nat.sub_add_cancel (show 2 ≤ r by omega), scale] using h

end RigidGHZ.Growth
