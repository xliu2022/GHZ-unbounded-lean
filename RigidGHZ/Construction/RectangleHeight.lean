module

public import RigidGHZ.Construction.RectangleRounding
public import RigidGHZ.Construction.RectanglePatterns

/-!
# Integral box dimensions for the rectangular construction

The quotient and remainder are exact. The size window for `m` gives the height
interval used by all subsequent geometric and capacity estimates.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

def widthA (k T : ℕ) : ℕ := 4 * k * T ^ 2
def widthB (k T : ℕ) : ℕ := 6 * k * T ^ 2
def boxHeight (k T m : ℕ) : ℕ := (m - 1) / (widthA k T * widthB k T)
def remainder (k T m : ℕ) : ℕ := (m - 1) % (widthA k T * widthB k T)

theorem widthA_cast (k T : ℕ) : (widthA k T : ℝ) = RectangleEstimates.A k T := by
  simp [widthA, RectangleEstimates.A]

theorem widthB_cast (k T : ℕ) : (widthB k T : ℝ) = RectangleEstimates.B k T := by
  simp [widthB, RectangleEstimates.B]

theorem gamma_cast (T : ℕ) : (Rectangle.gamma T : ℝ) = RectangleEstimates.D T := by
  have h : 2 * (Rectangle.gamma T : ℝ) + T = (T : ℝ) * T := by
    exact_mod_cast Rectangle.gamma_quadratic T
  unfold RectangleEstimates.D
  nlinarith

theorem widths_pos {k T : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    0 < widthA k T ∧ 0 < widthB k T := by
  constructor <;> simp only [widthA, widthB] <;> positivity

theorem box_division {k T m : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) (hm : 1 ≤ m) :
    remainder k T m < widthA k T * widthB k T ∧
      widthA k T * widthB k T * boxHeight k T m + remainder k T m + 1 = m := by
  have hp := mul_pos (widths_pos hk hT).1 (widths_pos hk hT).2
  refine ⟨Nat.mod_lt _ hp, ?_⟩
  have h := Nat.mod_add_div (m - 1) (widthA k T * widthB k T)
  dsimp [boxHeight, remainder]
  omega

theorem binomial_seven_bound {T : ℝ} (hT : 100 ≤ T) :
    (T + 1) ^ 7 ≤ T ^ 7 + 7 * T ^ 6 + 22 * T ^ 5 := by
  have ht : 0 ≤ T := by linarith
  have h54 : 100 * T ^ 4 ≤ T ^ 5 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (pow_nonneg ht 4)]
  have h43 : 100 * T ^ 3 ≤ T ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (pow_nonneg ht 3)]
  have h32 : 100 * T ^ 2 ≤ T ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)]
  have h21 : 100 * T ≤ T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) ht]
  nlinarith

theorem growth_window_bound {T : ℝ} (hT : 100 ≤ T) :
    (T + 1) ^ 7 ≤ T ^ 7 + (117 / 16 : ℝ) * T ^ 6 := by
  have hp := binomial_seven_bound hT
  have h : 0 ≤ ((5 / 16 : ℝ) * T - 22) * T ^ 5 :=
    mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
  nlinarith

theorem box_height_bounds {k T m : ℕ} (hk : 1 ≤ k) (hT : 100 ≤ T)
    (hlo : 128 * k ^ 3 * T ^ 7 ≤ m)
    (hhi : m < 128 * k ^ 3 * (T + 1) ^ 7) :
    (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ boxHeight k T m ∧
      (boxHeight k T m : ℝ) ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 +
        39 * k * (T : ℝ) ^ 2 := by
  have hk0 : 0 < k := by omega
  have hT0 : 0 < T := by omega
  have hm : 1 ≤ m := by
    have hp : 0 < 128 * k ^ 3 * T ^ 7 := by positivity
    omega
  obtain ⟨hr, he⟩ := box_division (T := T) (m := m) hk (by omega) hm
  have hmul := mul_pos (widths_pos (T := T) hk (by omega)).1
    (widths_pos (T := T) hk (by omega)).2
  have hmulr : (0 : ℝ) < (widthA k T : ℝ) * widthB k T := by exact_mod_cast hmul
  have hquot : m ≤ widthA k T * widthB k T * (boxHeight k T m + 1) := by nlinarith
  have hbase : widthA k T * widthB k T * boxHeight k T m < m := by omega
  have hquotr : (m : ℝ) ≤ (widthA k T : ℝ) * widthB k T * (boxHeight k T m + 1) := by
    exact_mod_cast hquot
  have hbaser : (widthA k T : ℝ) * widthB k T * boxHeight k T m < (m : ℝ) := by
    exact_mod_cast hbase
  have hlor : (128 : ℝ) * (k : ℝ) ^ 3 * (T : ℝ) ^ 7 ≤ m := by exact_mod_cast hlo
  have hhir : (m : ℝ) < 128 * (k : ℝ) ^ 3 * ((T : ℝ) + 1) ^ 7 := by exact_mod_cast hhi
  have hb := growth_window_bound (by exact_mod_cast hT : (100 : ℝ) ≤ T)
  have hg := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 128 * (k : ℝ) ^ 3)
  have ha : (widthA k T : ℝ) = 4 * (k : ℝ) * (T : ℝ) ^ 2 := by simp [widthA]
  have hb' : (widthB k T : ℝ) = 6 * (k : ℝ) * (T : ℝ) ^ 2 := by simp [widthB]
  rw [ha, hb'] at hquotr hbaser hmulr
  constructor
  · apply (mul_le_mul_iff_right₀ hmulr).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hmulr).mp
    nlinarith

end RigidGHZ.Rectangular
