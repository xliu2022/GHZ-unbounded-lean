module

public import RigidGHZ.Construction.PlanarEstimates
public import RigidGHZ.Construction.RectanglePatterns

/-! Integral box parameters and the planar height threshold. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle

/-- Width multiplier and full box width in Proposition A.3. -/
def multiplier (k : ℕ) : ℕ := 32 * k
def width (k T : ℕ) : ℕ := multiplier k * (T + 1)
def auxiliaryHeight (T : ℕ) : ℕ := (T - 1) ^ 2 + 1

def privateBudget (k T : ℕ) : ℕ := (T + 1) * gamma T + width k T - 1

def heightCeil (k T : ℕ) : ℕ :=
  ⌈PlanarEstimates.heightNumerator k T / (32 * (k : ℝ) - 2)⌉₊

def minimumHeight (k T : ℕ) : ℕ :=
  max (4 * gamma T + auxiliaryHeight T) (3 * gamma T + heightCeil k T)

theorem gamma_cast_real (T : ℕ) : (gamma T : ℝ) = PlanarEstimates.D T := by
  have hg : 2 * (gamma T : ℝ) + T = (T : ℝ) * T := by
    exact_mod_cast gamma_quadratic T
  unfold PlanarEstimates.D
  nlinarith

theorem auxiliaryHeight_cast {T : ℕ} (hT : 1 ≤ T) :
    (auxiliaryHeight T : ℝ) = PlanarEstimates.B T := by
  simp only [auxiliaryHeight, PlanarEstimates.B, Nat.cast_add, Nat.cast_pow,
    Nat.cast_sub hT, Nat.cast_one]

theorem width_cast (k T : ℕ) : (width k T : ℝ) = PlanarEstimates.width k T := by
  simp [width, multiplier, PlanarEstimates.width]

theorem width_pos {k T : ℕ} (hk : 1 ≤ k) : 0 < width k T := by
  unfold width multiplier
  positivity

theorem privateBudget_cast {k T : ℕ} (hk : 1 ≤ k) :
    (privateBudget k T : ℝ) = PlanarEstimates.R0 k T := by
  have hw : 1 ≤ (T + 1) * gamma T + width k T := by
    have hp := width_pos (T := T) hk
    omega
  rw [privateBudget, Nat.cast_sub hw, Nat.cast_add, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, gamma_cast_real, width_cast]
  unfold PlanarEstimates.R0 PlanarEstimates.D
  ring

theorem minimumHeight_cast {k T : ℕ} (hT : 1 ≤ T) :
    (minimumHeight k T : ℝ) =
      max (4 * PlanarEstimates.D T + PlanarEstimates.B T)
        (3 * PlanarEstimates.D T + heightCeil k T) := by
  simp only [minimumHeight, Nat.cast_max, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, gamma_cast_real, auxiliaryHeight_cast hT]

theorem minimumHeight_upper {k T : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T) :
    (minimumHeight k T : ℝ) ≤ (T : ℝ) ^ 3 / (60 * (k : ℝ)) + 3 * (T : ℝ) ^ 2 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hn := PlanarEstimates.heightNumerator_nonneg hkr hTr
  have hd : 0 < 32 * (k : ℝ) - 2 := by linarith
  have hc : (heightCeil k T : ℝ) ≤
      PlanarEstimates.heightNumerator k T / (32 * (k : ℝ) - 2) + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg hn hd.le)).le
  rw [minimumHeight_cast (by omega)]
  exact PlanarEstimates.height_bound hkr hTr hc

theorem minimumHeight_area_lt {k T : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hTupper : T ≤ 224 ^ 2) :
    ((width k T * minimumHeight k T : ℕ) : ℝ) < PlanarEstimates.growthScale k T := by
  have hb := PlanarEstimates.width_height_lt_threshold
    (by exact_mod_cast hk : (1 : ℝ) ≤ k) (by exact_mod_cast hT : (2 : ℝ) ≤ T)
    (by exact_mod_cast hTupper : (T : ℝ) ≤ 224 ^ 2) (minimumHeight_upper hk hT)
  simpa only [Nat.cast_mul, width_cast] using hb

theorem growthScale_square (k T : ℕ) :
    (PlanarEstimates.growthScale k T) ^ 2 =
      (((128 * k ^ 3) ^ 2 * T ^ 7 : ℕ) : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  unfold PlanarEstimates.growthScale
  push_cast
  calc
    _ = 128 ^ 2 * (k : ℝ) ^ 6 * (T : ℝ) ^ 6 * (Real.sqrt T) ^ 2 := by ring
    _ = _ := by rw [hs]; ring

/-- An entirely integral hypothesis equivalent to the paper's strict size threshold. -/
theorem growthScale_lt_of_squared {k T m : ℕ}
    (hm : (128 * k ^ 3) ^ 2 * T ^ 7 < m ^ 2) :
    PlanarEstimates.growthScale k T < (m : ℝ) := by
  have hs : (PlanarEstimates.growthScale k T) ^ 2 < (m : ℝ) ^ 2 := by
    rw [growthScale_square]
    exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

/-- Quotient and remainder produce a box tall enough for all planar pools. -/
theorem choose_box_height {k T m : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hTupper : T ≤ 224 ^ 2) (hm : (128 * k ^ 3) ^ 2 * T ^ 7 < m ^ 2) :
    minimumHeight k T ≤ (m - 1) / width k T ∧
      (m - 1) % width k T < width k T ∧
      width k T * ((m - 1) / width k T) + (m - 1) % width k T + 1 = m := by
  have harea : width k T * minimumHeight k T < m := by
    exact_mod_cast (minimumHeight_area_lt hk hT hTupper).trans (growthScale_lt_of_squared hm)
  have hw := width_pos (T := T) hk
  have hm0 : 0 < m := by omega
  refine ⟨?_, Nat.mod_lt _ hw, ?_⟩
  · apply (Nat.le_div_iff_mul_le hw).mpr
    rw [Nat.mul_comm]
    omega
  · have hdiv := Nat.mod_add_div (m - 1) (width k T)
    omega

/-- The lower geometric height constraint. -/
theorem minimumHeight_lower {k T h : ℕ} (hh : minimumHeight k T ≤ h) :
    4 * gamma T + auxiliaryHeight T ≤ h := (le_max_left _ _).trans hh

/-- The ceiling term gives exactly the private-hole capacity inequality. -/
theorem private_capacity_lower {k T h : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hh : minimumHeight k T ≤ h) :
    (32 * (k : ℝ) - 2) * ((h : ℝ) - 3 * (gamma T : ℝ)) ≥
      (privateBudget k T : ℝ) + gamma T + 2 * auxiliaryHeight T - 1 := by
  have hlower : 3 * gamma T + heightCeil k T ≤ h := (le_max_right _ _).trans hh
  have hlowerr : 3 * (gamma T : ℝ) + heightCeil k T ≤ h := by exact_mod_cast hlower
  have hc := Nat.le_ceil (PlanarEstimates.heightNumerator k T / (32 * (k : ℝ) - 2))
  change PlanarEstimates.heightNumerator k T / (32 * (k : ℝ) - 2) ≤ (heightCeil k T : ℝ) at hc
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 32 * (k : ℝ) - 2 := by linarith
  have hdiv : PlanarEstimates.heightNumerator k T / (32 * (k : ℝ) - 2) ≤
      (h : ℝ) - 3 * (gamma T : ℝ) := by linarith
  have hb := (div_le_iff₀ hd).mp hdiv
  rw [privateBudget_cast hk, gamma_cast_real, auxiliaryHeight_cast (by omega)]
  unfold PlanarEstimates.heightNumerator at hb
  rw [gamma_cast_real] at hb
  nlinarith

end RigidGHZ.Planar
