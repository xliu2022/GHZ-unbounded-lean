module

public import RigidGHZ.Construction.RectangleLevels

/-! Exact area accounting and the number of private holes after rounding. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleEstimates

def shortArea (B T D L : ℝ) : ℝ := if D ≤ L then (B - T) * L else 0

def roundedArea (k T H : ℝ) : ℝ :=
  nHorizontal k T H * T * (H - 2 * D T) +
    nVertical k T H * (B k T - T) * D T +
    nFull k T H * (B k T - T) * (H - 2 * D T) +
    shortArea (B k T) T (D T) (shortHeight k T H)

def exactArea (k T H : ℝ) : ℝ := T * (A k T + B k T) * H + 2 * A k T * B k T * D T

def residueStar (k T H ρ : ℝ) : ℝ :=
  A k T * B k T + (A k T + B k T) * (2 * D T + 1) * T +
    (H + 2 * D T + 1) * T ^ 2 - 1 - ρ

def privateAmount (k T H ρ : ℝ) : ℝ :=
  (A k T + T) * (B k T + T) * (H + 2 * D T + 1) -
    roundedArea k T H - (A k T * B k T * H + ρ + 1)

theorem privateAmount_identity (k T H ρ : ℝ) :
    privateAmount k T H ρ = residueStar k T H ρ + (exactArea k T H - roundedArea k T H) := by
  unfold privateAmount residueStar exactArea
  ring

theorem short_area_loss_bounds {B T D L α h : ℝ}
    (hBT : 0 < B - T) (hD : 0 ≤ D) (hh : 0 ≤ h) (ha : 0 ≤ α)
    (hL : L ≤ α * h) (hL' : α * h < L + 1) :
    0 ≤ α * (B - T) * h - shortArea B T D L ∧
      α * (B - T) * h - shortArea B T D L < (B - T) * (D + 1) := by
  unfold shortArea
  split_ifs with hshort
  · have hlo := mul_le_mul_of_nonneg_left hL hBT.le
    have hhi := mul_lt_mul_of_pos_left hL' hBT
    have hd := mul_nonneg hBT.le hD
    constructor <;> nlinarith
  · have hhα : 0 ≤ α * (B - T) * h := by positivity
    have hhi := mul_lt_mul_of_pos_left (show α * h < D + 1 by linarith) hBT
    exact ⟨by simpa only [sub_zero] using hhα, by nlinarith⟩

theorem area_loss_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    0 ≤ exactArea k T H - roundedArea k T H ∧
      exactArea k T H - roundedArea k T H < T * H + 3 * B k T * D T + B k T := by
  have hn := nHorizontal_bounds hk hT hH
  have hv := nVertical_bounds hk hT hH
  have hf := nFull_bounds hk hT hH
  have ha := fractionFull_bounds hk hT hH
  have hL := shortHeight_bounds hk hT hH
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hh := height_margin_pos hk hT hH
  have hb := B_margin_pos hk (by linarith : 1 ≤ T)
  have hBT : 0 < B k T - T := by linarith
  have hHD : 0 < H - 2 * D T := by linarith
  have hTH : 0 < T * (H - 2 * D T) := mul_pos (by linarith) hHD
  have hBD : 0 ≤ (B k T - T) * D T := mul_nonneg hBT.le hd
  have hhor0 := mul_nonneg (sub_nonneg.mpr hn.2.1) hTH.le
  have hhor1 := mul_lt_mul_of_pos_right (show X k T H - nHorizontal k T H < 1 by linarith) hTH
  have hver0 := mul_nonneg (show 0 ≤ Y k T H - nVertical k T H by linarith) hBD
  have hver2 := mul_le_mul_of_nonneg_right
    (show Y k T H - nVertical k T H ≤ 2 by linarith) hBD
  have hs := short_area_loss_bounds hBT hd hHD.le ha.1 hL.1 hL.2
  have he := calibration_area hk hT hH
  change _ = exactArea k T H at he
  have htotal : exactArea k T H - roundedArea k T H =
      (X k T H - nHorizontal k T H) * (T * (H - 2 * D T)) +
      (Y k T H - nVertical k T H) * ((B k T - T) * D T) +
      (fractionFull k T H * (B k T - T) * (H - 2 * D T) -
        shortArea (B k T) T (D T) (shortHeight k T H)) := by
    rw [← he]
    unfold roundedArea fractionFull
    ring
  rw [htotal]
  have hTD : 0 ≤ T * D T := mul_nonneg (by linarith) hd
  constructor <;> nlinarith

theorem area_loss_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 100 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H)
    (hH' : H ≤ (16 / 3 : ℝ) * k * T ^ 3 + 39 * k * T ^ 2) :
    exactArea k T H - roundedArea k T H < 15 * k * T ^ 4 := by
  have hb := (area_loss_bounds hk (by linarith) hH).2
  have hTH := mul_le_mul_of_nonneg_left hH' (by linarith : 0 ≤ T)
  have hTT : 100 * T ≤ T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)]
  have hg : 0 < (2 / 3 : ℝ) * T ^ 2 - 39 * T - 6 := by nlinarith
  have hp := mul_pos hg (show 0 < k * T ^ 2 by positivity)
  unfold B D at hb
  nlinarith

theorem residueStar_pos {k T H ρ : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H)
    (hρ : ρ ≤ A k T * B k T - 1) : 0 < residueStar k T H ρ := by
  have ha := A_pos hk (by linarith : 1 ≤ T)
  have hb := B_pos hk (by linarith : 1 ≤ T)
  have hh := height_pos hk hT hH
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hp : 0 < (A k T + B k T) * (2 * D T + 1) * T := by positivity
  have hq : 0 ≤ (H + 2 * D T + 1) * T ^ 2 := by positivity
  unfold residueStar
  linarith

theorem residueStar_upper {k T H ρ : ℝ} (hk : 1 ≤ k) (hT : 100 ≤ T)
    (hH : H ≤ (16 / 3 : ℝ) * k * T ^ 3 + 39 * k * T ^ 2) (hρ : 0 ≤ ρ) :
    residueStar k T H ρ ≤ (46 / 3 : ℝ) * k * T ^ 5 + 65 * k ^ 2 * T ^ 4 := by
  have hT0 : 0 ≤ T := by linarith
  have hH2 := mul_le_mul_of_nonneg_right hH (sq_nonneg T)
  have hk2 : k ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  have hk2T4 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hT0 4)
  have h1T4 := mul_le_mul_of_nonneg_right hk (pow_nonneg hT0 4)
  have hTT : 100 * T ≤ T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) hT0]
  have hsmall : 10 * T + 1 ≤ T ^ 2 := by nlinarith
  have hsmall2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ k ^ 2 * T ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hT0 3)
  have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ k ^ 2 by nlinarith) (sq_nonneg T)
  have hneg : 0 ≤ 10 * k * T ^ 4 + T ^ 3 + 1 := by positivity
  unfold residueStar A B D
  nlinarith

theorem privateAmount_bounds {k T H ρ : ℝ} (hk : 1 ≤ k) (hT : 100 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H)
    (hH' : H ≤ (16 / 3 : ℝ) * k * T ^ 3 + 39 * k * T ^ 2)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ A k T * B k T - 1) :
    0 < privateAmount k T H ρ ∧
      privateAmount k T H ρ ≤ (46 / 3 : ℝ) * k * T ^ 5 + 80 * k ^ 2 * T ^ 4 := by
  have hp := residueStar_pos hk (by linarith) hH hρ
  have hu := residueStar_upper hk hT hH' hρ0
  have hl := (area_loss_bounds hk (by linarith) hH).1
  have hb := area_loss_upper hk hT hH hH'
  have hk2 : k ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  have hkm := mul_le_mul_of_nonneg_right hk2 (show 0 ≤ T ^ 4 by positivity)
  rw [privateAmount_identity]
  constructor <;> linarith

end RigidGHZ.RectangleEstimates
