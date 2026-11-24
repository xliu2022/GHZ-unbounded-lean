module

public import RigidGHZ.Construction.RectangleArea

/-! Private-grid capacity and active-support estimates for the rectangular factor. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

def gridX (k T : ℕ) : ℕ := (widthA k T - 1) / (T + 1)
def gridY (k T : ℕ) : ℕ := (widthB k T - 1) / (T + 1)

theorem gridX_lower {k T : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    4 * k * (T - 1) ≤ gridX k T := by
  unfold gridX
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos T)).mpr
  have he : 4 * k * (T - 1) * (T + 1) + 4 * k = widthA k T := by
    unfold widthA
    zify [hT]
    ring
  rw [← he]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left (show 1 ≤ 4 * k by omega) _)

theorem gridY_lower {k T : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    6 * k * (T - 1) ≤ gridY k T := by
  unfold gridY
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos T)).mpr
  have he : 6 * k * (T - 1) * (T + 1) + 6 * k = widthB k T := by
    unfold widthB
    zify [hT]
    ring
  rw [← he]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left (show 1 ≤ 6 * k by omega) _)

end RigidGHZ.Rectangular

namespace RigidGHZ.RectangleEstimates

theorem slab_height_lower {k T H : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    k * ((16 / 3 : ℝ) * T ^ 3 - T ^ 2) ≤ H - 2 * D T := by
  have hp := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  unfold D
  nlinarith

theorem remaining_levels_lower {k T Px U : ℝ} (hk : 1 ≤ k) (hT : 0 ≤ T)
    (hPx : 4 * k * (T - 1) ≤ Px) (hU : U ≤ (83 / 24 : ℝ) * T + 6) :
    k * ((13 / 24 : ℝ) * T - 10) ≤ Px - U := by
  have hp := mul_nonneg (sub_nonneg.mpr hk) hT
  nlinarith

theorem private_grid_capacity {k T H U Px Py R : ℝ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H)
    (hU : U ≤ (83 / 24 : ℝ) * T + 6)
    (hPx : 4 * k * (T - 1) ≤ Px) (hPy : 6 * k * (T - 1) ≤ Py)
    (hR : R ≤ (46 / 3 : ℝ) * k * T ^ 5 + 80 * k ^ 2 * T ^ 4) :
    R < (Px - U) * Py * (H - 2 * D T) := by
  have hT0 : 0 ≤ T := by linarith
  have hkr : 0 < k := by linarith
  have hX := remaining_levels_lower hk hT0 hPx hU
  have hZ := slab_height_lower hk (by linarith) hH
  have hXpos : 0 < k * ((13 / 24 : ℝ) * T - 10) := mul_pos hkr (by linarith)
  have hYpos : 0 < 6 * k * (T - 1) := mul_pos (by positivity) (by linarith)
  have ht3 : T ^ 2 ≤ T ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ T - 1 by linarith) (sq_nonneg T)]
  have hZpos : 0 < k * ((16 / 3 : ℝ) * T ^ 3 - T ^ 2) := by
    apply mul_pos hkr
    have hs : 0 < T ^ 2 := by positivity
    nlinarith only [ht3, hs]
  have hxy1 := mul_le_mul_of_nonneg_right hX (show 0 ≤ Py by linarith)
  have hxy2 := mul_le_mul_of_nonneg_left hPy hXpos.le
  have hxy : k * ((13 / 24 : ℝ) * T - 10) * (6 * k * (T - 1)) ≤ (Px - U) * Py :=
    hxy2.trans hxy1
  have hxypos : 0 ≤ k * ((13 / 24 : ℝ) * T - 10) * (6 * k * (T - 1)) :=
    mul_nonneg hXpos.le hYpos.le
  have hxyz1 := mul_le_mul_of_nonneg_right hxy (show 0 ≤ H - 2 * D T by linarith)
  have hxyz2 := mul_le_mul_of_nonneg_left hZ hxypos
  have hprod : k ^ 3 * (((13 / 24 : ℝ) * T - 10) * (6 * T - 6) *
      ((16 / 3 : ℝ) * T ^ 3 - T ^ 2)) ≤ (Px - U) * Py * (H - 2 * D T) := by
    convert hxyz2.trans hxyz1 using 1 <;> ring
  have hpoly : (52 / 3 : ℝ) * T ^ 5 - 341 * T ^ 4 ≤
      ((13 / 24 : ℝ) * T - 10) * (6 * T - 6) *
        ((16 / 3 : ℝ) * T ^ 3 - T ^ 2) := by
    have hpos : 0 ≤ T ^ 2 * ((5 / 12 : ℝ) * T ^ 2 + (1533 / 4 : ℝ) * T - 60) :=
      mul_nonneg (sq_nonneg T) (by nlinarith [sq_nonneg T])
    nlinarith only [hpos]
  have hpoly' := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ k ^ 3 by positivity)
  have hk2 : k ≤ k ^ 2 := by nlinarith only [hk, sq_nonneg (k - 1)]
  have hk3 : k ^ 2 ≤ k ^ 3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg k)]
  have hRa := mul_le_mul_of_nonneg_right (hk2.trans hk3) (pow_nonneg hT0 5)
  have hRb := mul_le_mul_of_nonneg_right hk3 (pow_nonneg hT0 4)
  have hR' : R ≤ k ^ 3 * ((46 / 3 : ℝ) * T ^ 5 + 80 * T ^ 4) := by
    nlinarith only [hR, hRa, hRb]
  have hgap := mul_pos (show 0 < k ^ 3 * T ^ 4 by positivity)
    (show 0 < 2 * T - 421 by linarith)
  have hR'' : R < k ^ 3 * ((52 / 3 : ℝ) * T ^ 5 - 341 * T ^ 4) := by
    nlinarith only [hR', hgap]
  exact hR''.trans_le (hpoly'.trans hprod)

theorem primary_support_fraction {k T H U : ℝ} (hk : 1 ≤ k) (hT : 100 ≤ T)
    (hH : 0 ≤ H) (hU : U ≤ (83 / 24 : ℝ) * T + 6) :
    k * (T + 1) * U * B k T * H ≤ (9 / 10 : ℝ) * A k T * B k T * H := by
  have hTU := mul_le_mul_of_nonneg_left hU (show 0 ≤ T + 1 by linarith)
  have hTT : 100 * T ≤ T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ T by linarith)]
  have hc : (T + 1) * U ≤ (18 / 5 : ℝ) * T ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ k * B k T * H by have hb := (B_pos hk (by linarith : 1 ≤ T)).le; positivity)
  unfold A
  nlinarith

theorem private_support_fraction {k T H R : ℝ} (hk : 2 ≤ k) (hT : 100 ≤ T)
    (hH : 5 * k * T ^ 3 ≤ H)
    (hR : R ≤ (46 / 3 : ℝ) * k * T ^ 5 + 80 * k ^ 2 * T ^ 4) :
    k * (T + 1) ^ 2 * R ≤ (3 / 40 : ℝ) * A k T * B k T * H := by
  have hT0 : 0 ≤ T := by linarith
  have hk2 : 2 * k ≤ k ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k by linarith)]
  have hkT5 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hT0 5)
  have hT45 := mul_nonneg (show 0 ≤ T - 100 by linarith)
    (show 0 ≤ k ^ 2 * T ^ 4 by positivity)
  have hR' : R ≤ (127 / 15 : ℝ) * k ^ 2 * T ^ 5 := by nlinarith
  have hTsq : (T + 1) ^ 2 ≤ (101 / 100 : ℝ) ^ 2 * T ^ 2 := by
    have hTT := mul_nonneg (show 0 ≤ T - 100 by linarith) (show 0 ≤ T + 100 by linarith)
    nlinarith
  have hmul1 := mul_le_mul_of_nonneg_left hR'
    (show 0 ≤ k * (T + 1) ^ 2 by positivity)
  have hmul2 := mul_le_mul_of_nonneg_right hTsq
    (show 0 ≤ (127 / 15 : ℝ) * k ^ 3 * T ^ 5 by positivity)
  have hbig := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ (24 : ℝ) * k ^ 2 * T ^ 4 by positivity)
  have hp : 0 ≤ k ^ 3 * T ^ 7 := by positivity
  unfold A B
  nlinarith

theorem active_support_lt {k T H U R u m : ℝ} (hk : 2 ≤ k) (hT : 100 ≤ T)
    (hH : 5 * k * T ^ 3 ≤ H)
    (hU : U ≤ (83 / 24 : ℝ) * T + 6)
    (hR : R ≤ (46 / 3 : ℝ) * k * T ^ 5 + 80 * k ^ 2 * T ^ 4)
    (hu : u ≤ 1 + (T + 1) * U * B k T * H + (T + 1) ^ 2 * R)
    (hm : A k T * B k T * H ≤ m) : k * u < m := by
  have hk1 : 1 ≤ k := by linarith
  have hpH : 0 ≤ H := by
    have hp : 0 ≤ 5 * k * T ^ 3 := by positivity
    linarith only [hp, hH]
  have ha := primary_support_fraction hk1 hT hpH hU
  have hb := private_support_fraction hk hT hH hR
  have hbig := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ (24 : ℝ) * k ^ 2 * T ^ 4 by positivity)
  have hk2 : k ≤ k ^ 3 := by
    have h0 : 0 ≤ k * (k - 1) * (k + 1) := by positivity
    nlinarith
  have ht7 : 1 ≤ T ^ 7 := one_le_pow₀ (by linarith : 1 ≤ T)
  have hkT := mul_le_mul_of_nonneg_left ht7 (show 0 ≤ k ^ 3 by positivity)
  have hhub : k < (1 / 40 : ℝ) * A k T * B k T * H := by
    unfold A B
    nlinarith
  have hku := mul_le_mul_of_nonneg_left hu (show 0 ≤ k by linarith)
  nlinarith

end RigidGHZ.RectangleEstimates
