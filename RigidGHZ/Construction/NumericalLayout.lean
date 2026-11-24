module

public import RigidGHZ.Construction.PackedRectangles
public import RigidGHZ.Construction.RectangleCapacity

/-! Instantiating the finite layout with the calibrated, rounded parameters. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

theorem count_le_ceil_capacity (n d : ℕ) (hd : 0 < d) :
    n ≤ ⌈(n : ℝ) / d⌉₊ * d := by
  have hc := Nat.le_ceil ((n : ℝ) / d)
  have h := (div_le_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mp hc
  exact_mod_cast h

theorem natural_margins {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    2 * T < widthB k T ∧ 3 * gamma T < H := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hb := B_margin_pos hkr (by linarith : (1 : ℝ) ≤ T)
  have hh := height_margin_pos hkr hTr hH
  rw [← widthB_cast] at hb
  rw [← gamma_cast] at hh
  constructor
  · have h : 2 * (T : ℝ) < (widthB k T : ℝ) := by linarith
    exact_mod_cast h
  · have h : 3 * (gamma T : ℝ) < (H : ℝ) := by linarith
    exact_mod_cast h

theorem shortHeight_fit {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    shortHeight k T H ≤ H - 2 * gamma T := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have ha := fractionFull_bounds hkr hTr hH
  have hl := (shortHeight_bounds hkr hTr hH).1
  have hh := height_margin_pos hkr hTr hH
  have hd := D_nonneg (by linarith : (1 : ℝ) ≤ T)
  have hm := mul_le_mul_of_nonneg_right ha.2.le (show 0 ≤ (H : ℝ) - 2 * D T by linarith)
  have hmargin := (natural_margins hk hT hH).2
  have he : ((H - 2 * gamma T : ℕ) : ℝ) = (H : ℝ) - 2 * D T := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, gamma_cast]
  have hc : (shortHeight k T H : ℝ) ≤ ((H - 2 * gamma T : ℕ) : ℝ) := by rw [he]; linarith
  exact_mod_cast hc

def numericalLayout (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) : PackedLayout T (widthB k T) H where
  Lh := horizontalCapacity k T
  Lv := verticalCapacity T H
  nh := nHorizontal k T H
  nv := nVertical k T H
  nf := nFull k T H
  ns := shortIndicator k T H
  uh := horizontalLevels k T H
  uv := verticalLevels k T H
  L := shortHeight k T H
  Lh_pos := by unfold horizontalCapacity; positivity
  Lv_pos := verticalCapacity_pos hk hT hH
  horizontal_fit := by unfold horizontalCapacity widthB; nlinarith
  vertical_fit := verticalCapacity_fit hk hT hH
  horizontal_count := count_le_ceil_capacity _ _ (by unfold horizontalCapacity; positivity)
  vertical_count := count_le_ceil_capacity _ _ (verticalCapacity_pos hk hT hH)
  width_margin := by have h := (natural_margins hk hT hH).1; omega
  height_margin := by have h := (natural_margins hk hT hH).2; omega
  short_fit := shortHeight_fit hk hT hH

@[simp] theorem numericalLayout_levels (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (numericalLayout k T H hk hT hH).totalLevels = primaryLevels k T H := rfl

theorem shortIndicator_valid (k T H : ℕ) :
    shortIndicator k T H ≠ 0 → gamma T ≤ shortHeight k T H := by
  unfold shortIndicator
  split_ifs with h
  · exact fun _ => h
  · simp

theorem numericalLayout_area_cast (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    ((numericalLayout k T H hk hT hH).area : ℝ) = roundedArea k T H := by
  have hm := natural_margins hk hT hH
  have hB : T ≤ widthB k T := by omega
  have hD : 2 * gamma T ≤ H := by omega
  by_cases hs : gamma T ≤ shortHeight k T H
  · have hsr : D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.area, numericalLayout, shortIndicator, if_pos hs,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD, Nat.cast_ofNat,
      Nat.cast_one, widthB_cast, gamma_cast, roundedArea, shortArea, if_pos hsr, one_mul]
  · have hsr : ¬ D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.area, numericalLayout, shortIndicator, if_neg hs,
      zero_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD,
      Nat.cast_ofNat, Nat.cast_zero, widthB_cast, gamma_cast, roundedArea,
      shortArea, if_neg hsr]

end RigidGHZ.Rectangular
