module

public import RigidGHZ.Construction.RectangleEstimates
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rounding the calibrated rectangular multiplicities

These are the exact floor choices used in Appendix A.  The extra subtraction
of one vertical rectangle reserves enough anchors for the shorter rectangle.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleEstimates

def nHorizontal (k T H : ℝ) : ℕ := ⌊X k T H⌋₊
def nVertical (k T H : ℝ) : ℕ := ⌊Y k T H⌋₊ - 1
def nFull (k T H : ℝ) : ℕ := ⌊Z k T H⌋₊
def fractionFull (k T H : ℝ) : ℝ := Z k T H - nFull k T H
def shortHeight (k T H : ℝ) : ℕ := ⌊fractionFull k T H * (H - 2 * D T)⌋₊

theorem nHorizontal_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    1 ≤ nHorizontal k T H ∧ (nHorizontal k T H : ℝ) ≤ X k T H ∧
      X k T H < nHorizontal k T H + 1 := by
  have hx := X_gt_one hk hT hH
  exact ⟨Nat.le_floor (by simpa using hx.le), Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

theorem nVertical_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    1 ≤ nVertical k T H ∧ (nVertical k T H : ℝ) ≤ Y k T H - 1 ∧
      Y k T H < nVertical k T H + 2 := by
  have hy := Y_gt_two hk hT hH
  have hf : 2 ≤ ⌊Y k T H⌋₊ := Nat.le_floor hy.le
  have he : (nVertical k T H : ℝ) = (⌊Y k T H⌋₊ : ℝ) - 1 := by
    unfold nVertical
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hlo := Nat.floor_le (by linarith : 0 ≤ Y k T H)
  have hhi := Nat.lt_floor_add_one (Y k T H)
  refine ⟨by unfold nVertical; omega, ?_, ?_⟩ <;> linarith

theorem nFull_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    1 ≤ nFull k T H ∧ (nFull k T H : ℝ) ≤ Z k T H ∧
      Z k T H < nFull k T H + 1 := by
  have hz := Z_lower hk hT hH
  exact ⟨Nat.le_floor (by norm_num; linarith), Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

theorem fractionFull_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    0 ≤ fractionFull k T H ∧ fractionFull k T H < 1 := by
  have h := nFull_bounds hk hT hH
  unfold fractionFull
  constructor <;> linarith

theorem shortHeight_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    (shortHeight k T H : ℝ) ≤ fractionFull k T H * (H - 2 * D T) ∧
      fractionFull k T H * (H - 2 * D T) < shortHeight k T H + 1 := by
  have ha := (fractionFull_bounds hk hT hH).1
  have hh := height_margin_pos hk hT hH
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hnon : 0 ≤ fractionFull k T H * (H - 2 * D T) :=
    mul_nonneg ha (by linarith)
  exact ⟨Nat.floor_le hnon, Nat.lt_floor_add_one _⟩

def shortPrefixDemand (D Q L l : ℝ) : ℝ := if D ≤ L then L - D + Q * l else 0
def shortFullDemand (B T D L : ℝ) : ℝ :=
  if D ≤ L then (B - 2 * T) * (L - D) + (T - 1) * D else 0

theorem rounded_prefix_le {x y z nh nv nf H D Q L α l : ℝ}
    (hH : 0 ≤ H - 3 * D) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hl : 0 ≤ l)
    (hnh : nh ≤ x) (hnv : nv ≤ y - 1) (hnf : nf = z - α)
    (ha : 0 ≤ α) (ha1 : α ≤ 1) (hL : L ≤ α * (H - 2 * D)) :
    nh * (H - 3 * D + l) + nv * Q * l + nf * (H - 3 * D + Q * l) +
        shortPrefixDemand D Q L l ≤
      x * (H - 3 * D + l) + y * Q * l + z * (H - 3 * D + Q * l) := by
  have hQl : 0 ≤ Q * l := mul_nonneg hQ hl
  have hhcoef : 0 ≤ H - 3 * D + l := by linarith
  have hfcoef : 0 ≤ H - 3 * D + Q * l := by linarith
  have hh := mul_le_mul_of_nonneg_right hnh hhcoef
  have hv := mul_le_mul_of_nonneg_right hnv hQl
  have hf := mul_le_mul_of_nonneg_right ha hfcoef
  unfold shortPrefixDemand
  split_ifs with hshort
  · have hαD := mul_nonneg (sub_nonneg.mpr ha1) hD
    have hαQl := mul_nonneg ha hQl
    rw [hnf]
    nlinarith
  · rw [hnf]
    nlinarith

theorem rounded_full_le {x y z nh nv nf H B T D L α : ℝ}
    (hH : 0 ≤ H - 3 * D) (hD : 0 ≤ D) (hT : 1 ≤ T)
    (hB : 3 * T - 1 ≤ B)
    (hnh : nh ≤ x) (hnv : nv ≤ y) (hnf : nf = z - α)
    (ha : 0 ≤ α) (ha1 : α ≤ 1) (hL : L ≤ α * (H - 2 * D)) :
    (nh + nv + nf) * D * (T - 1) + nf * (B - 2 * T) * (H - 3 * D) +
        shortFullDemand B T D L ≤
      (x + y + z) * D * (T - 1) + z * (B - 2 * T) * (H - 3 * D) := by
  have hBT : 0 ≤ B - 2 * T := by linarith
  have hDT : 0 ≤ D * (T - 1) := mul_nonneg hD (by linarith)
  have hBTmargin : 0 ≤ (B - 2 * T) * (H - 3 * D) := mul_nonneg hBT hH
  have hh := mul_le_mul_of_nonneg_right hnh hDT
  have hv := mul_le_mul_of_nonneg_right hnv hDT
  have hfa := mul_nonneg ha hDT
  have hfb := mul_nonneg ha hBTmargin
  unfold shortFullDemand
  split_ifs with hshort
  · have hLm := mul_le_mul_of_nonneg_left hL hBT
    have hαD := mul_nonneg (sub_nonneg.mpr ha1) hD
    have hgap := mul_nonneg hαD (sub_nonneg.mpr hB)
    rw [hnf]
    nlinarith
  · rw [hnf]
    nlinarith

theorem integer_prefix_supply {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) {l : ℝ} (hl : 0 ≤ l) :
    (nHorizontal k T H : ℝ) * (H - 3 * D T + l) +
      (nVertical k T H : ℝ) * Q k T * l +
      (nFull k T H : ℝ) * (H - 3 * D T + Q k T * l) +
      shortPrefixDemand (D T) (Q k T) (shortHeight k T H) l ≤
      A k T * H + A k T * B k T * l := by
  have hn := nHorizontal_bounds hk hT hH
  have hv := nVertical_bounds hk hT hH
  have ha := fractionFull_bounds hk hT hH
  have hL := shortHeight_bounds hk hT hH
  have hb := rounded_prefix_le (z := Z k T H) (nf := (nFull k T H : ℝ))
    (α := fractionFull k T H) (height_margin_pos hk hT hH).le
    (D_nonneg (T := T) (by linarith)) (Q_pos (T := T) hk (by linarith)).le hl hn.2.1 hv.2.1
    (by unfold fractionFull; ring) ha.1 ha.2.le hL.1
  exact hb.trans_eq (calibration_prefix hk hT hH l)

theorem integer_full_supply {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    ((nHorizontal k T H : ℝ) + nVertical k T H + nFull k T H) * D T * (T - 1) +
      (nFull k T H : ℝ) * (B k T - 2 * T) * (H - 3 * D T) +
      shortFullDemand (B k T) T (D T) (shortHeight k T H) ≤
      T * B k T * H + A k T * B k T * D T := by
  have hn := nHorizontal_bounds hk hT hH
  have hv := nVertical_bounds hk hT hH
  have ha := fractionFull_bounds hk hT hH
  have hL := shortHeight_bounds hk hT hH
  have hB : 3 * T - 1 ≤ B k T := by
    have hQ := Q_lower (T := T) hk
    have hk2 := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
    have ht2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
    unfold Q B at *
    nlinarith
  have hb := rounded_full_le (z := Z k T H) (nf := (nFull k T H : ℝ))
    (α := fractionFull k T H) (height_margin_pos hk hT hH).le
    (D_nonneg (T := T) (by linarith)) (by linarith : 1 ≤ T) hB hn.2.1
    (by linarith : (nVertical k T H : ℝ) ≤ Y k T H)
    (by unfold fractionFull; ring) ha.1 ha.2.le hL.1
  exact hb.trans_eq (calibration_full hk hT hH)

end RigidGHZ.RectangleEstimates
