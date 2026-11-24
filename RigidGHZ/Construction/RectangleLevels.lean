module

public import RigidGHZ.Construction.RectangleHeight

/-! The rounded rectangle counts fit in the claimed number of primary levels. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates

def horizontalCapacity (k T : ℕ) : ℕ := 3 * k * T
def verticalCapacity (T H : ℕ) : ℕ :=
  ⌊((H : ℝ) - D T) / (2 * D T)⌋₊
def horizontalLevels (k T H : ℕ) : ℕ :=
  ⌈(nHorizontal k T H : ℝ) / horizontalCapacity k T⌉₊
def verticalLevels (k T H : ℕ) : ℕ :=
  ⌈(nVertical k T H : ℝ) / verticalCapacity T H⌉₊
def shortIndicator (k T H : ℕ) : ℕ :=
  if Rectangle.gamma T ≤ shortHeight k T H then 1 else 0
def primaryLevels (k T H : ℕ) : ℕ :=
  horizontalLevels k T H + verticalLevels k T H + nFull k T H + shortIndicator k T H

theorem D_pos {T : ℝ} (hT : 2 ≤ T) : 0 < D T := by
  unfold D
  have h : 0 < T - 1 := by linarith
  positivity

theorem verticalCapacity_lower {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (16 / 3 : ℝ) * k * T ≤ verticalCapacity T H := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hD := D_pos (by linarith : (2 : ℝ) ≤ T)
  have hden : (0 : ℝ) < 2 * D T := by positivity
  have hgap : (16 / 3 : ℝ) * k * T + 1 ≤ ((H : ℝ) - D T) / (2 * D T) := by
    apply (le_div_iff₀ hden).mpr
    have hkT := mul_le_mul_of_nonneg_right hkr (sq_nonneg (T : ℝ))
    have hTT : (36 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    unfold D
    nlinarith
  have hf := Nat.lt_floor_add_one (((H : ℝ) - D T) / (2 * D T))
  change ((H : ℝ) - D T) / (2 * D T) < (verticalCapacity T H : ℝ) + 1 at hf
  linarith

theorem verticalCapacity_pos {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    0 < verticalCapacity T H := by
  have h := verticalCapacity_lower hk hT hH
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hp : (0 : ℝ) < (16 / 3 : ℝ) * k * T := by positivity
  exact_mod_cast hp.trans_le h

theorem verticalCapacity_fit {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    2 * verticalCapacity T H * Rectangle.gamma T + Rectangle.gamma T ≤ H := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hD := D_pos (by linarith : (2 : ℝ) ≤ T)
  have hh := height_margin_pos hkr hTr hH
  have hnon : 0 ≤ ((H : ℝ) - D T) / (2 * D T) :=
    div_nonneg (by linarith) (by positivity)
  have hf := Nat.floor_le hnon
  change (verticalCapacity T H : ℝ) ≤ ((H : ℝ) - D T) / (2 * D T) at hf
  have hb := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D T)).mp hf
  have hcast : (2 : ℝ) * verticalCapacity T H * (Rectangle.gamma T : ℝ) +
      Rectangle.gamma T ≤ H := by
    rw [gamma_cast]
    nlinarith
  exact_mod_cast hcast

theorem ceil_quotient_lt {n : ℕ} {d b : ℝ} (hd : 0 < d) (hn : (n : ℝ) ≤ b * d) :
    (⌈(n : ℝ) / d⌉₊ : ℝ) < b + 1 := by
  have hc := Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg n) hd.le)
  exact hc.trans_le (add_le_add ((div_le_iff₀ hd).mpr hn) (le_refl 1))

theorem rounded_horizontal_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    (nHorizontal k T H : ℝ) ≤ A k T + (6 / 5 : ℝ) * T := by
  have hn := (nHorizontal_bounds hk hT hH).2.1
  have hz := Z_lower hk hT hH
  have hs := S_upper hk hT hH
  unfold X at hn
  linarith

theorem rounded_vertical_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    (nVertical k T H : ℝ) ≤ A k T + (7 / 5 : ℝ) * T := by
  have hn := (nVertical_bounds hk hT hH).2.1
  have hx := X_gt_one hk hT hH
  have hz := Z_lower hk hT hH
  have hq := Q_pos hk (by linarith : 1 ≤ T)
  have hd : 0 ≤ X k T H / Q k T := div_nonneg (by linarith) hq.le
  have hb := AB_div_Q_upper hk (by linarith : 1 ≤ T)
  rw [Y, sub_div] at hn
  linarith

theorem horizontalLevels_upper {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (horizontalLevels k T H : ℝ) ≤ (4 / 3 : ℝ) * T + 7 / 5 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hn := rounded_horizontal_upper hkr hTr hH
  have hc : (horizontalCapacity k T : ℝ) = 3 * (k : ℝ) * T := by simp [horizontalCapacity]
  have hp : (0 : ℝ) < (horizontalCapacity k T : ℝ) := by rw [hc]; positivity
  have hb : (nHorizontal k T H : ℝ) ≤
      ((4 / 3 : ℝ) * T + 2 / 5) * (horizontalCapacity k T : ℝ) := by
    rw [hc]
    have hkt := mul_le_mul_of_nonneg_right hkr (show (0 : ℝ) ≤ T by positivity)
    unfold A at hn
    nlinarith
  have hl := ceil_quotient_lt hp hb
  change (horizontalLevels k T H : ℝ) < _ at hl
  linarith

theorem verticalLevels_upper {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (verticalLevels k T H : ℝ) ≤ (3 / 4 : ℝ) * T + 101 / 80 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hn := rounded_vertical_upper hkr hTr hH
  have hv := verticalCapacity_lower hk hT hH
  have hp : (0 : ℝ) < (verticalCapacity T H : ℝ) := by
    exact_mod_cast verticalCapacity_pos hk hT hH
  have hcoef : (0 : ℝ) ≤ (3 / 4 : ℝ) * T + 21 / 80 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv hcoef
  have hb : (nVertical k T H : ℝ) ≤
      ((3 / 4 : ℝ) * T + 21 / 80) * (verticalCapacity T H : ℝ) := by
    have hkt := mul_le_mul_of_nonneg_right hkr (show (0 : ℝ) ≤ T by positivity)
    unfold A at hn
    nlinarith
  have hl := ceil_quotient_lt hp hb
  change (verticalLevels k T H : ℝ) < _ at hl
  linarith

theorem primaryLevels_upper {k T H : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (primaryLevels k T H : ℝ) ≤ (83 / 24 : ℝ) * T + 6 := by
  have hh := horizontalLevels_upper hk hT hH
  have hv := verticalLevels_upper hk hT hH
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hf := (nFull_bounds hkr hTr hH).2.1
  have hz := Z_upper hkr hTr hH
  have hi : shortIndicator k T H ≤ 1 := by unfold shortIndicator; split_ifs <;> omega
  have hir : (shortIndicator k T H : ℝ) ≤ 1 := by exact_mod_cast hi
  simp only [primaryLevels, Nat.cast_add]
  linarith

end RigidGHZ.Rectangular
