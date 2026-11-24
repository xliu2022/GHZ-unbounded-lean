module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Estimates for the rectangular construction

All parameters in this file are real.  The lower and upper hypotheses on the
box height are the explicit interval in (A.7) of the paper.  Integrality and
floor choices are handled separately.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleEstimates

def A (k T : ℝ) : ℝ := 4 * k * T ^ 2
def B (k T : ℝ) : ℝ := 6 * k * T ^ 2
def D (T : ℝ) : ℝ := T * (T - 1) / 2
def Q (k T : ℝ) : ℝ := B k T - 2 * T + 1
def S (k T H : ℝ) : ℝ := A k T * H / (H - 3 * D T)
def loss (k T H : ℝ) : ℝ := D T * (T - 1) * (S k T H + (A k T * B k T - S k T H) / Q k T)
def denom (k T H : ℝ) : ℝ :=
  (B k T - 2 * T) * (H - 3 * D T - D T * (T - 1) / Q k T)
def Z (k T H : ℝ) : ℝ :=
  (T * B k T * H + A k T * B k T * D T - loss k T H) / denom k T H
def X (k T H : ℝ) : ℝ := S k T H - Z k T H
def Y (k T H : ℝ) : ℝ := (A k T * B k T - X k T H) / Q k T - Z k T H

theorem D_nonneg {T : ℝ} (hT : 1 ≤ T) : 0 ≤ D T := by
  unfold D
  positivity

theorem A_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 0 < A k T := by
  unfold A
  positivity

theorem B_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 0 < B k T := by
  unfold B
  positivity

theorem Q_lower {k T : ℝ} (hk : 1 ≤ k) : 5 * k * T ^ 2 ≤ Q k T := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  unfold Q B
  nlinarith [sq_nonneg (T - 1)]

theorem height_margin {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    5 * k * T ^ 3 ≤ H - 3 * D T := by
  have hT0 : 0 ≤ T := by linarith
  have hpow : T ^ 3 ≥ 6 * T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)]
  have hkpow : k * T ^ 3 ≥ T ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 3)]
  unfold D
  nlinarith [sq_nonneg T]

theorem height_margin_pos {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 0 < H - 3 * D T := by
  have h := height_margin hk hT hH
  have hp : 0 < 5 * k * T ^ 3 := by positivity
  linarith

theorem height_pos {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 0 < H := by
  have hp := height_margin_pos hk hT hH
  have hd := D_nonneg (by linarith : 1 ≤ T)
  linarith

theorem Q_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 0 < Q k T := by
  have h := Q_lower (T := T) hk
  have hp : 0 < 5 * k * T ^ 2 := by positivity
  linarith

theorem S_sub_A {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    S k T H - A k T = 3 * A k T * D T / (H - 3 * D T) := by
  have hn := (height_margin_pos hk hT hH).ne'
  unfold S
  field_simp
  <;> ring

theorem S_lower {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : A k T ≤ S k T H := by
  have he := S_sub_A hk hT hH
  have ha := A_pos hk (by linarith : 1 ≤ T)
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hh := height_margin_pos hk hT hH
  have hp : 0 ≤ 3 * A k T * D T / (H - 3 * D T) := by positivity
  linarith

theorem S_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    S k T H ≤ A k T + (6 / 5 : ℝ) * T := by
  have he := S_sub_A hk hT hH
  have hh := height_margin_pos hk hT hH
  have hmargin := height_margin hk hT hH
  have hT0 : 0 ≤ T := by linarith
  have hm := mul_le_mul_of_nonneg_left hmargin hT0
  have hkpow : 0 ≤ k * T ^ 3 := by positivity
  have hdiv : 3 * A k T * D T / (H - 3 * D T) ≤ (6 / 5 : ℝ) * T := by
    apply (div_le_iff₀ hh).mpr
    unfold A D at *
    nlinarith
  linarith

theorem AB_div_Q_upper {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    A k T * B k T / Q k T ≤ A k T + (7 / 5 : ℝ) * T := by
  apply (div_le_iff₀ (Q_pos hk hT)).mpr
  have hT0 : 0 ≤ T := by linarith
  have h1 : 0 ≤ (2 / 5 : ℝ) * k * T ^ 3 := by positivity
  have h2 : 0 ≤ (4 * k - (14 / 5 : ℝ)) * T ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg T)
  unfold Q B A
  nlinarith

theorem B_margin_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    0 < B k T - 2 * T := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold B
  nlinarith

theorem Q_ge_one {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 1 ≤ Q k T := by
  unfold Q
  linarith [B_margin_pos hk hT]

theorem S_lt_Q {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : S k T H < Q k T := by
  have hs := S_upper hk hT hH
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold Q B A at *
  nlinarith

theorem A_ge_one {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 1 ≤ A k T := by
  have h := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold A
  nlinarith

theorem Q_lt_AB {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : Q k T < A k T * B k T := by
  have hb := B_pos hk hT
  have ha := A_ge_one hk hT
  have hm := mul_le_mul_of_nonneg_right ha hb.le
  unfold Q
  nlinarith

theorem loss_nonneg {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 0 ≤ loss k T H := by
  have ht : 1 ≤ T := by linarith
  have hs : 0 ≤ S k T H := (A_pos hk ht).le.trans (S_lower hk hT hH)
  have hsab : S k T H ≤ A k T * B k T :=
    (S_lt_Q hk hT hH).le.trans (Q_lt_AB hk ht).le
  have hd := D_nonneg ht
  have hq := Q_pos hk ht
  unfold loss
  positivity

theorem loss_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    loss k T H ≤ (9 / 2 : ℝ) * k * T ^ 5 := by
  have ht : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs := S_upper hk hT hH
  have hab := AB_div_Q_upper hk ht
  have hs0 : 0 ≤ S k T H := (A_pos hk ht).le.trans (S_lower hk hT hH)
  have hq := Q_pos hk ht
  have hinner : S k T H + (A k T * B k T - S k T H) / Q k T ≤
      2 * A k T + (13 / 5 : ℝ) * T := by
    rw [sub_div]
    have : 0 ≤ S k T H / Q k T := div_nonneg hs0 hq.le
    linarith
  have hd := D_nonneg ht
  have hdT : 0 ≤ D T * (T - 1) := mul_nonneg hd (by linarith)
  have hfirst := mul_le_mul_of_nonneg_left hinner hdT
  have hfac : D T * (T - 1) ≤ T ^ 3 / 2 := by
    unfold D
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * T - 1) hT0]
  have hrest : 0 ≤ 2 * A k T + (13 / 5 : ℝ) * T := by
    have := A_pos hk ht
    positivity
  have hsecond := mul_le_mul_of_nonneg_right hfac hrest
  have hk4 := mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 4)
  have ht4 := mul_nonneg (sub_nonneg.mpr hT) (pow_nonneg hT0 4)
  unfold loss A at *
  nlinarith

theorem BH_lower {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    30 * k ^ 2 * T ^ 5 ≤ B k T * H := by
  have hm := height_margin hk hT hH
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hb := B_pos hk (by linarith : 1 ≤ T)
  have hh : 5 * k * T ^ 3 ≤ H := by linarith
  have he := mul_le_mul_of_nonneg_left hh hb.le
  unfold B at *
  nlinarith

theorem inner_denom_pos {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    0 < H - 3 * D T - D T * (T - 1) / Q k T := by
  have ht : 1 ≤ T := by linarith
  have hq := Q_pos hk ht
  have hq1 := Q_ge_one hk ht
  have hm := height_margin hk hT hH
  have hT0 : 0 ≤ T := by linarith
  have hd := D_nonneg ht
  have hfac : D T * (T - 1) ≤ T ^ 3 := by
    unfold D
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * T - 1) hT0,
      pow_nonneg hT0 3]
  have hdiv : D T * (T - 1) / Q k T ≤ T ^ 3 := by
    apply (div_le_iff₀ hq).mpr
    have h := mul_le_mul_of_nonneg_left hq1 (pow_nonneg hT0 3)
    nlinarith
  have hk3 := mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 3)
  have ht3 : 0 < T ^ 3 := by positivity
  nlinarith

theorem denom_pos {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 0 < denom k T H :=
  mul_pos (B_margin_pos hk (by linarith)) (inner_denom_pos hk hT hH)

theorem denom_le_BH {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : denom k T H ≤ B k T * H := by
  have ht : 1 ≤ T := by linarith
  have hd := D_nonneg ht
  have hq := Q_pos hk ht
  have hh := height_pos hk hT hH
  have hp := inner_denom_pos hk hT hH
  have hdiv : 0 ≤ D T * (T - 1) / Q k T := by positivity
  exact mul_le_mul (by linarith) (by linarith) hp.le (B_pos hk ht).le

theorem Z_lower {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : T - 1 < Z k T H := by
  have ht : 1 ≤ T := by linarith
  have hd := denom_pos hk hT hH
  apply (lt_div_iff₀ hd).mpr
  have hden := mul_le_mul_of_nonneg_left (denom_le_BH hk hT hH)
    (by linarith : 0 ≤ T - 1)
  have hloss := loss_upper hk hT hH
  have hbh := BH_lower hk hT hH
  have habd : 0 ≤ A k T * B k T * D T :=
    mul_nonneg (mul_nonneg (A_pos hk ht).le (B_pos hk ht).le) (D_nonneg ht)
  have hk5 := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k * T ^ 5 by positivity)
  have hp : 0 < k * T ^ 5 := by positivity
  nlinarith

theorem B_ratio_upper {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    B k T / (B k T - 2 * T) ≤ (2 * T + 1) / (2 * T) := by
  apply (div_le_div_iff₀ (B_margin_pos hk hT) (by positivity : 0 < 2 * T)).mpr
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold B
  nlinarith

theorem small_loss_upper {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    D T * (T - 1) / Q k T ≤ T / 10 := by
  apply (div_le_iff₀ (Q_pos hk hT)).mpr
  have hT0 : 0 ≤ T := by linarith
  have hq := mul_le_mul_of_nonneg_left (Q_lower (T := T) hk) hT0
  have hk3 := mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 3)
  have ht2 := mul_nonneg (by linarith : 0 ≤ 2 * T - 1) hT0
  unfold D
  nlinarith

theorem total_loss_upper {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    3 * D T + D T * (T - 1) / Q k T ≤ 2 * T ^ 2 := by
  have h := small_loss_upper hk hT
  have ht2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold D at *
  nlinarith

theorem H_ratio_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    H / (H - 3 * D T - D T * (T - 1) / Q k T) ≤ (2 * T + 1) / (2 * T) := by
  apply (div_le_div_iff₀ (inner_denom_pos hk hT hH) (by positivity : 0 < 2 * T)).mpr
  have ht : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hl := mul_le_mul_of_nonneg_left (total_loss_upper hk ht)
    (by positivity : 0 ≤ 2 * T + 1)
  have hk3 := mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 3)
  have ht3 := mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)
  nlinarith [sq_nonneg (T - 1)]

theorem AD_div_H_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    A k T * D T / H ≤ (3 / 8 : ℝ) * T := by
  apply (div_le_iff₀ (height_pos hk hT hH)).mpr
  have hT0 : 0 ≤ T := by linarith
  have hh := mul_le_mul_of_nonneg_left hH hT0
  have hk3 := mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0 3)
  have ht3 := mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)
  have ht2 := mul_nonneg (by linarith : 0 ≤ T - 1) hT0
  unfold A D
  nlinarith

theorem Z_upper {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    Z k T H ≤ (11 / 8 : ℝ) * T + 2 := by
  have ht : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hh := height_pos hk hT hH
  have hb := B_margin_pos hk ht
  have hi := inner_denom_pos hk hT hH
  have hd := denom_pos hk hT hH
  have hl := loss_nonneg hk hT hH
  have hfirst : Z k T H ≤ (T * B k T * H + A k T * B k T * D T) / denom k T H := by
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  have he : (T * B k T * H + A k T * B k T * D T) / denom k T H =
      (T + A k T * D T / H) * (B k T / (B k T - 2 * T)) *
        (H / (H - 3 * D T - D T * (T - 1) / Q k T)) := by
    unfold denom
    field_simp
    <;> ring
  have hcoef : T + A k T * D T / H ≤ (11 / 8 : ℝ) * T := by
    linarith [AD_div_H_upper hk hT hH]
  have hcoef0 : 0 ≤ T + A k T * D T / H := by
    have ha := A_pos hk ht
    have hdt := D_nonneg ht
    positivity
  have hb0 : 0 ≤ B k T / (B k T - 2 * T) := div_nonneg (B_pos hk ht).le hb.le
  have hi0 : 0 ≤ H / (H - 3 * D T - D T * (T - 1) / Q k T) := div_nonneg hh.le hi.le
  have hr0 : 0 ≤ (2 * T + 1) / (2 * T) := by positivity
  have hm1 := mul_le_mul hcoef (B_ratio_upper hk ht) hb0 (by positivity : 0 ≤ (11 / 8 : ℝ) * T)
  have hm2 := mul_le_mul hm1 (H_ratio_upper hk hT hH) hi0
    (mul_nonneg (by positivity : 0 ≤ (11 / 8 : ℝ) * T) hr0)
  have hlast : (11 / 8 : ℝ) * T * ((2 * T + 1) / (2 * T)) *
      ((2 * T + 1) / (2 * T)) ≤ (11 / 8 : ℝ) * T + 2 := by
    have hform : (11 / 8 : ℝ) * T * ((2 * T + 1) / (2 * T)) *
        ((2 * T + 1) / (2 * T)) = (11 / 8 : ℝ) * T + 11 / 8 + 11 / (32 * T) := by
      field_simp
      <;> ring
    rw [hform]
    have hrem : (11 : ℝ) / (32 * T) ≤ 5 / 8 := by
      apply (div_le_iff₀ (by positivity : 0 < 32 * T)).mpr
      linarith
    linarith
  rw [he] at hfirst
  exact hfirst.trans (hm2.trans hlast)

theorem X_gt_one {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 1 < X k T H := by
  have hs := S_lower hk hT hH
  have hz := Z_upper hk hT hH
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold X A at *
  nlinarith

theorem Y_gt_two {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) : 2 < Y k T H := by
  have ht : 1 ≤ T := by linarith
  have hz := Z_upper hk hT hH
  have hzlo := Z_lower hk hT hH
  have hsq := S_lt_Q hk hT hH
  have hq := Q_pos hk ht
  have hxq : X k T H < Q k T := by unfold X; linarith
  have hxd : X k T H / Q k T < 1 := (div_lt_one hq).mpr hxq
  have hab : A k T < A k T * B k T / Q k T := by
    apply (lt_div_iff₀ hq).mpr
    have ha := A_pos hk ht
    have hdiff : 0 < 2 * T - 1 := by linarith
    have hm := mul_pos ha hdiff
    unfold Q
    nlinarith
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)
  have ht2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold Y
  rw [sub_div]
  unfold A at *
  nlinarith

theorem calibration_constant {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    (X k T H + Z k T H) * (H - 3 * D T) = A k T * H := by
  have hn := (height_margin_pos hk hT hH).ne'
  simp only [X, sub_add_cancel, S]
  exact div_mul_cancel₀ _ hn

theorem calibration_slope {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T) :
    X k T H + Q k T * (Y k T H + Z k T H) = A k T * B k T := by
  have hn := (Q_pos hk (by linarith : 1 ≤ T)).ne'
  simp only [Y, sub_add_cancel]
  rw [mul_div_cancel₀ _ hn]
  ring

theorem calibration_full {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    (X k T H + Y k T H + Z k T H) * D T * (T - 1) +
        Z k T H * (B k T - 2 * T) * (H - 3 * D T) =
      T * B k T * H + A k T * B k T * D T := by
  have hq := (Q_pos hk (by linarith : 1 ≤ T)).ne'
  have hd := (denom_pos hk hT hH).ne'
  have hz : Z k T H * denom k T H =
      T * B k T * H + A k T * B k T * D T - loss k T H :=
    div_mul_cancel₀ _ hd
  have halg : (X k T H + Y k T H + Z k T H) * D T * (T - 1) +
        Z k T H * (B k T - 2 * T) * (H - 3 * D T) =
      loss k T H + Z k T H * denom k T H := by
    unfold Y X loss denom
    have hQ : Q k T = B k T - 2 * T + 1 := rfl
    field_simp
    rw [hQ]
    ring
  rw [halg, hz]
  ring

theorem calibration_prefix {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) (l : ℝ) :
    X k T H * (H - 3 * D T + l) + Y k T H * Q k T * l +
        Z k T H * (H - 3 * D T + Q k T * l) =
      A k T * H + A k T * B k T * l := by
  have hc := calibration_constant hk hT hH
  have hs := congrArg (fun x => x * l) (calibration_slope (H := H) hk hT)
  nlinarith

theorem calibration_area {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    X k T H * T * (H - 2 * D T) + Y k T H * (B k T - T) * D T +
        Z k T H * (B k T - T) * (H - 2 * D T) =
      T * (A k T + B k T) * H + 2 * A k T * B k T * D T := by
  have halg : X k T H * T * (H - 2 * D T) + Y k T H * (B k T - T) * D T +
        Z k T H * (B k T - T) * (H - 2 * D T) =
      T * ((X k T H + Z k T H) * (H - 3 * D T)) +
      D T * (X k T H + Q k T * (Y k T H + Z k T H)) +
      ((X k T H + Y k T H + Z k T H) * D T * (T - 1) +
        Z k T H * (B k T - 2 * T) * (H - 3 * D T)) := by
    unfold Q D
    ring
  rw [halg, calibration_constant hk hT hH, calibration_slope hk hT,
    calibration_full hk hT hH]
  ring

end RigidGHZ.RectangleEstimates
