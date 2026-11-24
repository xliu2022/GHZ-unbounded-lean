module

public import RigidGHZ.Construction.ScaledLimits
public import RigidGHZ.Construction.RectangleHeight

/-! The exact leading constants of the calibrated parameters in Appendix A. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 3000000

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology RectangleEstimates

 theorem D_ratio : RatioLimit (fun T => D T) 2 (1 / 2) := by
  have hminus : RatioLimit (fun T => (T : ℝ) - 1) 1 1 := by
    simpa using ratio_variable.sub (ratio_const 1 (by omega : 0 < 1))
  have h := (ratio_variable.mul hminus).mul_const (1 / 2)
  simpa [D, div_eq_mul_inv] using h

 theorem A_ratio (k : ℝ) : RatioLimit (fun T => A k T) 2 (4 * k) :=
  ratio_monomial (4 * k) 2

 theorem B_ratio (k : ℝ) : RatioLimit (fun T => B k T) 2 (6 * k) :=
  ratio_monomial (6 * k) 2

 theorem Q_ratio (k : ℝ) : RatioLimit (fun T => Q k T) 2 (6 * k) := by
  have hlin : RatioLimit (fun T => 2 * (T : ℝ)) 2 0 := by
    simpa using (ratio_variable.const_mul 2).pad 1 (by omega)
  simpa [Q] using ((B_ratio k).sub hlin).add (ratio_const 1 (by omega : 0 < 2))

 theorem AB_ratio (k : ℝ) :
    RatioLimit (fun T => A k T * B k T) 4 (24 * k ^ 2) := by
  convert (A_ratio k).mul (B_ratio k) using 1 <;> ring

 theorem height_ratio_of_bounds {k : ℝ} {H : ℕ → ℝ}
    (hH : ∀ᶠ (T : ℕ) in atTop,
      (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T ∧
        H T ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2) :
    RatioLimit H 3 ((16 / 3 : ℝ) * k) := by
  have hlo : RatioLimit (fun T => (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2)
      3 ((16 / 3 : ℝ) * k) := by
    simpa using (ratio_monomial ((16 / 3 : ℝ) * k) 3).sub (ratio_const 2 (by omega))
  have hhi : RatioLimit (fun T => (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2)
      3 ((16 / 3 : ℝ) * k) := by
    simpa using (ratio_monomial ((16 / 3 : ℝ) * k) 3).add
      ((ratio_monomial (39 * k) 2).pad 1 (by omega))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hH] with T hT
    exact div_le_div_of_nonneg_right hT.1 (by positivity)
  · filter_upwards [hH] with T hT
    exact div_le_div_of_nonneg_right hT.2 (by positivity)

 theorem S_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => S k T (H T)) 2 (4 * k) := by
  have hd : RatioLimit (fun T => H T - 3 * D T) 3 ((16 / 3 : ℝ) * k) := by
    simpa using hH.sub ((D_ratio.const_mul 3).pad 1 (by omega))
  have hn : (16 / 3 : ℝ) * k ≠ 0 := by positivity
  have hs := RatioLimit.div (n := 2) ((A_ratio k).mul hH) hd hn
  have he : (4 * k * ((16 / 3 : ℝ) * k)) / ((16 / 3 : ℝ) * k) = 4 * k := by
    rw [mul_div_cancel_right₀ _ hn]
  simpa only [S, he] using hs

 theorem AB_minus_S_div_Q_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => (A k T * B k T - S k T (H T)) / Q k T) 2 (4 * k) := by
  have hs : RatioLimit (fun T => S k T (H T)) 4 0 :=
    (S_ratio hk hH).pad 2 (by omega)
  have hn : RatioLimit (fun T => A k T * B k T - S k T (H T)) 4 (24 * k ^ 2) := by
    simpa using (AB_ratio k).sub hs
  have hq : 6 * k ≠ 0 := by positivity
  have he : 24 * k ^ 2 / (6 * k) = 4 * k := by
    apply (div_eq_iff hq).mpr
    ring
  simpa only [he] using RatioLimit.div (n := 2) hn (Q_ratio k) hq

 theorem loss_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => loss k T (H T)) 5 (4 * k) := by
  have hminus : RatioLimit (fun T => (T : ℝ) - 1) 1 1 := by
    simpa using ratio_variable.sub (ratio_const 1 (by omega : 0 < 1))
  have h := (D_ratio.mul hminus).mul ((S_ratio hk hH).add (AB_minus_S_div_Q_ratio hk hH))
  have he : (1 / 2 : ℝ) * 1 * (4 * k + 4 * k) = 4 * k := by ring
  simpa only [loss, he] using h

 theorem denom_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => denom k T (H T)) 5 (32 * k ^ 2) := by
  have hb : RatioLimit (fun T => B k T - 2 * (T : ℝ)) 2 (6 * k) := by
    simpa using (B_ratio k).sub ((ratio_variable.const_mul 2).pad 1 (by omega))
  have hminus : RatioLimit (fun T => (T : ℝ) - 1) 1 1 := by
    simpa using ratio_variable.sub (ratio_const 1 (by omega : 0 < 1))
  have hq : 6 * k ≠ 0 := by positivity
  have hsmall : RatioLimit (fun T => D T * ((T : ℝ) - 1) / Q k T) 3 0 :=
    (RatioLimit.div (n := 1) (D_ratio.mul hminus) (Q_ratio k) hq).pad 2 (by omega)
  have hh : RatioLimit (fun T => H T - 3 * D T - D T * ((T : ℝ) - 1) / Q k T)
      3 ((16 / 3 : ℝ) * k) := by
    simpa using (hH.sub ((D_ratio.const_mul 3).pad 1 (by omega))).sub hsmall
  have he : 6 * k * ((16 / 3 : ℝ) * k) = 32 * k ^ 2 := by ring
  simpa only [denom, he] using hb.mul hh

 theorem Z_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => Z k T (H T)) 1 (11 / 8) := by
  have hfirst := (ratio_variable.mul (B_ratio k)).mul hH
  have hsecond := (AB_ratio k).mul D_ratio
  have hsmall : RatioLimit (fun T => loss k T (H T)) 6 0 :=
    (loss_ratio hk hH).pad 1 (by omega)
  have hn : RatioLimit (fun T => (T : ℝ) * B k T * H T + A k T * B k T * D T - loss k T (H T))
      6 (44 * k ^ 2) := by
    convert (hfirst.add hsecond).sub hsmall using 1 <;> ring
  have hd : 32 * k ^ 2 ≠ 0 := by positivity
  have he : 44 * k ^ 2 / (32 * k ^ 2) = (11 / 8 : ℝ) := by
    apply (div_eq_iff hd).mpr
    ring
  simpa only [Z, he] using RatioLimit.div (n := 1) hn (denom_ratio hk hH) hd

 theorem X_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => X k T (H T)) 2 (4 * k) := by
  simpa [X] using (S_ratio hk hH).sub ((Z_ratio hk hH).pad 1 (by omega))

 theorem Y_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k)) :
    RatioLimit (fun T => Y k T (H T)) 2 (4 * k) := by
  have hn : RatioLimit (fun T => A k T * B k T - X k T (H T)) 4 (24 * k ^ 2) := by
    simpa using (AB_ratio k).sub ((X_ratio hk hH).pad 2 (by omega))
  have hq : 6 * k ≠ 0 := by positivity
  have he : 24 * k ^ 2 / (6 * k) = 4 * k := by
    apply (div_eq_iff hq).mpr
    ring
  have hx : RatioLimit (fun T => (A k T * B k T - X k T (H T)) / Q k T) 2 (4 * k) := by
    simpa only [he] using RatioLimit.div (n := 2) hn (Q_ratio k) hq
  simpa [Y] using hx.sub ((Z_ratio hk hH).pad 1 (by omega))

 theorem rounded_counts_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => (nHorizontal k T (H T) : ℝ)) 2 (4 * k) ∧
    RatioLimit (fun T => (nVertical k T (H T) : ℝ)) 2 (4 * k) ∧
    RatioLimit (fun T => (nFull k T (H T) : ℝ)) 1 (11 / 8) := by
  constructor
  · apply (X_ratio hk hH).of_bounded_error (by omega) 1
    filter_upwards [hlower, eventually_ge_atTop 6] with T hl hT
    have hb := nHorizontal_bounds hk (show (6 : ℝ) ≤ T by exact_mod_cast hT) hl
    constructor <;> linarith
  constructor
  · apply (Y_ratio hk hH).of_bounded_error (by omega) 2
    filter_upwards [hlower, eventually_ge_atTop 6] with T hl hT
    have hb := nVertical_bounds hk (show (6 : ℝ) ≤ T by exact_mod_cast hT) hl
    constructor <;> linarith
  · apply (Z_ratio hk hH).of_bounded_error (by omega) 1
    filter_upwards [hlower, eventually_ge_atTop 6] with T hl hT
    have hb := nFull_bounds hk (show (6 : ℝ) ≤ T by exact_mod_cast hT) hl
    constructor <;> linarith

end RigidGHZ.RectangleAsymptotics
