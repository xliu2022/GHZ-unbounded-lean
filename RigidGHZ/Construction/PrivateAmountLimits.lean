module

public import RigidGHZ.Construction.CalibrationLimits
public import RigidGHZ.Construction.RectangleArea

/-! The private-hole count and the input-size scale, with the actual rounding. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 3000000

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology RectangleEstimates Rectangular

 theorem box_height_eventual {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    ∀ᶠ (T : ℕ) in atTop,
      (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ boxHeight k T (m T) ∧
      (boxHeight k T (m T) : ℝ) ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2 := by
  filter_upwards [hw, eventually_ge_atTop 100] with T hw hT
  exact box_height_bounds hk hT hw.1 hw.2

 theorem box_height_ratio {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    RatioLimit (fun T => (boxHeight k T (m T) : ℝ)) 3 ((16 / 3 : ℝ) * k) :=
  height_ratio_of_bounds (box_height_eventual hk hw)

 theorem size_ratio {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    RatioLimit (fun T => (m T : ℝ)) 7 (128 * (k : ℝ) ^ 3) := by
  have hlo := ratio_monomial (128 * (k : ℝ) ^ 3) 7
  have hp : RatioLimit (fun T => (T : ℝ) + 1) 1 1 := by
    simpa using ratio_variable.add (ratio_const 1 (by omega : 0 < 1))
  have hhi : RatioLimit (fun T => 128 * (k : ℝ) ^ 3 * ((T : ℝ) + 1) ^ 7)
      7 (128 * (k : ℝ) ^ 3) := by
    simpa using (hp.pow 7).const_mul (128 * (k : ℝ) ^ 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hw] with T hw
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hw.1
  · filter_upwards [hw] with T hw
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hw.2.le

 theorem remainder_bounds_eventual {k : ℕ} (hk : 1 ≤ k) (m : ℕ → ℕ) :
    ∀ᶠ (T : ℕ) in atTop,
      0 ≤ (remainder k T (m T) : ℝ) ∧
        (remainder k T (m T) : ℝ) ≤ A k T * B k T - 1 := by
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hp := mul_pos (widths_pos hk hT).1 (widths_pos hk hT).2
  have hr : remainder k T (m T) + 1 ≤ widthA k T * widthB k T :=
    Nat.mod_lt _ hp
  have he : (remainder k T (m T) : ℝ) + 1 ≤ (widthA k T : ℝ) * widthB k T := by
    exact_mod_cast hr
  rw [widthA_cast, widthB_cast] at he
  exact ⟨by positivity, by linarith⟩

 theorem residue_ratio {k : ℝ} {ρ : ℕ → ℝ}
    (hρ : ∀ᶠ (T : ℕ) in atTop, 0 ≤ ρ T ∧ ρ T ≤ A k T * B k T - 1) :
    RatioLimit ρ 5 0 := by
  apply ((AB_ratio k).pad 1 (by omega)).squeeze_zero
  filter_upwards [hρ] with T hT
  exact ⟨hT.1, by linarith [hT.2]⟩

 theorem area_rounding_loss_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : ∀ᶠ (T : ℕ) in atTop,
      (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T ∧
        H T ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2) :
    RatioLimit (fun T => exactArea k T (H T) - roundedArea k T (H T)) 5 0 := by
  apply ((ratio_monomial (15 * k) 4).pad 1 (by omega)).squeeze_zero
  filter_upwards [hH, eventually_ge_atTop 100] with T hH hT
  have hTr : (100 : ℝ) ≤ T := by exact_mod_cast hT
  exact ⟨(area_loss_bounds hk (by linarith) hH.1).1,
    (area_loss_upper hk hTr hH.1 hH.2).le⟩

 theorem residueStar_ratio {k : ℝ} {H ρ : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hρ : RatioLimit ρ 5 0) :
    RatioLimit (fun T => residueStar k T (H T) (ρ T)) 5 ((46 / 3 : ℝ) * k) := by
  have hD : RatioLimit (fun T => 2 * D T + 1) 2 1 := by
    convert (D_ratio.const_mul 2).add (ratio_const 1 (by omega : 0 < 2)) using 1 <;> norm_num
  have hfirst : RatioLimit (fun T => A k T * B k T) 5 0 := (AB_ratio k).pad 1 (by omega)
  have hsecond := (((A_ratio k).add (B_ratio k)).mul hD).mul ratio_variable
  have hthird := (hH.add (hD.pad 1 (by omega))).mul (ratio_monomial 1 2)
  have ht : RatioLimit (fun T => (H T + 2 * D T + 1) * (T : ℝ) ^ 2)
      5 ((16 / 3 : ℝ) * k) := by
    convert hthird using 1
    · ext T
      ring
    · ring
  convert (((hfirst.add hsecond).add ht).sub (ratio_const 1 (by omega : 0 < 5))).sub hρ
    using 1
  · rfl
  · ring

 theorem privateAmount_ratio {k : ℝ} (hk : 1 ≤ k) {H ρ : ℕ → ℝ}
    (hH : ∀ᶠ (T : ℕ) in atTop,
      (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T ∧
        H T ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2)
    (hρ : ∀ᶠ (T : ℕ) in atTop, 0 ≤ ρ T ∧ ρ T ≤ A k T * B k T - 1) :
    RatioLimit (fun T => privateAmount k T (H T) (ρ T)) 5 ((46 / 3 : ℝ) * k) := by
  simpa only [← privateAmount_identity, add_zero] using
    (residueStar_ratio (height_ratio_of_bounds hH) (residue_ratio hρ)).add
      (area_rounding_loss_ratio hk hH)

/-- The actual quotient, remainder, and rounded-hole expression have the three
leading constants stated in the paper, for every choice in the size window. -/
theorem actual_size_height_private_limits {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    RatioLimit (fun T => (m T : ℝ)) 7 (128 * (k : ℝ) ^ 3) ∧
    RatioLimit (fun T => (boxHeight k T (m T) : ℝ)) 3 ((16 / 3 : ℝ) * k) ∧
    RatioLimit (fun T => privateAmount k T (boxHeight k T (m T)) (remainder k T (m T)))
      5 ((46 / 3 : ℝ) * k) := by
  exact ⟨size_ratio hk hw, box_height_ratio hk hw,
    privateAmount_ratio (by exact_mod_cast hk) (box_height_eventual hk hw)
      (remainder_bounds_eventual hk m)⟩

end RigidGHZ.RectangleAsymptotics
