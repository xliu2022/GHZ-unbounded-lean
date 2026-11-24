module

public import RigidGHZ.Construction.PrivateAmountLimits
public import RigidGHZ.Construction.RoundedOwnerCounts

/-! Leading constants for each actual class of owner vertices. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 3000000

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology RectangleEstimates Rectangular

 theorem shortOwnerMass_bounds {k T H : ℝ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * T ^ 3 - 2 ≤ H) :
    0 ≤ shortOwnerMass k T H ∧ shortOwnerMass k T H ≤ B k T * H + B k T * D T := by
  have hd := D_nonneg (by linarith : 1 ≤ T)
  have hh := height_pos hk hT hH
  have hb := B_pos hk (by linarith : 1 ≤ T)
  have hbm := B_margin_pos hk (by linarith : 1 ≤ T)
  have hmargin := height_margin_pos hk hT hH
  have hf := fractionFull_bounds hk hT hH
  have hs := (shortHeight_bounds hk hT hH).1
  have hm := mul_le_mul_of_nonneg_right hf.2.le (show 0 ≤ H - 2 * D T by linarith)
  have hl : (shortHeight k T H : ℝ) ≤ H := by linarith
  have hbl := mul_le_mul_of_nonneg_left hl hb.le
  have hbd := mul_le_mul_of_nonneg_right (show B k T - T - 1 ≤ B k T by linarith) hd
  have hcoef : 0 ≤ B k T - T - 1 := by linarith
  unfold shortOwnerMass
  split_ifs
  · constructor
    · positivity
    · linarith
  · exact ⟨le_rfl, by positivity⟩

 theorem shortOwnerMass_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => shortOwnerMass k T (H T)) 6 0 := by
  have hb : RatioLimit (fun T => B k T * H T + B k T * D T) 6 0 := by
    simpa using (((B_ratio k).mul hH).pad 1 (by omega)).add
      (((B_ratio k).mul D_ratio).pad 2 (by omega))
  apply hb.squeeze_zero
  filter_upwards [hlower, eventually_ge_atTop 6] with T hH hT
  exact shortOwnerMass_bounds hk (by exact_mod_cast hT) hH

 theorem horizontalOwnerMass_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => horizontalOwnerMass k T (H T)) 6 ((128 / 3 : ℝ) * k ^ 2) := by
  have hcounts := (rounded_counts_ratio hk hH hlower).1
  have hh : RatioLimit (fun T => H T - 2 * D T) 3 ((16 / 3 : ℝ) * k) := by
    simpa using hH.sub ((D_ratio.const_mul 2).pad 1 (by omega))
  have hminus : RatioLimit (fun T => (T : ℝ) - 1) 1 1 := by
    simpa using ratio_variable.sub (ratio_const 1 (by omega : 0 < 1))
  have hco := ((ratio_variable.add ratio_variable).mul hh).add
    ((hminus.mul D_ratio).pad 1 (by omega))
  have he : 4 * k * ((1 + 1) * ((16 / 3 : ℝ) * k) + 0) = (128 / 3 : ℝ) * k ^ 2 := by ring
  simpa only [horizontalOwnerMass, he] using hcounts.mul hco

 theorem B_minus_T_one_ratio (k : ℝ) :
    RatioLimit (fun T => B k T - (T : ℝ) - 1) 2 (6 * k) := by
  simpa using ((B_ratio k).sub (ratio_variable.pad 1 (by omega))).sub
    (ratio_const 1 (by omega : 0 < 2))

 theorem verticalOwnerMass_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => verticalOwnerMass k T (H T)) 6 (24 * k ^ 2) := by
  have hcounts := (rounded_counts_ratio hk hH hlower).2.1
  have hco := ((B_ratio k).mul D_ratio).add ((B_minus_T_one_ratio k).mul D_ratio)
  have he : 4 * k * (6 * k * (1 / 2 : ℝ) + 6 * k * (1 / 2 : ℝ)) = 24 * k ^ 2 := by ring
  simpa only [verticalOwnerMass, he] using hcounts.mul hco

 theorem fullOwnerMass_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => fullOwnerMass k T (H T)) 6 (44 * k ^ 2) := by
  have hcounts := (rounded_counts_ratio hk hH hlower).2.2
  have hh : RatioLimit (fun T => H T - 2 * D T) 3 ((16 / 3 : ℝ) * k) := by
    simpa using hH.sub ((D_ratio.const_mul 2).pad 1 (by omega))
  have hco := ((B_ratio k).mul hh).add (((B_minus_T_one_ratio k).mul D_ratio).pad 1 (by omega))
  have he : (11 / 8 : ℝ) * (6 * k * ((16 / 3 : ℝ) * k) + 0) = 44 * k ^ 2 := by ring
  simpa only [fullOwnerMass, he] using hcounts.mul hco

 theorem ownerMass_ratio {k : ℝ} (hk : 1 ≤ k) {H : ℕ → ℝ}
    (hH : RatioLimit H 3 ((16 / 3 : ℝ) * k))
    (hlower : ∀ᶠ (T : ℕ) in atTop, (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H T) :
    RatioLimit (fun T => ownerMass k T (H T)) 6 ((332 / 3 : ℝ) * k ^ 2) := by
  have h := (((horizontalOwnerMass_ratio hk hH hlower).add
    (verticalOwnerMass_ratio hk hH hlower)).add (fullOwnerMass_ratio hk hH hlower)).add
    (shortOwnerMass_ratio hk hH hlower)
  have he : (128 / 3 : ℝ) * k ^ 2 + 24 * k ^ 2 + 44 * k ^ 2 + 0 =
      (332 / 3 : ℝ) * k ^ 2 := by ring
  simpa only [ownerMass, he] using h

end RigidGHZ.RectangleAsymptotics
