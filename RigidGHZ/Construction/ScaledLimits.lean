module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-! Elementary calculus for the normalized polynomial-scale limits used below. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology

abbrev RatioLimit (f : ℕ → ℝ) (n : ℕ) (a : ℝ) : Prop :=
  Tendsto (fun T => f T / (T : ℝ) ^ n) atTop (𝓝 a)

 theorem ratio_const_zero (a : ℝ) : RatioLimit (fun _ => a) 0 a := by
  simpa only [RatioLimit, pow_zero, div_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))

 theorem ratio_const (a : ℝ) {n : ℕ} (hn : 0 < n) : RatioLimit (fun _ => a) n 0 := by
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (Nat.ne_of_gt hn)).comp tendsto_natCast_atTop_atTop)

 theorem ratio_monomial (a : ℝ) (n : ℕ) :
    RatioLimit (fun T => a * (T : ℝ) ^ n) n a := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  simp [ht]

 theorem ratio_variable : RatioLimit (fun T => (T : ℝ)) 1 1 := by
  simpa using ratio_monomial 1 1

 theorem RatioLimit.add {f g : ℕ → ℝ} {n : ℕ} {a b : ℝ}
    (hf : RatioLimit f n a) (hg : RatioLimit g n b) :
    RatioLimit (fun T => f T + g T) n (a + b) := by
  simpa only [RatioLimit, add_div] using Filter.Tendsto.add hf hg

 theorem RatioLimit.sub {f g : ℕ → ℝ} {n : ℕ} {a b : ℝ}
    (hf : RatioLimit f n a) (hg : RatioLimit g n b) :
    RatioLimit (fun T => f T - g T) n (a - b) := by
  simpa only [RatioLimit, sub_div] using Filter.Tendsto.sub hf hg

 theorem RatioLimit.mul {f g : ℕ → ℝ} {n m : ℕ} {a b : ℝ}
    (hf : RatioLimit f n a) (hg : RatioLimit g m b) :
    RatioLimit (fun T => f T * g T) (n + m) (a * b) := by
  simpa only [RatioLimit, pow_add, mul_div_mul_comm] using Filter.Tendsto.mul hf hg

 theorem RatioLimit.pow {f : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (m : ℕ) :
    RatioLimit (fun T => f T ^ m) (n * m) (a ^ m) := by
  simpa only [RatioLimit, pow_mul, div_pow] using Filter.Tendsto.pow hf m

 theorem RatioLimit.div {f g : ℕ → ℝ} {n m : ℕ} {a b : ℝ}
    (hf : RatioLimit f (n + m) a) (hg : RatioLimit g m b) (hb : b ≠ 0) :
    RatioLimit (fun T => f T / g T) n (a / b) := by
  refine (Filter.Tendsto.div hf hg hb).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  dsimp
  by_cases hg0 : g T = 0
  · simp [hg0]
  · rw [pow_add]
    field_simp

 theorem RatioLimit.const_mul {f : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (c : ℝ) :
    RatioLimit (fun T => c * f T) n (c * a) := by
  simpa only [Nat.zero_add] using (ratio_const_zero c).mul hf

 theorem RatioLimit.mul_const {f : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (c : ℝ) :
    RatioLimit (fun T => f T * c) n (a * c) := by
  simpa only [Nat.add_zero] using hf.mul (ratio_const_zero c)

 theorem RatioLimit.pad {f : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (m : ℕ) (hm : 0 < m) :
    RatioLimit f (n + m) 0 := by
  simpa only [mul_one, mul_zero] using hf.mul (ratio_const 1 hm)

 theorem RatioLimit.congr {f g : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (h : f =ᶠ[atTop] g) : RatioLimit g n a := by
  apply hf.congr'
  filter_upwards [h] with T hT
  rw [hT]

/-- A bounded rounding error disappears after division by any positive power. -/
theorem RatioLimit.of_bounded_error {f g : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (hf : RatioLimit f n a) (hn : 0 < n) (C : ℝ)
    (h : ∀ᶠ T in atTop, f T - C ≤ g T ∧ g T ≤ f T + C) :
    RatioLimit g n a := by
  have hlo : RatioLimit (fun T => f T - C) n a := by
    simpa using hf.sub (ratio_const C hn)
  have hhi : RatioLimit (fun T => f T + C) n a := by
    simpa using hf.add (ratio_const C hn)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [h] with T hT
    exact div_le_div_of_nonneg_right hT.1 (pow_nonneg (Nat.cast_nonneg T) n)
  · filter_upwards [h] with T hT
    exact div_le_div_of_nonneg_right hT.2 (pow_nonneg (Nat.cast_nonneg T) n)

 theorem RatioLimit.squeeze_zero {g : ℕ → ℝ} {n : ℕ}
    (hg : RatioLimit g n 0) {f : ℕ → ℝ}
    (hf : ∀ᶠ T in atTop, 0 ≤ f T ∧ f T ≤ g T) : RatioLimit f n 0 := by
  apply _root_.squeeze_zero'
  · filter_upwards [hf] with T hT
    exact div_nonneg hT.1 (pow_nonneg (Nat.cast_nonneg T) n)
  · filter_upwards [hf] with T hT
    exact div_le_div_of_nonneg_right hT.2 (pow_nonneg (Nat.cast_nonneg T) n)
  · exact hg

end RigidGHZ.RectangleAsymptotics
