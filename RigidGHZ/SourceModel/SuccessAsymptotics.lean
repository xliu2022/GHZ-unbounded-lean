module

public import RigidGHZ.SourceModel.JointState
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The logarithmic success-probability asymptotic of Section 5, including a
uniform error bound for the vacuum factor and an explicit Theta hypothesis. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open Asymptotics Filter Topology

/-- The optimum already attained by the uniform pump in the binary model. -/
def optimalProbability (m d : ℕ) : ℝ :=
  (d : ℝ) * (1 / (d : ℝ)) ^ m * (1 - 1 / (d : ℝ)) ^ (m * (d - 1))

theorem optimalProbability_eq_success {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {H : Hypergraph V} {r m d : ℕ} (G : RigidFamily H (Fin d))
    (hU : Uniform H r) (hr : 0 < r) (hd : 2 ≤ d) (hV : Fintype.card V = r * m) :
    successProbability (MatchingDecomposition.ofRigidFamily G)
      (fun _ => 1 / (d : ℝ)) (fun _ => 0) = optimalProbability m d := by
  apply uniform_binary_success G hU hr hV _ (by positivity)
  apply (div_le_one (by exact_mod_cast (by omega : 0 < d))).mpr
  exact_mod_cast (by omega : 1 ≤ d)

theorem optimal_vacuum_positive {d : ℕ} (hd : 2 ≤ d) :
    0 < (1 : ℝ) - 1 / (d : ℝ) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hdR)

theorem optimalProbability_log (m d : ℕ) (hd : 2 ≤ d) :
    Real.log (optimalProbability m d) =
      (1 - (m : ℝ)) * Real.log (d : ℝ) +
        (m : ℝ) * ((d : ℝ) - 1) * Real.log (1 - 1 / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hv := optimal_vacuum_positive hd
  rw [optimalProbability, Real.log_mul (mul_pos hd0 (pow_pos (by positivity) m)).ne'
    (pow_pos hv _).ne', Real.log_mul hd0.ne' (pow_pos (by positivity) m).ne',
    Real.log_pow, Real.log_pow, Real.log_div one_ne_zero hd0.ne', Real.log_one]
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  ring

theorem vacuum_log_bounds {d : ℕ} (hd : 2 ≤ d) :
    -1 ≤ ((d : ℝ) - 1) * Real.log (1 - 1 / (d : ℝ)) ∧
      ((d : ℝ) - 1) * Real.log (1 - 1 / (d : ℝ)) ≤ 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    linarith
  have hv := optimal_vacuum_positive hd
  have hlo := Real.one_sub_inv_le_log_of_pos hv
  have hhi := Real.log_nonpos hv.le
    (show (1 : ℝ) - 1 / (d : ℝ) ≤ 1 by
      have : 0 ≤ (1 : ℝ) / d := by positivity
      linarith)
  have he : ((d : ℝ) - 1) * (1 - (1 - 1 / (d : ℝ))⁻¹) = -1 := by
    field_simp
    <;> ring
  constructor
  · rw [← he]
    exact mul_le_mul_of_nonneg_left hlo hd1.le
  · exact mul_nonpos_of_nonneg_of_nonpos hd1.le hhi

/-- The vacuum contribution to the optimal log probability has magnitude at
most the matching size, uniformly over every dimension at least two. -/
theorem optimalProbability_log_error (m d : ℕ) (hd : 2 ≤ d) :
    |Real.log (optimalProbability m d) - (1 - (m : ℝ)) * Real.log (d : ℝ)| ≤ m := by
  rw [optimalProbability_log m d hd]
  have h := vacuum_log_bounds hd
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlo := mul_le_mul_of_nonneg_left h.1 hm
  have hhi := mul_le_mul_of_nonneg_left h.2 hm
  apply abs_le.mpr
  constructor <;> nlinarith

theorem log_difference_of_theta {f g : ℕ → ℝ} (h : f =Θ[atTop] g)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    (fun n => Real.log (f n) - Real.log (g n)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨C, hC, hCf⟩ := h.1.exists_pos
  obtain ⟨D, hD, hDg⟩ := h.2.exists_pos
  apply IsBigO.of_bound (max |Real.log C| |Real.log D|)
  filter_upwards [hCf.bound, hDg.bound, hf, hg] with n hCf hDg hf hg
  have hfg : f n ≤ C * g n := by
    simpa only [Real.norm_of_nonneg hf.le, Real.norm_of_nonneg hg.le] using hCf
  have hgf : g n ≤ D * f n := by
    simpa only [Real.norm_of_nonneg hf.le, Real.norm_of_nonneg hg.le] using hDg
  have hu := Real.log_le_log hf hfg
  have hl := Real.log_le_log hg hgf
  rw [Real.log_mul hC.ne' hg.ne'] at hu
  rw [Real.log_mul hD.ne' hf.ne'] at hl
  have hc := (le_abs_self (Real.log C)).trans (le_max_left |Real.log C| |Real.log D|)
  have hd := (le_abs_self (Real.log D)).trans (le_max_right |Real.log C| |Real.log D|)
  simp only [Real.norm_eq_abs, abs_one, mul_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If dimension grows as `Theta(n^α)`, the optimal log probability is
`-(α/r)n log n + O(n)`, along the path counts `n=r*m`. -/
theorem optimalProbability_log_asymptotic (r : ℕ) (hr : 1 ≤ r) (α : ℝ) (hα : 0 < α)
    (d : ℕ → ℕ)
    (hθ : (fun m : ℕ => (d m : ℝ)) =Θ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ α)) :
    (fun m : ℕ => Real.log (optimalProbability m (d m)) +
      (α / (r : ℝ)) * ((r * m : ℕ) : ℝ) * Real.log ((r * m : ℕ) : ℝ)) =O[atTop]
        (fun m : ℕ => ((r * m : ℕ) : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : Tendsto (fun m : ℕ => ((r * m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using tendsto_natCast_atTop_atTop.const_mul_atTop hr0
  have hdtop : Tendsto (fun m : ℕ => ‖(d m : ℝ)‖) atTop atTop :=
    hθ.tendsto_norm_atTop_iff.mpr
      (tendsto_norm_atTop_atTop.comp ((tendsto_rpow_atTop hα).comp hn))
  have hd2 : ∀ᶠ m in atTop, 2 ≤ d m := by
    filter_upwards [hdtop.eventually_ge_atTop 2] with m hm
    exact_mod_cast (by simpa only [Real.norm_of_nonneg (show (0 : ℝ) ≤ (d m : ℝ) from Nat.cast_nonneg _)] using hm : (2 : ℝ) ≤ d m)
  have hlog := log_difference_of_theta hθ
    (hd2.mono (fun m hm => by exact_mod_cast (by omega : 0 < d m)))
    ((eventually_ge_atTop 1).mono (fun m hm => Real.rpow_pos_of_pos
      (by exact_mod_cast (show 0 < r * m by positivity)) _))
  have he : (fun m : ℕ => Real.log (d m : ℝ) - α * Real.log ((r * m : ℕ) : ℝ))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply hlog.congr' _ (EventuallyEq.refl _ _)
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [Real.log_rpow (by exact_mod_cast (show 0 < r * m by positivity))]
  obtain ⟨K, hK, herror⟩ := he.exists_pos
  let C : ℝ := 1 + 2 * K + |α| * (r : ℝ)
  apply IsBigO.of_bound C
  filter_upwards [herror.bound, hd2, eventually_ge_atTop 1] with m herror hd hm
  let n : ℝ := ((r * m : ℕ) : ℝ)
  let e : ℝ := Real.log (d m : ℝ) - α * Real.log n
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ r * m by nlinarith)
  have hmn : (m : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (show m ≤ r * m from (by simpa using Nat.mul_le_mul_right m hr))
  have heK : |e| ≤ K := by simpa only [Real.norm_eq_abs, abs_one, mul_one] using herror
  have hlogn : |Real.log n| ≤ n := by
    rw [abs_of_nonneg (Real.log_nonneg hn1)]
    exact Real.log_le_self (by linarith)
  have hlogd : |Real.log (d m : ℝ)| ≤ K + |α| * n := by
    calc
      _ = |e + α * Real.log n| := by dsimp [e]; congr 1; ring
      _ ≤ |e| + |α| * |Real.log n| := by
        simpa only [abs_mul] using abs_add_le e (α * Real.log n)
      _ ≤ K + |α| * n := by gcongr
  have ht := optimalProbability_log_error m (d m) hd
  have hident : Real.log (optimalProbability m (d m)) +
        (α / (r : ℝ)) * n * Real.log n =
      (Real.log (optimalProbability m (d m)) - (1 - (m : ℝ)) * Real.log (d m : ℝ)) +
        Real.log (d m : ℝ) - (m : ℝ) * e := by
    dsimp [e, n]
    push_cast
    field_simp
    <;> ring
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change ‖Real.log (optimalProbability m (d m)) + (α / (r : ℝ)) * n * Real.log n‖ ≤ C * ‖n‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ n), hident]
  calc
    _ ≤ |Real.log (optimalProbability m (d m)) - (1 - (m : ℝ)) * Real.log (d m : ℝ)| +
        |Real.log (d m : ℝ)| + (m : ℝ) * |e| := by
      have h1 := abs_sub
        ((Real.log (optimalProbability m (d m)) - (1 - (m : ℝ)) * Real.log (d m : ℝ)) +
          Real.log (d m : ℝ)) ((m : ℝ) * e)
      have h2 := abs_add_le
        (Real.log (optimalProbability m (d m)) - (1 - (m : ℝ)) * Real.log (d m : ℝ))
        (Real.log (d m : ℝ))
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg _)] at h1
      linarith
    _ ≤ (m : ℝ) + (K + |α| * n) + (m : ℝ) * K := by gcongr
    _ ≤ C * (m : ℝ) := by dsimp [C, n]; push_cast; nlinarith
    _ ≤ C * n := mul_le_mul_of_nonneg_left hmn hC

end RigidGHZ.SourceModel
