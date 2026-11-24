module

public import RigidGHZ.SourceModel.MainTheorem
public import RigidGHZ.SourceModel.SuccessAsymptotics

/-! Retaining an exact polynomial number of classes gives the concrete
success-probability and source-count asymptotics claimed in Section 5. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open Asymptotics Filter Topology

def retainedDimension (r m : ℕ) : ℕ :=
  max 1 ⌊growthConstant r * ((r * m : ℕ) : ℝ) ^
    (2 * ((r - 2 : ℕ) : ℝ) / 7)⌋₊

/-- The retained dimension is realized by actual ordinary coherent networks. -/
theorem retained_network (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ N : CoherentNetwork r m (retainedDimension r m),
      ∀ p : ℝ, 0 < p → p < 1 → N.ProducesGHZ p := by
  obtain ⟨D, hD, hlower⟩ := Growth.balanced_growth r m hr hm
  have hk : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
  have hbase : 0 < (m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3) := by
    apply div_pos (by exact_mod_cast (show 0 < m by omega))
    positivity
  have hDpos : 1 ≤ D := by
    have : (0 : ℝ) < D := (Real.rpow_pos_of_pos hbase _).trans_le hlower
    have : 0 < D := by exact_mod_cast this
    omega
  have hdD : retainedDimension r m ≤ D := by
    apply max_le hDpos
    apply Nat.floor_le_of_le
    rwa [growthConstant_scaling r m hr]
  obtain ⟨H, hU, hP, ⟨G⟩⟩ := hD.restrict (by omega) hm hdD
  let N : CoherentNetwork r m (retainedDimension r m) := ⟨H, hU, hP, G⟩
  refine ⟨N, fun p hp hp1 => N.producesGHZ (by omega) (by omega) ?_ p hp hp1⟩
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem retainedDimension_theta (r : ℕ) (hr : 3 ≤ r) :
    (fun m : ℕ => (retainedDimension r m : ℝ)) =Θ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ (2 * ((r - 2 : ℕ) : ℝ) / 7)) := by
  let α : ℝ := 2 * ((r - 2 : ℕ) : ℝ) / 7
  let f : ℕ → ℝ := fun m => growthConstant r * ((r * m : ℕ) : ℝ) ^ α
  have hα : 0 < α := by
    have : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
    dsimp [α]
    positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn : Tendsto (fun m : ℕ => ((r * m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using tendsto_natCast_atTop_atTop.const_mul_atTop hr0
  have hf : Tendsto f atTop atTop :=
    ((tendsto_rpow_atTop hα).comp hn).const_mul_atTop (growthConstant_pos hr)
  have hfloor := (isEquivalent_nat_floor (R := ℝ)).comp_tendsto hf
  have he : (fun m : ℕ => (retainedDimension r m : ℝ)) ~[atTop] f := by
    apply hfloor.congr_left
    filter_upwards [hf.eventually_ge_atTop 1] with m hm
    have hm' : 1 ≤ ⌊f m⌋₊ := (Nat.le_floor_iff' (by decide)).mpr (by simpa using hm)
    change (⌊f m⌋₊ : ℝ) = ((max 1 ⌊f m⌋₊ : ℕ) : ℝ)
    rw [max_eq_right hm']
  exact (isTheta_const_mul_right (growthConstant_pos hr).ne').mp he.isTheta

theorem source_count_theta (r : ℕ) (hr : 1 ≤ r) (α : ℝ) (d : ℕ → ℕ)
    (hθ : (fun m : ℕ => (d m : ℝ)) =Θ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ α)) :
    (fun m : ℕ => ((d m * m : ℕ) : ℝ)) =Θ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ (α + 1)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hmθ : (fun m : ℕ => (m : ℝ)) =Θ[atTop] (fun m : ℕ => ((r * m : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul] using
      ((isTheta_const_mul_right hr0.ne').mpr
        (isTheta_rfl : (fun m : ℕ => (m : ℝ)) =Θ[atTop] (fun m : ℕ => (m : ℝ))))
  have hl : (fun m : ℕ => (d m : ℝ) * (m : ℝ)) =ᶠ[atTop]
      (fun m : ℕ => ((d m * m : ℕ) : ℝ)) :=
    Eventually.of_forall (fun m => (Nat.cast_mul (d m) m).symm)
  have hg : (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ α * ((r * m : ℕ) : ℝ)) =ᶠ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ (α + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hn : (0 : ℝ) < (r * m : ℕ) := by
      exact_mod_cast (show 0 < r * m by positivity)
    rw [Real.rpow_add hn, Real.rpow_one]
  exact ⟨(hθ.mul hmθ).1.congr' hl hg, (hθ.mul hmθ).2.congr' hg hl⟩

theorem retained_source_count_theta (r : ℕ) (hr : 3 ≤ r) :
    (fun m : ℕ => ((retainedDimension r m * m : ℕ) : ℝ)) =Θ[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ (1 + 2 * ((r - 2 : ℕ) : ℝ) / 7)) := by
  simpa only [add_comm] using source_count_theta r (by omega)
    (2 * ((r - 2 : ℕ) : ℝ) / 7) (retainedDimension r) (retainedDimension_theta r hr)

theorem retained_success_log (r : ℕ) (hr : 3 ≤ r) :
    (fun m : ℕ => Real.log (optimalProbability m (retainedDimension r m)) +
      (2 * ((r - 2 : ℕ) : ℝ) / (7 * (r : ℝ))) * ((r * m : ℕ) : ℝ) *
        Real.log ((r * m : ℕ) : ℝ)) =O[atTop] (fun m : ℕ => ((r * m : ℕ) : ℝ)) := by
  have hα : 0 < 2 * ((r - 2 : ℕ) : ℝ) / 7 := by
    have : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
    positivity
  simpa only [div_div] using optimalProbability_log_asymptotic r (by omega)
    (2 * ((r - 2 : ℕ) : ℝ) / 7) hα (retainedDimension r) (retainedDimension_theta r hr)

theorem triplet_retained_success_log :
    (fun m : ℕ => Real.log (optimalProbability m (retainedDimension 3 m)) +
      (2 / 21 : ℝ) * ((3 * m : ℕ) : ℝ) * Real.log ((3 * m : ℕ) : ℝ)) =O[atTop]
        (fun m : ℕ => ((3 * m : ℕ) : ℝ)) := by
  convert retained_success_log 3 (by decide) using 1 <;> norm_num

end RigidGHZ.SourceModel
