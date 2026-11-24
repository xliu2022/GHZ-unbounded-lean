module

public import RigidGHZ.UpperBounds.Corollaries
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Asymptotic upper bounds, expressed with explicit dominating functions.
This avoids an opaque extremal operator: the envelope bounds every ordinary
rigid hypergraph at every positive matching size, and has the claimed leading
constant. In particular every attainable dimension sequence is subpolynomial
of degree `r-1`. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open Asymptotics Filter Topology

theorem beta_sub_log_bounds {m : ℕ} (hm : 5 ≤ m) :
    0 ≤ beta m - Real.log (m : ℝ) ∧ beta m - Real.log (m : ℝ) ≤ 1 := by
  have hlo : Real.log (m : ℝ) ≤ beta m := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by linarith)
      _ ≤ beta m := logarithm_le_beta hm
  have hhi : beta m ≤ 1 + Real.log (m : ℝ) := by
    rw [beta_eq_harmonic hm, harmonic_eq_rat]
    exact _root_.harmonic_le_one_add_log m
  constructor <;> linarith

theorem beta_log_error : (fun m : ℕ => beta m - Real.log (m : ℝ)) =O[atTop]
    (fun _ : ℕ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 5] with m hm
  have h := beta_sub_log_bounds hm
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1, abs_one, mul_one] using h.2

theorem log_nat_tendsto : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem beta_equivalent_log : beta ~[atTop] (fun m : ℕ => Real.log (m : ℝ)) := by
  have h : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun m : ℕ => Real.log (m : ℝ)) :=
    isLittleO_one_left_iff ℝ |>.mpr (tendsto_norm_atTop_atTop.comp log_nat_tendsto)
  exact beta_log_error.trans_isLittleO h

theorem log_nat_mul_equivalent (r : ℕ) (hr : 0 < r) :
    (fun m : ℕ => Real.log ((r * m : ℕ) : ℝ)) ~[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  have h : (fun m : ℕ => Real.log (r : ℝ) + Real.log (m : ℝ)) ~[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) :=
    IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp log_nat_tendsto)
  apply h.congr_left
  filter_upwards [eventually_ge_atTop 1] with m hm
  simp only [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr (by omega : r ≠ 0))
    (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))]

/-- The exact unrestricted upper envelope. -/
def unrestrictedEnvelope (r m : ℕ) : ℝ := ((r * m).choose (r - 1) : ℝ) / beta m

/-- The exact balanced multipartite upper envelope. -/
def balancedEnvelope (r m : ℕ) : ℝ := (m : ℝ) ^ (r - 1) / beta m

theorem unrestricted_envelope_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    {H : Hypergraph (Fin (r * m))} (hU : Uniform H r) (hR : IsRigid H d) :
    (d : ℝ) ≤ unrestrictedEnvelope r m := by
  have h := unrestricted_harmonic_shadow (m := m) hR hU hr (by simp)
  have hc : ((shadow H (r - 1)).card : ℝ) ≤ (r * m).choose (r - 1) := by
    exact_mod_cast h.2.2
  exact (le_div_iff₀ (beta_pos hm)).mpr (h.1.trans (h.2.1.trans hc))

theorem balanced_envelope_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    {H : Hypergraph (Fin r × Fin m)} (hP : BalancedPartite H r m) (hR : IsRigid H d) :
    (d : ℝ) ≤ balancedEnvelope r m :=
  (le_div_iff₀ (beta_pos hm)).mpr (balanced_partite_harmonic_bound hr hR hP)

/-- The coefficient of the unrestricted asymptotic bound is `1/(r-1)!`. -/
theorem unrestricted_envelope_equivalent (r : ℕ) (hr : 2 ≤ r) :
    unrestrictedEnvelope r ~[atTop]
      (fun m : ℕ => (1 / ((r - 1).factorial : ℝ)) *
        (((r * m : ℕ) : ℝ) ^ (r - 1) / Real.log ((r * m : ℕ) : ℝ))) := by
  have hmul : Tendsto (fun m : ℕ => r * m) atTop atTop := by
    apply tendsto_atTop_mono (f := fun m : ℕ => m) (g := fun m => r * m) _ tendsto_id
    intro m
    calc
      m = 1 * m := by omega
      _ ≤ r * m := Nat.mul_le_mul_right m (by omega)
  have hc := (isEquivalent_choose (r - 1)).comp_tendsto hmul
  have hb := beta_equivalent_log.trans (log_nat_mul_equivalent r (by omega)).symm
  apply (hc.div hb).congr_right
  exact Eventually.of_forall (fun m => by dsimp; ring)

/-- The coefficient of the balanced multipartite bound is one. -/
theorem balanced_envelope_equivalent (r : ℕ) :
    balancedEnvelope r ~[atTop]
      (fun m : ℕ => (m : ℝ) ^ (r - 1) / Real.log (m : ℝ)) :=
  IsEquivalent.refl.div beta_equivalent_log

theorem power_div_log_littleO (r k : ℕ) (hr : 0 < r) :
    (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ k / Real.log ((r * m : ℕ) : ℝ)) =o[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ k) := by
  have hmul : Tendsto (fun m : ℕ => ((r * m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (Nat.cast_pos.mpr hr)
  have hinv : (fun m : ℕ => (Real.log ((r * m : ℕ) : ℝ))⁻¹) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr
      (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hmul))
  simpa only [div_eq_mul_inv, mul_one] using
    (isBigO_refl (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ k) atTop).mul_isLittleO hinv

/-- Every attainable dimension sequence is `o(n^(r-1))`; at `r=3` this is
the paper's `f₃(n)=o(n²)` conclusion along multiples of three. -/
theorem attainable_dimension_littleO (r : ℕ) (hr : 2 ≤ r) (d : ℕ → ℕ)
    (hd : ∀ m : ℕ, 1 ≤ m → ∃ H : Hypergraph (Fin (r * m)),
      Uniform H r ∧ IsRigid H (d m)) :
    (fun m : ℕ => (d m : ℝ)) =o[atTop]
      (fun m : ℕ => ((r * m : ℕ) : ℝ) ^ (r - 1)) := by
  have hbound : (fun m : ℕ => (d m : ℝ)) =O[atTop] unrestrictedEnvelope r := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 1] with m hm
    obtain ⟨H, hU, hR⟩ := hd m hm
    have h := unrestricted_envelope_bound hr hm hU hR
    have hb : 0 ≤ unrestrictedEnvelope r m := by
      exact div_nonneg (Nat.cast_nonneg _) (beta_pos hm).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (d m : ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg hb, one_mul] using h
  exact hbound.trans (unrestricted_envelope_equivalent r hr).isBigO |>.trans_isLittleO
    ((power_div_log_littleO r (r - 1) (by omega)).const_mul_left _)

end RigidGHZ.UpperBounds
