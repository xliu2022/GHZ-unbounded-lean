module

public import RigidGHZ.UpperBounds.Shadow
public import RigidGHZ.UpperBounds.Partite
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Floor.Semiring

/-! The floor bounds, small harmonic constants and logarithmic consequences
of Theorem 4.1. All bounds apply pointwise to ordinary rigid hypergraphs. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

theorem harmonic_eq_rat (m : ℕ) : harmonic m = ((_root_.harmonic m : ℚ) : ℝ) := by
  simp [harmonic, shiftedHarmonic, _root_.harmonic, one_div, add_comm]

theorem harmonic_succ (m : ℕ) : harmonic (m + 1) = harmonic m + 1 / ((m : ℝ) + 1) := by
  simp only [harmonic, shiftedHarmonic, Finset.sum_range_succ]
  rw [add_comm (1 : ℝ) (m : ℝ)]

theorem harmonic_ge_one {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) ≤ harmonic m := by
  have h0 : 0 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (f := fun j : ℕ => (1 : ℝ) / (1 + (j : ℝ)))
    (fun j _ => by positivity) h0
  simpa [harmonic, shiftedHarmonic] using h

theorem beta_pos {m : ℕ} (hm : 1 ≤ m) : 0 < beta m := by
  by_cases he : m = 1
  · simp [beta, he]
  · rw [beta, if_neg he]
    exact lt_min (by positivity) (lt_of_lt_of_le zero_lt_one (harmonic_ge_one hm))

theorem harmonic_le_half {m : ℕ} (hm : 5 ≤ m) : harmonic m ≤ (m : ℝ) / 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [harmonic, shiftedHarmonic, Finset.sum_range_succ]
  | succ n hn ih =>
    rw [harmonic_succ]
    have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hterm : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    push_cast
    linarith

theorem beta_eq_harmonic {m : ℕ} (hm : 5 ≤ m) : beta m = harmonic m := by
  rw [beta, if_neg (by omega : m ≠ 1), min_eq_right]
  simpa using harmonic_le_half hm

theorem beta_two : beta 2 = 1 := by
  norm_num [beta, harmonic, shiftedHarmonic, Finset.sum_range_succ]

theorem beta_three : beta 3 = (3 : ℝ) / 2 := by
  norm_num [beta, harmonic, shiftedHarmonic, Finset.sum_range_succ]

theorem beta_four : beta 4 = 2 := by
  norm_num [beta, harmonic, shiftedHarmonic, Finset.sum_range_succ]

theorem logarithm_le_beta {m : ℕ} (hm : 5 ≤ m) :
    Real.log ((m : ℝ) + 1) ≤ beta m := by
  rw [beta_eq_harmonic hm, harmonic_eq_rat]
  simpa only [Nat.cast_add, Nat.cast_one] using _root_.log_add_one_le_harmonic m

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Hypergraph V}

theorem unrestricted_floor_bound {r m d : ℕ} (hR : IsRigid H d) (hU : Uniform H r)
    (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) :
    d ≤ ⌊((r * m).choose (r - 1) : ℝ) / beta m⌋₊ := by
  have h := unrestricted_harmonic_shadow hR hU hr hV
  have hc : ((shadow H (r - 1)).card : ℝ) ≤ (r * m).choose (r - 1) := by
    exact_mod_cast h.2.2
  apply Nat.le_floor
  exact (le_div_iff₀ (beta_pos hm)).mpr (h.1.trans (h.2.1.trans hc))

theorem balanced_partite_floor_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    d ≤ ⌊(m : ℝ) ^ (r - 1) / beta m⌋₊ := by
  apply Nat.le_floor
  exact (le_div_iff₀ (beta_pos hm)).mpr (balanced_partite_harmonic_bound hr hR hP)

/-- An explicit logarithmic upper bound, with the exact binomial numerator. -/
theorem unrestricted_log_bound {r m d : ℕ} (hR : IsRigid H d) (hU : Uniform H r)
    (hr : 2 ≤ r) (hm : 5 ≤ m) (hV : Fintype.card V = r * m) :
    (d : ℝ) ≤ ((r * m).choose (r - 1) : ℝ) / Real.log ((m : ℝ) + 1) := by
  have h := unrestricted_harmonic_shadow hR hU hr hV
  have hc : ((shadow H (r - 1)).card : ℝ) ≤ (r * m).choose (r - 1) := by
    exact_mod_cast h.2.2
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1)))).mpr
  exact (mul_le_mul_of_nonneg_left (logarithm_le_beta hm) (Nat.cast_nonneg d)).trans
    (h.1.trans (h.2.1.trans hc))

theorem balanced_partite_log_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 5 ≤ m)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    (d : ℝ) ≤ (m : ℝ) ^ (r - 1) / Real.log ((m : ℝ) + 1) := by
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1)))).mpr
  exact (mul_le_mul_of_nonneg_left (logarithm_le_beta hm) (Nat.cast_nonneg d)).trans
    (balanced_partite_harmonic_bound hr hR hP)

theorem tripartite_four_upper {d : ℕ} (hR : IsRigid H d)
    (hP : BalancedPartite H 3 4) : d ≤ 8 := by
  have h := balanced_partite_harmonic_bound (by decide : 2 ≤ 3) hR hP
  rw [beta_four] at h
  norm_num at h
  exact_mod_cast (show (d : ℝ) ≤ 8 by linarith)

end RigidGHZ.UpperBounds
