module

public import RigidGHZ.UpperBounds.FiniteAverage
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Independent representative averaging

The proof uses finite sums over all independent representative choices. Integrals
are only used to evaluate the identity `1/(1+n) = integral_0^1 z^n` and to apply
the elementary Bernoulli bound to the resulting finite product.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators
open MeasureTheory

variable {B : Type*} [Fintype B] [DecidableEq B] {r : ℕ}

/-- Number of selected representatives belonging to their prescribed neighbor sets. -/
def hitCount (hit : B → Finset (Fin r)) (q : B → Fin r) : ℕ :=
  (Finset.univ.filter (fun b => q b ∈ hit b)).card

/-- Average reciprocal of one plus the number of independent hits. -/
def averageReciprocal (hit : B → Finset (Fin r)) : ℝ :=
  (∑ q : B → Fin r, 1 / (1 + (hitCount hit q : ℝ))) / (r : ℝ) ^ Fintype.card B

theorem finiteAverage_reciprocal_eq (hit : B → Finset (Fin r)) :
    finiteAverage (fun q : B → Fin r => 1 / (1 + (hitCount hit q : ℝ))) =
      averageReciprocal hit := by
  simp only [finiteAverage, averageReciprocal, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]

theorem indicator_sum_div (hr : 0 < r) (s : Finset (Fin r)) (z : ℝ) :
    (∑ x : Fin r, if x ∈ s then z else 1) / (r : ℝ) =
      1 - ((s.card : ℝ) / r) * (1 - z) := by
  classical
  have hs : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hmem : Finset.univ.filter (fun x : Fin r => x ∈ s) = s := by ext x; simp
  have hnot : Finset.univ.filter (fun x : Fin r => ¬ x ∈ s) = Finset.univ \ s := by
    ext x
    simp
  rw [Finset.sum_ite, hmem, hnot]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hs]
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  field_simp
  ring

theorem generating_average (hr : 0 < r) (hit : B → Finset (Fin r)) (z : ℝ) :
    (∑ q : B → Fin r, z ^ hitCount hit q) / (r : ℝ) ^ Fintype.card B =
      ∏ b : B, (1 - ((hit b).card : ℝ) / r * (1 - z)) := by
  classical
  have hmon : ∀ q : B → Fin r, z ^ hitCount hit q =
      ∏ b : B, if q b ∈ hit b then z else 1 := by
    intro q
    simp [hitCount, Finset.prod_ite]
  calc
    _ = (∏ b : B, ∑ x : Fin r, if x ∈ hit b then z else 1) /
        (∏ _b : B, (r : ℝ)) := by
      rw [Fintype.prod_sum]
      simp only [Finset.prod_const, Finset.card_univ]
      congr 1
      exact Finset.sum_congr rfl (fun q _ => hmon q)
    _ = ∏ b : B, ((∑ x : Fin r, if x ∈ hit b then z else 1) / (r : ℝ)) :=
      (Finset.prod_div_distrib _ _).symm
    _ = _ := Finset.prod_congr rfl (fun b _ => indicator_sum_div hr (hit b) z)

theorem averageReciprocal_integral (hr : 0 < r) (hit : B → Finset (Fin r)) :
    averageReciprocal hit =
      ∫ z in (0 : ℝ)..1, ∏ b : B, (1 - ((hit b).card : ℝ) / r * (1 - z)) := by
  classical
  have hterm : ∀ q : B → Fin r,
      (1 : ℝ) / (1 + (hitCount hit q : ℝ)) =
        ∫ z in (0 : ℝ)..1, z ^ hitCount hit q := by
    intro q
    rw [integral_pow]
    simp [Nat.cast_add, add_comm]
  unfold averageReciprocal
  calc
    _ = (∑ q : B → Fin r, ∫ z in (0 : ℝ)..1, z ^ hitCount hit q) /
        (r : ℝ) ^ Fintype.card B := by
      congr 1
      exact Finset.sum_congr rfl (fun q _ => hterm q)
    _ = ∫ z in (0 : ℝ)..1,
        (∑ q : B → Fin r, z ^ hitCount hit q) / (r : ℝ) ^ Fintype.card B := by
      rw [intervalIntegral.integral_div]
      congr 1
      exact (intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun q z => z ^ hitCount hit q)
        (fun q _ => (continuous_id.pow (hitCount hit q)).intervalIntegrable 0 1)).symm
    _ = _ := intervalIntegral.integral_congr (fun z _ => generating_average hr hit z)

/-- Bernoulli's inequality compares each block with its individual possible neighbors. -/
theorem block_factor_bound (hr : 0 < r) (k : ℕ) (hk : k ≤ r)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 1 - ((k : ℝ) / r) * (1 - z) ∧
      1 - ((k : ℝ) / r) * (1 - z) ≤ (1 - (1 - z) / r) ^ k := by
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (k : ℝ) / r ≤ 1 := (div_le_one hrpos).mpr (by exact_mod_cast hk)
  have hu0 : 0 ≤ (1 - z) / r := div_nonneg (sub_nonneg.mpr hz1) hrpos.le
  have hu1 : (1 - z) / r ≤ 1 := (div_le_one hrpos).mpr (by linarith)
  constructor
  · have hm := mul_le_mul_of_nonneg_right hk1 (sub_nonneg.mpr hz1)
    nlinarith
  · have hb := one_add_mul_le_pow (a := -((1 - z) / (r : ℝ))) (by linarith) k
    convert hb using 1 <;> congr 1 <;> ring

theorem product_block_bound (hr : 0 < r) (hit : B → Finset (Fin r))
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∏ b : B, (1 - ((hit b).card : ℝ) / r * (1 - z))) ≤
      (1 - (1 - z) / r) ^ (∑ b, (hit b).card) := by
  classical
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro b _
    exact (block_factor_bound hr (hit b).card (by simpa using Finset.card_le_univ (hit b)) hz0 hz1).1
  · intro b _
    exact (block_factor_bound hr (hit b).card (by simpa using Finset.card_le_univ (hit b)) hz0 hz1).2

theorem integral_uniform_power (hr : 0 < r) (k : ℕ) :
    (∫ z in (0 : ℝ)..1, (1 - (1 - z) / r) ^ k) =
      (r : ℝ) / (k + 1) * (1 - (1 - 1 / (r : ℝ)) ^ (k + 1)) := by
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have hfun : (fun z : ℝ => (1 - (1 - z) / r) ^ k) =
      (fun z : ℝ => ((1 / (r : ℝ)) * z + (1 - 1 / (r : ℝ))) ^ k) := by
    funext z
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_comp_mul_add
    (fun x : ℝ => x ^ k) (one_div_ne_zero hrne) (1 - 1 / (r : ℝ))]
  have ht : (1 / (r : ℝ)) * 1 + (1 - 1 / (r : ℝ)) = 1 := by ring
  simp only [mul_zero, zero_add, ht, integral_pow, one_pow,
    one_div, inv_inv, smul_eq_mul]
  ring

/-- The conditional expectation estimate in the unrestricted shadow bound. -/
theorem independent_reciprocal_bound (hr : 0 < r) (hit : B → Finset (Fin r)) :
    averageReciprocal hit ≤
      (r : ℝ) / ((∑ b, (hit b).card) + 1) *
        (1 - (1 - 1 / (r : ℝ)) ^ ((∑ b, (hit b).card) + 1)) := by
  rw [averageReciprocal_integral hr hit, ← integral_uniform_power hr]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (by fun_prop : Continuous
      (fun z : ℝ => ∏ b : B, (1 - ((hit b).card : ℝ) / r * (1 - z)))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous
      (fun z : ℝ => (1 - (1 - z) / r) ^ (∑ b, (hit b).card))).intervalIntegrable _ _
  · intro z hz
    exact product_block_bound hr hit hz.1 hz.2

end RigidGHZ.UpperBounds
