module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Numeric estimates for the planar selector

These are the explicit height and active-support inequalities of Proposition A.3.
The two square-root estimates are proved by multiplying nonnegative linear
factors, which gives the same endpoint bound as the paper's convexity argument.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.PlanarEstimates

def D (T : ℝ) : ℝ := T * (T - 1) / 2
def B (T : ℝ) : ℝ := (T - 1) ^ 2 + 1
def width (k T : ℝ) : ℝ := 32 * k * (T + 1)
def R0 (k T : ℝ) : ℝ := (T ^ 3 - T) / 2 + width k T - 1
def heightNumerator (k T : ℝ) : ℝ := R0 k T + D T + 2 * B T - 1
def growthScale (k T : ℝ) : ℝ := 128 * k ^ 3 * T ^ 3 * Real.sqrt T

theorem D_nonneg {T : ℝ} (hT : 1 ≤ T) : 0 ≤ D T := by unfold D; positivity

theorem B_ge_one (T : ℝ) : 1 ≤ B T := by unfold B; nlinarith [sq_nonneg (T - 1)]

theorem width_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 1 ≤ T) : 0 < width k T := by
  unfold width
  positivity

theorem R0_pos {k T : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T) : 0 < R0 k T := by
  have h3 : 0 ≤ T ^ 3 - T := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T - 1) (show 0 ≤ T ^ 2 + T by positivity)]
  have hw : 32 ≤ width k T := by
    have hmul := mul_le_mul_of_nonneg_left hk (by linarith : 0 ≤ T + 1)
    unfold width
    nlinarith
  unfold R0
  linarith

theorem heightNumerator_nonneg {k T : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T) :
    0 ≤ heightNumerator k T := by
  have hR := R0_pos hk hT
  have hD := D_nonneg (by linarith : 1 ≤ T)
  have hB := B_ge_one T
  unfold heightNumerator
  linarith

theorem first_height_bound {T : ℝ} (hT : 2 ≤ T) : 4 * D T + B T ≤ 3 * T ^ 2 := by
  unfold D B
  nlinarith

theorem second_height_bound {k T c : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hc : c ≤ heightNumerator k T / (32 * k - 2) + 1) :
    3 * D T + c ≤ T ^ 3 / (60 * k) + 3 * T ^ 2 := by
  have hkpos : 0 < k := by linarith
  have hn := heightNumerator_nonneg hk hT
  have hdiv : heightNumerator k T / (32 * k - 2) ≤ heightNumerator k T / (30 * k) :=
    div_le_div_of_nonneg_left hn (by positivity) (by linarith)
  have hpart : heightNumerator k T / (30 * k) ≤
      T ^ 3 / (60 * k) + T ^ 2 / 12 + 16 * (T + 1) / 15 := by
    apply (div_le_iff₀ (by positivity : 0 < 30 * k)).mpr
    have he : (T ^ 3 / (60 * k) + T ^ 2 / 12 + 16 * (T + 1) / 15) * (30 * k) =
        T ^ 3 / 2 + (5 / 2 : ℝ) * k * T ^ 2 + 32 * k * (T + 1) := by
      field_simp
      ring
    rw [he]
    unfold heightNumerator R0 D B width
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg T)]
  have hT2 := mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T)
  unfold D
  linarith [hdiv, hpart, hT2]

theorem height_bound {k T c : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hc : c ≤ heightNumerator k T / (32 * k - 2) + 1) :
    max (4 * D T + B T) (3 * D T + c) ≤ T ^ 3 / (60 * k) + 3 * T ^ 2 := by
  apply max_le_iff.mpr
  refine ⟨?_, second_height_bound hk hT hc⟩
  have hn : 0 ≤ T ^ 3 / (60 * k) := by positivity
  linarith [first_height_bound hT]

theorem width_height_bound {k T h : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hh : h ≤ T ^ 3 / (60 * k) + 3 * T ^ 2) :
    width k T * h ≤ (8 / 15 : ℝ) * T ^ 4 + 145 * k * T ^ 3 := by
  have hw := width_pos hk (by linarith : 1 ≤ T)
  have hm := mul_le_mul_of_nonneg_left hh hw.le
  have he : width k T * (T ^ 3 / (60 * k) + 3 * T ^ 2) =
      (8 / 15 : ℝ) * T ^ 4 + (8 / 15 : ℝ) * T ^ 3 +
        96 * k * T ^ 3 + 96 * k * T ^ 2 := by
    unfold width
    field_simp
    ring
  rw [he] at hm
  have ht : 0 ≤ T ^ 3 - 2 * T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)]
  have hkt := mul_nonneg (by linarith : 0 ≤ k) ht
  have hk3 := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ T ^ 3 by positivity)
  nlinarith

/-- The paper's first convex endpoint estimate, proved without a convexity library. -/
theorem height_sqrt_bound {T : ℝ} (hT : 2 ≤ T) (hTupper : T ≤ 224 ^ 2) :
    (8 / 15 : ℝ) * T + 145 < 128 * Real.sqrt T := by
  have hx := Real.sqrt_nonneg T
  have hx2 := Real.sq_sqrt (by linarith : 0 ≤ T)
  have hlo : (7 / 5 : ℝ) ≤ Real.sqrt T := by nlinarith
  have hhi : Real.sqrt T ≤ 224 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

/-- The paper's second convex endpoint estimate. -/
theorem support_sqrt_bound {T : ℝ} (hT : 2 ≤ T) (hTupper : T ≤ 224 ^ 2) :
    T / 2 + 61 < 113 * Real.sqrt T := by
  have hx := Real.sqrt_nonneg T
  have hx2 := Real.sq_sqrt (by linarith : 0 ≤ T)
  have hlo : (1 : ℝ) ≤ Real.sqrt T := by nlinarith
  have hhi : Real.sqrt T ≤ 224 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

theorem width_height_lt_threshold {k T h : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hTupper : T ≤ 224 ^ 2) (hh : h ≤ T ^ 3 / (60 * k) + 3 * T ^ 2) :
    width k T * h < growthScale k T := by
  have hbound := width_height_bound hk hT hh
  have hs := height_sqrt_bound hT hTupper
  have hk0 : 0 < k := by linarith
  have hT0 : 0 < T := by linarith
  have hpow : k ≤ k ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k * (k + 1) by positivity)]
  have hfirst : (8 / 15 : ℝ) * T ^ 4 + 145 * k * T ^ 3 ≤
      k * T ^ 3 * ((8 / 15 : ℝ) * T + 145) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (pow_nonneg hT0.le 4)]
  have hsecond := mul_lt_mul_of_pos_left hs (show 0 < k * T ^ 3 by positivity)
  have hthird := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ 128 * T ^ 3 * Real.sqrt T by positivity)
  unfold growthScale
  nlinarith [hbound, hfirst, hsecond, hthird]

/-- All terms in the support count other than the two long strips. -/
def supportRest (k T : ℝ) : ℝ :=
  2 * D T * (width k T - T) + 2 * T * B T + (T + 1) * R0 k T + 1

theorem supportRest_identity (k T : ℝ) :
    supportRest k T = T ^ 4 / 2 +
      (32 * k + (3 / 2 : ℝ)) * T ^ 3 + (32 * k - (7 / 2 : ℝ)) * T ^ 2 +
        (32 * k + (5 / 2 : ℝ)) * T + 32 * k := by
  unfold supportRest D B R0 width
  ring

theorem supportRest_bound {k T : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T) :
    supportRest k T ≤ T ^ 4 / 2 + 61 * k * T ^ 3 := by
  have hp : 0 ≤ (T - 2) *
      ((28 * k - (9 / 8 : ℝ)) * T ^ 2 + (24 * k + (5 / 4 : ℝ)) * T + 16 * k) := by
    apply mul_nonneg (sub_nonneg.mpr hT)
    have hcoef : 0 ≤ 28 * k - (9 / 8 : ℝ) := by linarith
    positivity
  have he : (T - 2) *
      ((28 * k - (9 / 8 : ℝ)) * T ^ 2 + (24 * k + (5 / 4 : ℝ)) * T + 16 * k) =
      T ^ 4 / 2 + (60 * k + (3 / 8 : ℝ)) * T ^ 3 - supportRest k T := by
    rw [supportRest_identity]
    ring
  rw [he] at hp
  have hm := mul_nonneg (by linarith : 0 ≤ k - (3 / 8 : ℝ))
    (show 0 ≤ T ^ 3 by positivity)
  linarith

/-- The exact support inequality used after the geometric owner count. -/
theorem active_support_lt {k T h m u : ℝ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hTupper : T ≤ 224 ^ 2) (hh : 0 ≤ h)
    (hsize : width k T * h < m) (hm : growthScale k T < m)
    (hu : u ≤ 2 * T * h + supportRest k T) : k * u < m := by
  have hk0 : 0 < k := by linarith
  have hT0 : 0 < T := by linarith
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hm0 : 0 < m := lt_trans (by unfold growthScale; positivity) hm
  have hlong : k * (2 * T * h) < m / 16 := by
    have hkh := mul_nonneg hk0.le hh
    unfold width at hsize
    nlinarith
  have hr := supportRest_bound hk hT
  have hs := support_sqrt_bound hT hTupper
  have hrest1 : k * supportRest k T ≤ k ^ 2 * T ^ 3 * (T / 2 + 61) := by
    have hkr := mul_le_mul_of_nonneg_left hr hk0.le
    have hgap := mul_nonneg (show 0 ≤ k ^ 2 - k by nlinarith)
      (pow_nonneg hT0.le 4)
    nlinarith
  have hrest2 := mul_lt_mul_of_pos_left hs (show 0 < k ^ 2 * T ^ 3 by positivity)
  have hkk : k ^ 2 ≤ k ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg k)]
  have hrest3 := mul_le_mul_of_nonneg_right hkk
    (show 0 ≤ 113 * T ^ 3 * Real.sqrt T by positivity)
  have hrest : k * supportRest k T < (113 / 128 : ℝ) * m := by
    unfold growthScale at hm
    nlinarith [hrest1, hrest2, hrest3]
  have hku := mul_le_mul_of_nonneg_left hu hk0.le
  nlinarith

end RigidGHZ.PlanarEstimates
