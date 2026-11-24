module

public import RigidGHZ.Construction.NumericalLayout
public import RigidGHZ.Construction.PackedDemands

/-! Natural shared-arc counts satisfy the proved real calibration inequalities. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

theorem numericalLayout_proper_cast (k T H l : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    ((numericalLayout k T H hk hT hH).properDemand l : ℝ) =
      (nHorizontal k T H : ℝ) * ((H : ℝ) - 3 * D T + l) +
      (nVertical k T H : ℝ) * Q k T * l +
      (nFull k T H : ℝ) * ((H : ℝ) - 3 * D T + Q k T * l) +
      shortPrefixDemand (D T) (Q k T) (shortHeight k T H) l := by
  have hm := natural_margins hk hT hH
  have hB : 2 * T ≤ widthB k T := hm.1.le
  have hD : 3 * gamma T ≤ H := hm.2.le
  by_cases hs : gamma T ≤ shortHeight k T H
  · have hsr : D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.properDemand, numericalLayout, shortIndicator, if_pos hs,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD, Nat.cast_sub hs,
      Nat.cast_ofNat, Nat.cast_one, widthB_cast, gamma_cast, shortPrefixDemand, if_pos hsr,
      Q, one_mul]
  · have hsr : ¬ D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.properDemand, numericalLayout, shortIndicator, if_neg hs,
      zero_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, widthB_cast, gamma_cast,
      shortPrefixDemand, if_neg hsr, Q]

theorem numericalLayout_full_cast (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    ((numericalLayout k T H hk hT hH).fullDemand : ℝ) =
      ((nHorizontal k T H : ℝ) + nVertical k T H + nFull k T H) * D T * ((T : ℝ) - 1) +
      (nFull k T H : ℝ) * (B k T - 2 * T) * ((H : ℝ) - 3 * D T) +
      shortFullDemand (B k T) T (D T) (shortHeight k T H) := by
  have hm := natural_margins hk hT hH
  have hB : 2 * T ≤ widthB k T := hm.1.le
  have hD : 3 * gamma T ≤ H := hm.2.le
  have ht : 1 ≤ T := by omega
  by_cases hs : gamma T ≤ shortHeight k T H
  · have hsr : D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.fullDemand, numericalLayout, shortIndicator, if_pos hs,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD, Nat.cast_sub hs,
      Nat.cast_sub ht, Nat.cast_ofNat, Nat.cast_one, widthB_cast, gamma_cast,
      shortFullDemand, if_pos hsr, one_mul]
  · have hsr : ¬ D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [PackedLayout.fullDemand, numericalLayout, shortIndicator, if_neg hs,
      zero_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hD,
      Nat.cast_sub ht, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, widthB_cast, gamma_cast,
      shortFullDemand, if_neg hsr]

theorem numericalLayout_proper_supply (k T H l : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (numericalLayout k T H hk hT hH).properDemand l ≤
      widthA k T * H + widthA k T * widthB k T * l := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hi := integer_prefix_supply hkr hTr hH (Nat.cast_nonneg l)
  rw [← numericalLayout_proper_cast k T H l hk hT hH,
    ← widthA_cast, ← widthB_cast] at hi
  exact_mod_cast hi

theorem numericalLayout_full_supply (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (numericalLayout k T H hk hT hH).fullDemand ≤
      T * widthB k T * H + widthA k T * widthB k T * gamma T := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT
  have hi := integer_full_supply hkr hTr hH
  rw [← numericalLayout_full_cast k T H hk hT hH,
    ← widthA_cast, ← widthB_cast, ← gamma_cast] at hi
  exact_mod_cast hi

end RigidGHZ.Rectangular
