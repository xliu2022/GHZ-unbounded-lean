module

public import RigidGHZ.Construction.SupportCardinality
public import RigidGHZ.Construction.NumericalLayout

/-! Exact owner counts for the numerical layout, before and after coercion. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleEstimates

def horizontalOwnerMass (k T H : ℝ) : ℝ :=
  nHorizontal k T H * ((T + T) * (H - 2 * D T) + (T - 1) * D T)

def verticalOwnerMass (k T H : ℝ) : ℝ :=
  nVertical k T H * (B k T * D T + (B k T - T - 1) * D T)

def fullOwnerMass (k T H : ℝ) : ℝ :=
  nFull k T H * (B k T * (H - 2 * D T) + (B k T - T - 1) * D T)

def shortOwnerMass (k T H : ℝ) : ℝ :=
  if D T ≤ shortHeight k T H then
    B k T * shortHeight k T H + (B k T - T - 1) * D T else 0

def ownerMass (k T H : ℝ) : ℝ :=
  horizontalOwnerMass k T H + verticalOwnerMass k T H + fullOwnerMass k T H + shortOwnerMass k T H

end RigidGHZ.RectangleEstimates

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

def roundedOwnerCount (k T H : ℕ) : ℕ :=
  nHorizontal k T H * ((T + T) * (H - 2 * gamma T) + (T - 1) * gamma T) +
  nVertical k T H * ((widthB k T - T + T) * gamma T + (widthB k T - T - 1) * gamma T) +
  nFull k T H * ((widthB k T - T + T) * (H - 2 * gamma T) + (widthB k T - T - 1) * gamma T) +
  shortIndicator k T H * ((widthB k T - T + T) * shortHeight k T H + (widthB k T - T - 1) * gamma T)

/-- This is the cardinality of the actual active support; it is independent of
where admissible private holes were chosen within their grid. -/
def supportCount (k T H R : ℕ) : ℕ :=
  1 + (T + 1) * roundedOwnerCount k T H + (T + 1) ^ 2 * R

 theorem numericalLayout_ownerCount (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (numericalLayout k T H hk hT hH).ownerCount = roundedOwnerCount k T H := rfl

 theorem roundedOwnerCount_cast (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (roundedOwnerCount k T H : ℝ) = ownerMass k T H := by
  have hm := natural_margins hk hT hH
  have hB : T ≤ widthB k T := by omega
  have hB1 : 1 ≤ widthB k T - T := by omega
  have hD : 2 * gamma T ≤ H := by omega
  have ht : 1 ≤ T := by omega
  by_cases hs : gamma T ≤ shortHeight k T H
  · have hsr : D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [roundedOwnerCount, shortIndicator, if_pos hs, one_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hB1, Nat.cast_sub hD,
      Nat.cast_sub ht, Nat.cast_ofNat, Nat.cast_one, widthB_cast, gamma_cast,
      ownerMass, horizontalOwnerMass, verticalOwnerMass, fullOwnerMass, shortOwnerMass, if_pos hsr]
    ring
  · have hsr : ¬ D (T : ℝ) ≤ (shortHeight k T H : ℝ) := by
      rw [← gamma_cast]; exact_mod_cast hs
    simp only [roundedOwnerCount, shortIndicator, if_neg hs, zero_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_sub hB1, Nat.cast_sub hD,
      Nat.cast_sub ht, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, widthB_cast, gamma_cast,
      ownerMass, horizontalOwnerMass, verticalOwnerMass, fullOwnerMass, shortOwnerMass, if_neg hsr]
    ring

 theorem supportCount_cast (k T H R : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    (supportCount k T H R : ℝ) =
      1 + ((T : ℝ) + 1) * ownerMass k T H + ((T : ℝ) + 1) ^ 2 * R := by
  simp only [supportCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
    roundedOwnerCount_cast k T H hk hT hH]

 theorem numerical_physicalSupport_card (k T H : ℕ) (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H)
    (X Z : Finset Point3)
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    (hZafter : ∀ z ∈ Z, (primaryLevels k T H * (T + 1) : ℕ) + (T : ℤ) + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T),
      ownerBlock (numericalLayout k T H hk hT hH).rectangles i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X) :
    (physicalSupport (T := T) (numericalLayout k T H hk hT hH).rectangles X Z).card =
      supportCount k T H Z.card := by
  let s := numericalLayout k T H hk hT hH
  have hm := natural_margins hk hT hH
  have hw : ∀ a, 1 ≤ (s.rectangles a).width := fun a =>
    (show 1 ≤ T by omega).trans (s.widths_ge hm.1.le a)
  have hj : ∀ a, T ≤ (s.rectangles a).height + 1 := by
    intro a
    have hg := s.heights_ge hm.2.le (shortIndicator_valid k T H) a
    have ht := le_gamma_add_one T
    omega
  exact s.physicalSupport_card_exact X Z hgrid hZafter hownerX hprivateX hw hj

/-- The exact tag-space balance in the constructed witness fixes the private
count, including all floors and the possible omitted short rectangle. -/
theorem private_count_cast_of_balance {k T H R ρ : ℕ} (hk : 1 ≤ k) (hT : 6 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H)
    (hbalance : (widthA k T + T) * (widthB k T + T) * (H + 2 * gamma T + 1) =
      (numericalLayout k T H hk hT hH).area + R +
        (widthA k T * widthB k T * H + ρ + 1)) :
    (R : ℝ) = privateAmount k T H ρ := by
  have h : ((widthA k T : ℝ) + T) * ((widthB k T : ℝ) + T) * ((H : ℝ) + 2 * gamma T + 1) =
      ((numericalLayout k T H hk hT hH).area : ℝ) + R +
        ((widthA k T : ℝ) * widthB k T * H + ρ + 1) := by exact_mod_cast hbalance
  rw [numericalLayout_area_cast, widthA_cast, widthB_cast, gamma_cast] at h
  unfold privateAmount
  linarith only [h]

end RigidGHZ.Rectangular
