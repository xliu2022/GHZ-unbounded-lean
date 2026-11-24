module

public import RigidGHZ.Construction.PlanarHeight
public import Mathlib.Data.Int.Interval

/-! Tag-region sections and validity of the planar external anchor pools. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

abbrev Lattice := ℤ × ℤ

def box (lx ux ly uy : ℤ) : Finset Lattice :=
  (Finset.Ico lx ux) ×ˢ (Finset.Ico ly uy)

def tagRectangle (w h b : ℕ) : Finset Lattice :=
  box b (b + w) (gamma b) (gamma b + h + 1)

def tagRegion (w h T : ℕ) : Finset Lattice :=
  (Finset.range (T + 1)).biUnion (tagRectangle w h)

def projectionEnvelope (w h : ℕ) : Finset Lattice := box 0 w 0 (h + 1)

def translate (b : ℕ) (x : Lattice) : Lattice := (x.1 + b, x.2 + gamma b)

theorem gamma_add (a b : ℕ) : gamma (a + b) = gamma a + gamma b + a * b := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, gamma_succ, ih, gamma_succ]; ring

theorem gamma_int_mono {a b : ℕ} (h : a ≤ b) : (gamma a : ℤ) ≤ gamma b := by
  exact_mod_cast gamma_mono h

theorem gamma_int_succ (a : ℕ) : (gamma (a + 1) : ℤ) = gamma a + a := by
  exact_mod_cast gamma_succ a

theorem gamma_difference_mono {a b c : ℕ} (hbc : b ≤ c) :
    (gamma (a + b) : ℤ) - gamma b ≤ gamma (a + c) - gamma c := by
  simp only [gamma_add, Nat.cast_add, Nat.cast_mul]
  have ha : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have hbc' : (b : ℤ) ≤ c := by exact_mod_cast hbc
  nlinarith

/-- Consecutive vertical intervals overlap, so their union has no gaps. -/
theorem exists_gamma_band {h a b : ℕ} (hab : a ≤ b) (hb : b ≤ h + 1)
    {y : ℤ} (hylo : (gamma a : ℤ) ≤ y) (hyhi : y ≤ h + (gamma b : ℤ)) :
    ∃ c : ℕ, a ≤ c ∧ c ≤ b ∧ (gamma c : ℤ) ≤ y ∧ y ≤ h + (gamma c : ℤ) := by
  induction b generalizing a y with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact ⟨0, le_refl _, le_refl _, hylo, hyhi⟩
  | succ b ih =>
    by_cases hab' : a ≤ b
    · by_cases hyle : y ≤ h + (gamma b : ℤ)
      · obtain ⟨c, hac, hcb, hlo, hhi⟩ := ih hab' (by omega) hylo hyle
        exact ⟨c, hac, by omega, hlo, hhi⟩
      · refine ⟨b + 1, hab, le_refl _, ?_, hyhi⟩
        have hg := gamma_int_succ b
        omega
    · have ha : a = b + 1 := by omega
      subst a
      exact ⟨b + 1, le_refl _, le_refl _, hylo, hyhi⟩

/-- A uniform description of every vertical section used by the external pools. -/
theorem tagRegion_contains_band {w h T a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hbH : b ≤ h + 1) {x y : ℤ} (hxlo : (b : ℤ) ≤ x) (hxhi : x < a + (w : ℤ))
    (hylo : (gamma a : ℤ) ≤ y) (hyhi : y ≤ h + (gamma b : ℤ)) :
    (x, y) ∈ tagRegion w h T := by
  obtain ⟨c, hac, hcb, hyc, hyc'⟩ := exists_gamma_band hab hbH hylo hyhi
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_range.mpr (by omega), ?_⟩
  simp only [tagRectangle, box, Finset.mem_product, Finset.mem_Ico]
  omega

theorem translate_envelope_mem {w h T b : ℕ} (hb : b ≤ T) {x : Lattice}
    (hx : x ∈ projectionEnvelope w h) : translate b x ∈ tagRegion w h T := by
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
  simp only [projectionEnvelope, tagRectangle, box, translate,
    Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

/-- Prefix pool: the right column and upper strip. -/
def prefixColumn (w h T j : ℕ) : Finset Lattice :=
  box ((w : ℤ) + T - j) ((w : ℤ) + T - j + 1)
    ((gamma T : ℤ) - gamma (j - 1)) ((h : ℤ) + gamma T - gamma (j - 1) + 1)

def prefixStrip (w h T j : ℕ) : Finset Lattice :=
  box T w ((h : ℤ) + 1 + gamma T - gamma j)
    ((h : ℤ) + 1 + gamma T - gamma (j - 1))

/-- Suffix pool: the left column and lower strip. -/
def suffixColumn (w h T j : ℕ) : Finset Lattice :=
  box (-(j : ℤ)) (-(j : ℤ) + 1) (-(gamma j : ℤ))
    ((h : ℤ) - gamma T + gamma (T - j) + 1)

def suffixStrip (w h T j : ℕ) : Finset Lattice :=
  box 0 ((w : ℤ) - T) (-(gamma j : ℤ)) (-(gamma (j - 1) : ℤ))

/-- Rise of the lower boundary in a late column. -/
def rise (a b : ℕ) : ℤ := (gamma b : ℤ) - gamma (b - a)

def lowerColumn (w a j : ℕ) : Finset Lattice :=
  box ((w : ℤ) - 1 - a) ((w : ℤ) - a) (-rise a j) (-rise a (j - 1))

theorem rise_nonneg (a b : ℕ) : 0 ≤ rise a b := by
  exact sub_nonneg.mpr (gamma_int_mono (Nat.sub_le _ _))

theorem rise_succ (a b : ℕ) : rise a (b + 1) = rise a b + min a b := by
  by_cases hba : b < a
  · have h1 : b - a = 0 := by omega
    have h2 : b + 1 - a = 0 := by omega
    simp only [rise, h1, h2, gamma_zero, Nat.cast_zero, sub_zero,
      min_eq_right (Nat.le_of_lt hba), gamma_int_succ]
  · have h1 : b + 1 - a = (b - a) + 1 := by omega
    have hg := gamma_int_succ (b - a)
    have hb := gamma_int_succ b
    have hsub : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := by omega
    simp only [rise, h1, min_eq_left (by omega : a ≤ b)]
    omega

theorem rise_mono (a : ℕ) {b c : ℕ} (hbc : b ≤ c) : rise a b ≤ rise a c := by
  exact monotone_nat_of_le_succ (fun b => by rw [rise_succ]; omega) hbc

theorem prefixColumn_valid {w h T j b : ℕ} (hT : 1 ≤ T) (hj : 1 ≤ j)
    (hjT : j ≤ T) (hb : b < j) (hw : 2 * T ≤ w) (hh : T ≤ h + 1)
    {x : Lattice} (hx : x ∈ prefixColumn w h T j) :
    translate b x ∈ tagRegion w h T ∧ x ∉ projectionEnvelope w h ∧
      (w : ℤ) ≤ (translate b x).1 := by
  have hγ := gamma_int_mono (show b ≤ j - 1 by omega)
  have hdiff := gamma_difference_mono (a := T - j + 1) (show b ≤ j - 1 by omega)
  have hsum : T - j + 1 + (j - 1) = T := by omega
  rw [hsum] at hdiff
  simp only [prefixColumn, box, Finset.mem_product, Finset.mem_Ico] at hx
  refine ⟨?_, ?_, ?_⟩
  · apply tagRegion_contains_band (a := T - j + 1 + b) (b := T) (by omega)
      (le_refl _) hh
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
  · simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [translate]; omega

theorem suffixColumn_valid {w h T j b : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hjb : j ≤ b) (hbT : b ≤ T) (hw : T ≤ w) (hh : T ≤ h + 1)
    {x : Lattice} (hx : x ∈ suffixColumn w h T j) :
    translate b x ∈ tagRegion w h T ∧ x ∉ projectionEnvelope w h ∧
      (translate b x).1 < (T : ℤ) := by
  have hγ := gamma_int_mono hjb
  have hdiff := gamma_difference_mono (a := j) (show b - j ≤ T - j by omega)
  have hsum1 : j + (b - j) = b := by omega
  have hsum2 : j + (T - j) = T := by omega
  rw [hsum1, hsum2] at hdiff
  simp only [suffixColumn, box, Finset.mem_product, Finset.mem_Ico] at hx
  refine ⟨?_, ?_, ?_⟩
  · apply tagRegion_contains_band (a := 0) (b := b - j) (Nat.zero_le _) (by omega) (by omega)
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
    · simp only [gamma_zero, Nat.cast_zero]
      try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
  · simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [translate]; omega

theorem prefixStrip_valid {w h T j b : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hb : b < j) (hh : gamma T ≤ h)
    {x : Lattice} (hx : x ∈ prefixStrip w h T j) :
    translate b x ∈ tagRegion w h T ∧ x ∉ projectionEnvelope w h ∧
      (h : ℤ) < (translate b x).2 := by
  have hγj := gamma_int_mono hjT
  have hγb := gamma_int_mono (show b ≤ j - 1 by omega)
  simp only [prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨T, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [tagRectangle, box, translate, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [translate]; omega

theorem suffixStrip_valid {w h T j b : ℕ} (hj : 1 ≤ j) (hjb : j ≤ b)
    (hbT : b ≤ T) (hh : gamma T ≤ h)
    {x : Lattice} (hx : x ∈ suffixStrip w h T j) :
    translate b x ∈ tagRegion w h T ∧ x ∉ projectionEnvelope w h ∧
      (translate b x).2 < (gamma T : ℤ) := by
  have hγj := gamma_int_mono hjb
  have hγb := gamma_int_mono hbT
  simp only [suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [tagRectangle, box, translate, gamma_zero, Nat.cast_zero,
      Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [translate]; omega

theorem lowerColumn_valid {w h T a j b : ℕ} (ha : a < T) (hj : 1 ≤ j)
    (hjb : j ≤ b) (hbT : b ≤ T) (hw : 2 * T ≤ w) (hh : T ≤ h + 1)
    {x : Lattice} (hx : x ∈ lowerColumn w a j) :
    translate b x ∈ tagRegion w h T ∧ x ∉ projectionEnvelope w h ∧
      (translate b x).2 < (gamma T : ℤ) := by
  have hmon := rise_mono a hjb
  have hnon := rise_nonneg a (j - 1)
  have hγb := gamma_int_mono hbT
  have hγlo := gamma_int_mono (show b - a ≤ T by omega)
  simp only [lowerColumn, box, Finset.mem_product, Finset.mem_Ico] at hx
  refine ⟨?_, ?_, ?_⟩
  · apply tagRegion_contains_band (a := b - a) (b := T) (by omega) (le_refl _) hh
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      omega
    · try dsimp [translate]
      unfold rise at hmon hx
      omega
    · try dsimp [translate]
      omega
  · simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [translate]; omega

end RigidGHZ.Planar
