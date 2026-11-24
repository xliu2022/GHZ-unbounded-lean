module

public import RigidGHZ.Construction.PlanarCounts

/-! Private holes on separated congruence-class columns in the planar factor. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

def privateColumnX (T a : ℕ) : ℤ := ((a : ℤ) + 3) * (T + 1) - 3

def privateHeights (h T a : ℕ) : Finset ℤ :=
  if a = 0 then Finset.Ico (3 * gamma T + auxiliaryHeight T) h
  else if a = 1 then insert (3 * (gamma T : ℤ)) (Finset.Ico (4 * gamma T + auxiliaryHeight T) h)
  else Finset.Ico (3 * gamma T) h

def privateColumn (h T a : ℕ) : Finset Lattice :=
  {privateColumnX T a} ×ˢ privateHeights h T a

def privatePool (p h T : ℕ) : Finset Lattice :=
  (Finset.range (p - 2)).biUnion (privateColumn h T)

theorem auxiliaryHeight_pos (T : ℕ) : 1 ≤ auxiliaryHeight T := by
  unfold auxiliaryHeight
  omega

theorem privateHeights_bounds {h T a : ℕ} (hh : 4 * gamma T + auxiliaryHeight T ≤ h)
    {y : ℤ} (hy : y ∈ privateHeights h T a) : (3 * gamma T : ℤ) ≤ y ∧ y < h := by
  have hB := auxiliaryHeight_pos T
  unfold privateHeights at hy
  split_ifs at hy <;> simp only [Finset.mem_Ico, Finset.mem_insert] at hy <;> omega

theorem privateColumnX_injective (T : ℕ) : Function.Injective (privateColumnX T) := by
  intro a c h
  dsimp [privateColumnX] at h
  have hT : (0 : ℤ) < T + 1 := by omega
  have he : (a : ℤ) + 3 = c + 3 := mul_right_cancel₀ (ne_of_gt hT) (by omega)
  omega

theorem privateColumn_disjoint (h T : ℕ) {a c : ℕ} (hac : a ≠ c) :
    Disjoint (privateColumn h T a) (privateColumn h T c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [privateColumn, Finset.mem_product, Finset.mem_singleton] at hx hy
  exact hac (privateColumnX_injective T (hx.1.symm.trans hy.1))

theorem privateColumn_card {h T : ℕ} (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (a : ℕ) :
    ((privateColumn h T a).card : ℤ) =
      if a = 0 then (h : ℤ) - 3 * gamma T - auxiliaryHeight T
      else if a = 1 then (h : ℤ) - 4 * gamma T - auxiliaryHeight T + 1
      else (h : ℤ) - 3 * gamma T := by
  have hB := auxiliaryHeight_pos T
  simp only [privateColumn, Finset.card_product, Finset.card_singleton, one_mul]
  unfold privateHeights
  split_ifs with ha ha
  · rw [Int.card_Ico, Int.toNat_of_nonneg (by omega)]
    ring
  · rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_Ico]; omega), Nat.cast_add,
      Int.card_Ico, Int.toNat_of_nonneg (by omega)]
    ring
  · rw [Int.card_Ico, Int.toNat_of_nonneg (by omega)]

theorem privatePool_card {p h T : ℕ} (hp : 4 ≤ p)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) :
    ((privatePool p h T).card : ℤ) =
      ((p : ℤ) - 2) * ((h : ℤ) - 3 * gamma T) - (gamma T + 2 * auxiliaryHeight T - 1) := by
  have hd : (↑(Finset.range (p - 2)) : Set ℕ).PairwiseDisjoint (privateColumn h T) := by
    intro a ha c hc hac
    exact privateColumn_disjoint h T hac
  rw [privatePool, Finset.card_biUnion hd, Nat.cast_sum]
  simp_rw [privateColumn_card hh]
  have hp' : p - 2 = 2 + (p - 4) := by omega
  rw [hp', Finset.sum_range_add]
  have hs : (∑ a ∈ Finset.range (p - 4),
      if 2 + a = 0 then (h : ℤ) - 3 * gamma T - auxiliaryHeight T
      else if 2 + a = 1 then (h : ℤ) - 4 * gamma T - auxiliaryHeight T + 1
      else (h : ℤ) - 3 * gamma T) = (p - 4 : ℕ) * ((h : ℤ) - 3 * gamma T) := by
    simp only [show ∀ a : ℕ, ¬2 + a = 0 from fun a => by omega,
      show ∀ a : ℕ, ¬2 + a = 1 from fun a => by omega, ite_false,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hs]
  norm_num [Finset.sum_range_succ]
  have hpcast : ((p - 4 : ℕ) : ℤ) = (p : ℤ) - 4 := by omega
  rw [hpcast]
  ring

theorem privatePool_capacity {k h T : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hh : minimumHeight k T ≤ h) : privateBudget k T ≤ (privatePool (32 * k) h T).card := by
  have hc := private_capacity_lower hk hT hh
  have hc' : ((privateBudget k T : ℕ) : ℤ) + gamma T + 2 * auxiliaryHeight T - 1 ≤
      (32 * (k : ℤ) - 2) * ((h : ℤ) - 3 * gamma T) := by exact_mod_cast hc
  have he := privatePool_card (by omega : 4 ≤ 32 * k) (minimumHeight_lower hh)
  have : ((privateBudget k T : ℕ) : ℤ) ≤ (privatePool (32 * k) h T).card := by
    rw [he]
    push_cast
    linarith
  exact_mod_cast this

theorem choose_private_holes {k h T R : ℕ} (hk : 1 ≤ k) (hT : 2 ≤ T)
    (hh : minimumHeight k T ≤ h) (hR : R ≤ privateBudget k T) :
    ∃ Z : Finset Lattice, Z ⊆ privatePool (32 * k) h T ∧ Z.card = R :=
  Finset.exists_subset_card_eq (hR.trans (privatePool_capacity hk hT hh))

/-- Congruence separation: subtracting one of `0,...,T` distinguishes the exits. -/
theorem private_columns_separate {T a c b d : ℕ} (hb : b ≤ T) (hd : d ≤ T)
    (he : privateColumnX T a - b = privateColumnX T c - d) : b = d := by
  dsimp [privateColumnX] at he
  by_cases hac : a = c
  · subst c
    omega
  · rcases lt_or_gt_of_ne hac with hac | hca
    · have hm := mul_nonneg (show (0 : ℤ) ≤ (c : ℤ) - a - 1 by omega)
        (show (0 : ℤ) ≤ T by omega)
      nlinarith
    · have hm := mul_nonneg (show (0 : ℤ) ≤ (a : ℤ) - c - 1 by omega)
        (show (0 : ℤ) ≤ T by omega)
      nlinarith

theorem private_inverse_disjoint {p h T b c : ℕ} (hb : b ≤ T) (hc : c ≤ T)
    (hbc : b ≠ c) : Disjoint (inverseSet (privatePool p h T) b) (inverseSet (privatePool p h T) c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp (mem_inverseSet.mp hx)
  obtain ⟨d, hd, hy⟩ := Finset.mem_biUnion.mp (mem_inverseSet.mp hy)
  simp only [privateColumn, Finset.mem_product, Finset.mem_singleton, translate] at hx hy
  exact hbc (private_columns_separate (a := a) (c := d) hb hc (by omega))

theorem private_inverse_envelope {p h T b : ℕ} (hT : 2 ≤ T) (hb : b ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) {x : Lattice}
    (hx : translate b x ∈ privatePool p h T) :
    x ∈ box 0 (p * (T + 1)) 0 h ∧ (2 * T : ℤ) ≤ x.1 ∧ (2 * gamma T : ℤ) ≤ x.2 := by
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  have ha' := Finset.mem_range.mp ha
  simp only [privateColumn, Finset.mem_product, Finset.mem_singleton, translate] at hx
  have hY := privateHeights_bounds hh hx.2
  have hγ := gamma_int_mono hb
  have hcolLower : (3 * T : ℤ) ≤ privateColumnX T a := by
    have hm := mul_nonneg (show (0 : ℤ) ≤ a by omega) (show (0 : ℤ) ≤ T by omega)
    dsimp [privateColumnX]
    nlinarith
  have hcolUpper : privateColumnX T a < (p : ℤ) * (T + 1) := by
    have hpa : a + 3 ≤ p := by omega
    have hm := mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - a - 3 by omega)
      (show (0 : ℤ) ≤ T by omega)
    dsimp [privateColumnX]
    nlinarith
  simp only [box, Finset.mem_product, Finset.mem_Ico]
  push_cast
  omega

theorem private_avoids_first {p h T b c : ℕ} (hT : 2 ≤ T) (hb : b ≤ T) (hc : c ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) {x : Lattice}
    (hx : translate b x ∈ privatePool p h T) : translate c x ∉ primaryOne (p * (T + 1)) h T := by
  have he := private_inverse_envelope hT hb hh hx
  have hγ := gamma_int_mono hc
  simp only [primaryOne, box, translate, Finset.mem_union, Finset.mem_product, Finset.mem_Ico]
  omega

theorem private_avoids_second {p h T b c : ℕ} (hT : 2 ≤ T) (hb : b ≤ T) (hc : c ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) {x : Lattice}
    (hx : translate b x ∈ privatePool p h T) : translate c x ∉ primaryTwo T := by
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  simp only [privateColumn, Finset.mem_product, Finset.mem_singleton, translate] at hx
  intro he
  simp only [primaryTwo, box, translate, Finset.mem_product, Finset.mem_Ico] at he
  have hγb := gamma_int_mono hb
  have hγc := gamma_int_mono hc
  by_cases ha0 : a = 0
  · subst a
    have hcb : b ≤ c := by dsimp [privateColumnX] at hx; omega
    have hγ := gamma_int_mono hcb
    simp only [privateHeights, ite_true, Finset.mem_Ico] at hx
    omega
  · by_cases ha1 : a = 1
    · subst a
      have hcb : c + 2 ≤ b := by dsimp [privateColumnX] at hx; omega
      have hγ := gamma_int_mono hcb
      have hg0 := gamma_int_succ c
      have hg1 := gamma_int_succ (c + 1)
      rw [show c + 1 + 1 = c + 2 by omega] at hg1
      simp only [privateHeights, show ¬(1 : ℕ) = 0 by omega, ite_false, ite_true,
        Finset.mem_insert, Finset.mem_Ico] at hx
      omega
    · have hcol : (5 * T + 2 : ℤ) ≤ privateColumnX T a := by
        have hm := mul_nonneg (show (0 : ℤ) ≤ (a : ℤ) - 2 by omega)
          (show (0 : ℤ) ≤ T by omega)
        dsimp [privateColumnX]
        nlinarith
      omega

end RigidGHZ.Planar
