module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! Recovery of the individual marked-coordinate multiplicities, as integers.
The proof uses the actual strict superincreasing condition in the supplement. -/

@[expose] public section

namespace RigidGHZ.Supplement.Marked

open scoped BigOperators

/-- Each positive marked position is larger than the sum of preceding positions. -/
def Superincreasing {m : ℕ} (D : Finset (Fin m)) : Prop :=
  ∀ a ∈ D, 0 < a.val → ∑ b ∈ D.filter (fun b => b < a), b.val < a.val

 theorem weighted_abs_le {m : ℕ} (D : Finset (Fin m)) (ε : Fin m → ℤ)
    (hε : ∀ a ∈ D, |ε a| ≤ 1) :
    |∑ a ∈ D, (a.val : ℤ) * ε a| ≤ (∑ a ∈ D, a.val : ℕ) := by
  calc
    _ ≤ ∑ a ∈ D, |(a.val : ℤ) * ε a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ D, (a.val : ℤ) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      simpa using mul_le_mul_of_nonneg_left (hε a ha) (Int.natCast_nonneg a.val)
    _ = _ := by simp

/-- A zero signed sum of a strictly superincreasing family has no nonzero
coefficient at a positive position. The position zero is handled by total mass. -/
 theorem signed_unique_positive {m : ℕ} (D : Finset (Fin m)) (ε : Fin m → ℤ)
    (hD : Superincreasing D) (hε : ∀ a ∈ D, |ε a| ≤ 1)
    (hsum : ∑ a ∈ D, (a.val : ℤ) * ε a = 0) :
    ∀ a ∈ D, 0 < a.val → ε a = 0 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert a D hlt ih =>
    have haD : a ∉ D := by
      intro ha
      exact (lt_irrefl a) (hlt a ha)
    have hD' : Superincreasing D := by
      intro b hb hbpos
      have h := hD b (Finset.mem_insert_of_mem hb) hbpos
      have hle : ∑ c ∈ D.filter (fun c => c < b), c.val ≤
          ∑ c ∈ (insert a D).filter (fun c => c < b), c.val := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.filter_subset_filter _ (Finset.subset_insert _ _)
      exact hle.trans_lt h
    have hε' : ∀ b ∈ D, |ε b| ≤ 1 := fun b hb => hε b (Finset.mem_insert_of_mem hb)
    have hzero : 0 < a.val → ε a = 0 := by
      intro hapos
      have hfilter : (insert a D).filter (fun b => b < a) = D := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hb, hba⟩
          · exact (lt_irrefl _ hba).elim
          · exact hb
        · intro hb
          exact ⟨Or.inr hb, hlt b hb⟩
      have hsmall := hD a (Finset.mem_insert_self _ _) hapos
      rw [hfilter] at hsmall
      have hsplit : (a.val : ℤ) * ε a = - ∑ b ∈ D, (b.val : ℤ) * ε b := by
        rw [Finset.sum_insert haD] at hsum
        omega
      have hbound : |(a.val : ℤ) * ε a| < (a.val : ℤ) := by
        rw [hsplit, abs_neg]
        exact (weighted_abs_le D ε hε').trans_lt (by exact_mod_cast hsmall)
      have hcoef := hε a (Finset.mem_insert_self _ _)
      have hcoef' := abs_le.mp hcoef
      by_contra hne
      have hcases : ε a = -1 ∨ ε a = 1 := by omega
      rcases hcases with h | h <;> simp [h, abs_of_nonneg (Int.natCast_nonneg a.val)] at hbound
    have hterm : (a.val : ℤ) * ε a = 0 := by
      by_cases ha : a.val = 0
      · simp [ha]
      · rw [hzero (by omega), mul_zero]
    have hrest : ∑ b ∈ D, (b.val : ℤ) * ε b = 0 := by
      simpa only [Finset.sum_insert haD, hterm, zero_add] using hsum
    intro b hb hbpos
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hzero hbpos
    · exact ih hD' hε' hrest b hb hbpos

/-- Recovery in the signed form needed by slicing: congruence plus the strict
range bound first gives an integer equality, and total mass fixes position zero. -/
 theorem signed_recovery {m : ℕ} (D : Finset (Fin m)) (ε : Fin m → ℤ)
    (hsmall : ∑ a ∈ D, a.val < m) (hD : Superincreasing D)
    (houtside : ∀ a ∉ D, ε a = 0) (hε : ∀ a ∈ D, |ε a| ≤ 1)
    (hmass : ∑ a, ε a = 0)
    (hcong : (m : ℤ) ∣ ∑ a, (a.val : ℤ) * ε a) : ∀ a, ε a = 0 := by
  have hrestrict : ∑ a, (a.val : ℤ) * ε a = ∑ a ∈ D, (a.val : ℤ) * ε a := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a ha haD
    simp [houtside a haD]
  have hweighted : ∑ a ∈ D, (a.val : ℤ) * ε a = 0 := by
    rw [hrestrict] at hcong
    exact Int.eq_zero_of_abs_lt_dvd hcong
      ((weighted_abs_le D ε hε).trans_lt (by exact_mod_cast hsmall))
  have hpos : ∀ a : Fin m, 0 < a.val → ε a = 0 := by
    intro a ha
    by_cases haD : a ∈ D
    · exact signed_unique_positive D ε hD hε hweighted a haD ha
    · exact houtside a haD
  intro a
  by_cases hapos : 0 < a.val
  · exact hpos a hapos
  · have hsingle : ∑ b, ε b = ε a := by
      apply Finset.sum_eq_single a
      · intro b hb hba
        apply hpos
        have : b.val ≠ a.val := fun h => hba (Fin.ext h)
        omega
      · simp
    rw [hsingle] at hmass
    exact hmass

/-- Supplementary marked-multiplicity lemma, with nonnegative multiplicities.
It is slightly stronger than the printed statement: requiring `0 ∈ D` when
`D` is nonempty is unnecessary once total mass is included. -/
 theorem recovery {m : ℕ} (D : Finset (Fin m)) (n : Fin m → ℕ)
    (hsmall : ∑ a ∈ D, a.val < m) (hD : Superincreasing D)
    (houtside : ∀ a ∉ D, n a = 1) (hmarked : ∀ a ∈ D, n a ≤ 2)
    (hmass : ∑ a, n a = m)
    (hcong : (m : ℤ) ∣ ∑ a, (a.val : ℤ) * ((n a : ℤ) - 1)) :
    ∀ a, n a = 1 := by
  have hε : ∀ a, (n a : ℤ) - 1 = 0 := by
    apply signed_recovery D (fun a => (n a : ℤ) - 1) hsmall hD
    · intro a ha
      simp [houtside a ha]
    · intro a ha
      rw [abs_le]
      have hn := hmarked a ha
      constructor <;> omega
    · rw [Finset.sum_sub_distrib]
      simp only [← Nat.cast_sum, hmass, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]
    · exact hcong
  intro a
  have := hε a
  omega

end RigidGHZ.Supplement.Marked
