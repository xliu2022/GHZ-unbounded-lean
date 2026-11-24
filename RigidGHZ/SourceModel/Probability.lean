module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Optimal binary source probabilities

We use a product proof of the optimization: multiplying the equal branch
probabilities counts each emitting-source factor once and every vacuum factor
`d-1` times. This reduces the upper bound and its equality condition to a
one-variable inequality, without Jensen's inequality or unproved analytic
hypotheses.
-/

@[expose] public section

namespace RigidGHZ.SourceModel

open scoped BigOperators

noncomputable def trialFactor (n : ℕ) (p : ℝ) : ℝ := p * (1 - p) ^ n

theorem trialFactor_pos (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < trialFactor n p := mul_pos hp (pow_pos (sub_pos.mpr hp1) _)

theorem optimal_probability_pos (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity

theorem optimal_probability_lt_one {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / (n + 1) < 1 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_one (by positivity)).2
  linarith

theorem normalized_log_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    Real.log (p / (1 / ((n : ℝ) + 1))) +
      (n : ℝ) * Real.log ((1 - p) / (1 - 1 / ((n : ℝ) + 1))) ≤ 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha : 0 < (1 : ℝ) / (n + 1) := by positivity
  have hb : 0 < (1 : ℝ) - 1 / (n + 1) :=
    sub_pos.mpr (optimal_probability_lt_one hn)
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp ha)
  have h2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hp1) hb)
  have hcancel : p / (1 / ((n : ℝ) + 1)) - 1 +
      (n : ℝ) * ((1 - p) / (1 - 1 / ((n : ℝ) + 1)) - 1) = 0 := by
    field_simp [hnr.ne']
    <;> ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hnr.le]

theorem normalized_log_strict {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hne : p ≠ 1 / ((n : ℝ) + 1)) :
    Real.log (p / (1 / ((n : ℝ) + 1))) +
      (n : ℝ) * Real.log ((1 - p) / (1 - 1 / ((n : ℝ) + 1))) < 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < (1 : ℝ) / (n + 1) := by positivity
  have hb : 0 < (1 : ℝ) - 1 / (n + 1) :=
    sub_pos.mpr (optimal_probability_lt_one hn)
  have h1 := Real.log_lt_sub_one_of_pos (div_pos hp ha)
    (fun h => hne ((div_eq_one_iff_eq ha.ne').1 h))
  have h2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hp1) hb)
  have hcancel : p / (1 / ((n : ℝ) + 1)) - 1 +
      (n : ℝ) * ((1 - p) / (1 - 1 / ((n : ℝ) + 1)) - 1) = 0 := by
    field_simp [hnr.ne']
    <;> ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hnr.le]

theorem log_trialFactor (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Real.log (trialFactor n p) = Real.log p + (n : ℝ) * Real.log (1 - p) := by
  rw [trialFactor, Real.log_mul hp.ne' (pow_pos (sub_pos.mpr hp1) n).ne', Real.log_pow]

theorem trialFactor_le_optimal {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    trialFactor n p ≤ trialFactor n (1 / ((n : ℝ) + 1)) := by
  have ha := optimal_probability_pos n
  have ha1 := optimal_probability_lt_one hn
  have h := normalized_log_bound hn hp hp1
  rw [Real.log_div hp.ne' ha.ne',
    Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr ha1).ne'] at h
  apply (Real.log_le_log_iff (trialFactor_pos n hp hp1) (trialFactor_pos n ha ha1)).1
  rw [log_trialFactor n hp hp1, log_trialFactor n ha ha1]
  linarith

theorem trialFactor_eq_optimal_iff {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    trialFactor n p = trialFactor n (1 / ((n : ℝ) + 1)) ↔
      p = 1 / ((n : ℝ) + 1) := by
  constructor
  · intro he
    by_contra hnq
    have ha := optimal_probability_pos n
    have ha1 := optimal_probability_lt_one hn
    have h := normalized_log_strict hn hp hp1 hnq
    rw [Real.log_div hp.ne' ha.ne',
      Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr ha1).ne'] at h
    have he' := congrArg Real.log he
    rw [log_trialFactor n hp hp1, log_trialFactor n ha ha1] at he'
    linarith
  · rintro rfl
    rfl

variable {E I : Type*} [Fintype E] [Fintype I] [DecidableEq I]

/-- Probability that precisely the sources bearing label `i` emit. -/
noncomputable def branchProbability (label : E → I) (p : E → ℝ) (i : I) : ℝ :=
  ∏ e, if label e = i then p e else 1 - p e

theorem label_factor_product (i : I) (a b : ℝ) :
    (∏ j : I, if i = j then a else b) = a * b ^ (Fintype.card I - 1) := by
  classical
  rw [← Finset.mul_prod_erase (Finset.univ : Finset I)
    (fun j => if i = j then a else b) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  have h : (∏ j ∈ Finset.univ.erase i, if i = j then a else b) =
      ∏ _j ∈ Finset.univ.erase i, b := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    simp [hne]
  rw [h]
  simp

/-- Each source occurs in one emitting factor and in `d-1` vacuum factors. -/
theorem product_branchProbabilities (label : E → I) (p : E → ℝ) :
    (∏ i, branchProbability label p i) =
      ∏ e, trialFactor (Fintype.card I - 1) (p e) := by
  unfold branchProbability trialFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro e he
  exact label_factor_product (label e) (p e) (1 - p e)

theorem branchProbability_pos (label : E → I) (p : E → ℝ)
    (hp : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1) (i : I) :
    0 < branchProbability label p i := by
  apply Finset.prod_pos
  intro e he
  split_ifs
  · exact hp e
  · exact sub_pos.mpr (hp1 e)

/-- The common branch probability is bounded by the homogeneous optimum;
equality holds if and only if every source has probability `1/d`.
This is the optimization in Proposition 5.1 with `d = n+1` and `dm` sources. -/
theorem equal_branch_optimum {n m : ℕ} (hn : 0 < n)
    (hI : Fintype.card I = n + 1) (hE : Fintype.card E = m * (n + 1))
    (label : E → I) (p : E → ℝ)
    (hp : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (Q : ℝ) (hequal : ∀ i, branchProbability label p i = Q) :
    Q ≤ (trialFactor n (1 / ((n : ℝ) + 1))) ^ m ∧
    (Q = (trialFactor n (1 / ((n : ℝ) + 1))) ^ m ↔
      ∀ e, p e = 1 / ((n : ℝ) + 1)) := by
  classical
  let a : ℝ := 1 / ((n : ℝ) + 1)
  let B : ℝ := trialFactor n a
  have ha : 0 < a := optimal_probability_pos n
  have ha1 : a < 1 := optimal_probability_lt_one hn
  have hB : 0 < B := trialFactor_pos n ha ha1
  have hfpos : ∀ e, 0 < trialFactor n (p e) := fun e => trialFactor_pos n (hp e) (hp1 e)
  have hfle : ∀ e, trialFactor n (p e) ≤ B := fun e => trialFactor_le_optimal hn (hp e) (hp1 e)
  have hIpos : 0 < Fintype.card I := by rw [hI]; exact Nat.succ_pos n
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hIpos
  have hQ : 0 < Q := by
    rw [← hequal i]
    exact branchProbability_pos label p hp hp1 i
  have hprod : Q ^ (n + 1) = ∏ e, trialFactor n (p e) := by
    have he := product_branchProbabilities label p
    simpa only [hequal, Finset.prod_const, Finset.card_univ, hI, Nat.add_sub_cancel] using he
  have hpow : B ^ (Fintype.card E) = (B ^ m) ^ (n + 1) := by
    rw [hE, pow_mul]
  have hupper : Q ^ (n + 1) ≤ (B ^ m) ^ (n + 1) := by
    rw [hprod, ← hpow]
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := (Finset.univ : Finset E))
        (fun e _ => (hfpos e).le) (fun e _ => hfle e))
  have hbound : Q ≤ B ^ m :=
    (pow_le_pow_iff_left₀ hQ.le (pow_pos hB m).le (Nat.succ_ne_zero n)).1 hupper
  refine ⟨hbound, ?_⟩
  constructor
  · intro he e
    apply (trialFactor_eq_optimal_iff hn (hp e) (hp1 e)).1
    by_contra hne
    have hlt : trialFactor n (p e) < B := lt_of_le_of_ne (hfle e) hne
    have hstrict := Finset.prod_lt_prod₀
      (s := (Finset.univ : Finset E)) (fun x _ => hfpos x)
      (fun x _ => hfle x) ⟨e, Finset.mem_univ e, hlt⟩
    simp only [Finset.prod_const, Finset.card_univ] at hstrict
    rw [← hprod, hpow] at hstrict
    exact (ne_of_lt hstrict) (congrArg (fun x : ℝ => x ^ (n + 1)) he)
  · intro he
    have heprod : Q ^ (n + 1) = (B ^ m) ^ (n + 1) := by
      rw [hprod]
      simp only [he]
      simpa only [Finset.prod_const, Finset.card_univ] using hpow
    apply le_antisymm hbound
    exact (pow_le_pow_iff_left₀ (pow_pos hB m).le hQ.le (Nat.succ_ne_zero n)).1 heprod.ge

/-- Summing the equal probabilities gives the exact optimal success bound. -/
theorem equal_weight_success_bound {n m : ℕ} (hn : 0 < n)
    (hI : Fintype.card I = n + 1) (hE : Fintype.card E = m * (n + 1))
    (label : E → I) (p : E → ℝ)
    (hp : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (Q : ℝ) (hequal : ∀ i, branchProbability label p i = Q) :
    (∑ i, branchProbability label p i) ≤
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) := by
  have hb := (equal_branch_optimum hn hI hE label p hp hp1 Q hequal).1
  have h := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  simpa [hequal, hI, trialFactor, mul_pow, pow_mul, Nat.mul_comm, mul_assoc] using h

theorem homogeneous_branch_probability {n m : ℕ}
    (hE : Fintype.card E = m * (n + 1)) (label : E → I)
    (hfib : ∀ i, (Finset.univ.filter (fun e => label e = i)).card = m)
    (a : ℝ) (i : I) :
    branchProbability label (fun _ => a) i = (trialFactor n a) ^ m := by
  classical
  have hnot : (Finset.univ.filter (fun e => ¬ label e = i)).card = m * n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E))
      (p := fun e => label e = i)
    rw [hfib i, Finset.card_univ, hE, Nat.mul_add, Nat.mul_one] at h
    omega
  unfold branchProbability
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hfib i, hnot]
  simp [trialFactor, mul_pow, pow_mul, Nat.mul_comm]

/-- Equality in the total success-probability bound forces the unique optimal
choice at every source. -/
theorem equal_weight_success_eq_iff {n m : ℕ} (hn : 0 < n)
    (hI : Fintype.card I = n + 1) (hE : Fintype.card E = m * (n + 1))
    (label : E → I) (p : E → ℝ)
    (hp : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (Q : ℝ) (hequal : ∀ i, branchProbability label p i = Q) :
    ((∑ i, branchProbability label p i) =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n)) ↔
      ∀ e, p e = 1 / ((n : ℝ) + 1) := by
  have he := (equal_branch_optimum hn hI hE label p hp hp1 Q hequal).2
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hform : ((n : ℝ) + 1) * (trialFactor n (1 / ((n : ℝ) + 1))) ^ m =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) := by
    simp [trialFactor, mul_pow, pow_mul, Nat.mul_comm, mul_assoc]
  rw [← hform]
  simp only [hequal, Finset.sum_const, Finset.card_univ, hI,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · intro h
    exact he.1 (mul_left_cancel₀ hne h)
  · intro h
    rw [he.2 h]

/-- The optimum is attained by the homogeneous pump whenever every matching
class has `m` sources. -/
theorem homogeneous_success_probability {n m : ℕ}
    (hI : Fintype.card I = n + 1) (hE : Fintype.card E = m * (n + 1))
    (label : E → I)
    (hfib : ∀ i, (Finset.univ.filter (fun e => label e = i)).card = m) :
    (∑ i, branchProbability label (fun _ => 1 / ((n : ℝ) + 1)) i) =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) := by
  simp only [homogeneous_branch_probability hE label hfib,
    Finset.sum_const, Finset.card_univ, hI, nsmul_eq_mul]
  simp [trialFactor, mul_pow, pow_mul, Nat.mul_comm, mul_assoc]

end RigidGHZ.SourceModel
