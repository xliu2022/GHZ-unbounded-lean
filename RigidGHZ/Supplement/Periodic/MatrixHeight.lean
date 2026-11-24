module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

/-! Exact trace formulas for the two height-certificate patterns in Supplement S2. -/

@[expose] public section

set_option maxHeartbeats 1000000

namespace RigidGHZ.Supplement.Periodic.MatrixHeight

variable {S : Type*} [Fintype S] [DecidableEq S]

 theorem power_eq_on_height (A B : Matrix S S ℕ) (height : S → ℕ)
    (hA : A.BlockTriangular height) (hB : B.BlockTriangular height)
    (heq : ∀ s t, height s = height t → A s t = B s t)
    (n : ℕ) {s t : S} (hst : height s = height t) :
    (A ^ n) s t = (B ^ n) s t := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u hu
    rcases lt_trichotomy (height u) (height s) with h | h | h
    · rw [hA h, hB h, zero_mul, zero_mul]
    · rw [heq s u h.symm, ih (h.trans hst)]
    · have htu : height t < height u := by omega
      rw [(hA.pow n) htu, (hB.pow n) htu, mul_zero, mul_zero]

 theorem trace_eq_on_height (A B : Matrix S S ℕ) (height : S → ℕ)
    (hA : A.BlockTriangular height) (hB : B.BlockTriangular height)
    (heq : ∀ s t, height s = height t → A s t = B s t) (n : ℕ) :
    Matrix.trace (A ^ n) = Matrix.trace (B ^ n) := by
  apply Finset.sum_congr rfl
  intro s hs
  exact power_eq_on_height A B height hA hB heq n rfl

 theorem zero_one_pow {a q : ℕ} (ha : a ≤ 1) (hq : 0 < q) : a ^ q = a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
  · simp [h, Nat.ne_of_gt hq]
  · simp [h]

/-- Strictly height-increasing nonloops cannot contribute to a trace. -/
theorem strict_trace (A : Matrix S S ℕ) (height : S → ℕ)
    (hmono : A.BlockTriangular height)
    (hflat : ∀ s t, height s = height t → s ≠ t → A s t = 0)
    (hdiag : ∀ s, A s s ≤ 1) {q : ℕ} (hq : 0 < q) :
    Matrix.trace (A ^ q) = Matrix.trace A := by
  let B := Matrix.diagonal (fun s => A s s)
  have heq : ∀ s t, height s = height t → A s t = B s t := by
    intro s t hst
    by_cases h : s = t
    · subst t; simp [B]
    · simp [B, Matrix.diagonal_apply_ne _ h, hflat s t hst h]
  rw [trace_eq_on_height A B height hmono (Matrix.blockTriangular_diagonal _) heq q]
  simp only [B, Matrix.diagonal_pow, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro s hs
  exact zero_one_pow (hdiag s) hq

 def pairBlock (diag : S → ℕ) (x y : S) (a b : ℕ) : Matrix S S ℕ := fun s t =>
  if s = x then (if t = y then a else 0) else
  if s = y then (if t = x then b else 0) else
  if s = t then diag s else 0

 theorem power_step_of_row (B : Matrix S S ℕ) (s t : S) (a : ℕ)
    (hrow : ∀ u, B s u = if u = t then a else 0) (n : ℕ) (j : S) :
    (B ^ (n + 1)) s j = a * (B ^ n) t j := by
  rw [pow_succ', Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul]
  simp

 theorem alternating_power (B : Matrix S S ℕ) (x y : S) (hxy : x ≠ y) (a b : ℕ)
    (hx : ∀ u, B x u = if u = y then a else 0)
    (hy : ∀ u, B y u = if u = x then b else 0) :
    ∀ k, (B ^ (2 * k)) x x = (a * b) ^ k ∧ (B ^ (2 * k + 1)) x x = 0 := by
  have hstep : ∀ n, (B ^ (n + 2)) x x = (a * b) * (B ^ n) x x := by
    intro n
    rw [show n + 2 = (n + 1) + 1 by omega,
      power_step_of_row B x y a hx, power_step_of_row B y x b hy]
    exact (mul_assoc _ _ _).symm
  intro k
  induction k with
  | zero =>
    constructor
    · simp
    · simpa [hxy, Ne.symm hxy] using power_step_of_row B x y a hx 0 x
  | succ k ih =>
    constructor
    · rw [show 2 * (k + 1) = 2 * k + 2 by omega, hstep, ih.1, pow_succ]
      exact Nat.mul_comm _ _
    · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, hstep, ih.2, mul_zero]

 theorem pairBlock_outside_power (diag : S → ℕ) (x y : S) (a b : ℕ)
    {s : S} (hsx : s ≠ x) (hsy : s ≠ y) (q : ℕ) :
    (pairBlock diag x y a b ^ q) s s = diag s ^ q := by
  have hrow : ∀ u, pairBlock diag x y a b s u = if u = s then diag s else 0 := by
    intro u
    simp only [pairBlock, if_neg hsx, if_neg hsy]
    simp only [eq_comm]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [power_step_of_row _ s s (diag s) hrow, ih, pow_succ]
    exact Nat.mul_comm _ _

 theorem pairBlock_trace_odd (diag : S → ℕ) (x y : S) (hxy : x ≠ y) (a b : ℕ)
    (hx0 : diag x = 0) (hy0 : diag y = 0) (hdiag : ∀ s, diag s ≤ 1) (k : ℕ) :
    Matrix.trace (pairBlock diag x y a b ^ (2 * k + 1)) = ∑ s, diag s := by
  let B := pairBlock diag x y a b
  have hx : ∀ u, B x u = if u = y then a else 0 := by intro u; simp [B, pairBlock]
  have hy : ∀ u, B y u = if u = x then b else 0 := by intro u; simp [B, pairBlock, Ne.symm hxy]
  have hxx := (alternating_power B x y hxy a b hx hy k).2
  have hyy := (alternating_power B y x (Ne.symm hxy) b a hy hx k).2
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsx : s = x
  · subst s; exact hxx.trans hx0.symm
  by_cases hsy : s = y
  · subst s; exact hyy.trans hy0.symm
  exact (pairBlock_outside_power diag x y a b hsx hsy _).trans (zero_one_pow (hdiag s) (by omega))

 theorem pairBlock_trace_even (diag : S → ℕ) (x y : S) (hxy : x ≠ y) (a b : ℕ)
    (hx0 : diag x = 0) (hy0 : diag y = 0) (hdiag : ∀ s, diag s ≤ 1)
    (k : ℕ) (hk : 0 < k) :
    Matrix.trace (pairBlock diag x y a b ^ (2 * k)) = (∑ s, diag s) + 2 * (a * b) ^ k := by
  let B := pairBlock diag x y a b
  have hx : ∀ u, B x u = if u = y then a else 0 := by intro u; simp [B, pairBlock]
  have hy : ∀ u, B y u = if u = x then b else 0 := by intro u; simp [B, pairBlock, Ne.symm hxy]
  have hxx := (alternating_power B x y hxy a b hx hy k).1
  have hyy : (B ^ (2 * k)) y y = (a * b) ^ k := by
    simpa only [Nat.mul_comm b a] using (alternating_power B y x (Ne.symm hxy) b a hy hx k).1
  have hd : ∀ s, (B ^ (2 * k)) s s = diag s +
      (if s = x then (a * b) ^ k else 0) + (if s = y then (a * b) ^ k else 0) := by
    intro s
    by_cases hsx : s = x
    · subst s; simp [hxx, hx0, hxy]
    by_cases hsy : s = y
    · subst s; simp [hyy, hy0, Ne.symm hxy]
    rw [if_neg hsx, if_neg hsy, add_zero, add_zero]
    exact (pairBlock_outside_power diag x y a b hsx hsy _).trans
      (zero_one_pow (hdiag s) (by omega))
  change (∑ s, (B ^ (2 * k)) s s) = _
  simp_rw [hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  omega

/-- The exceptional equal-height two-cycle contributes exactly its weighted
alternating walks at even periods. -/
theorem exceptional_trace (A : Matrix S S ℕ) (height : S → ℕ)
    (x y : S) (hxy : x ≠ y) (hheight : height x = height y)
    (hmono : A.BlockTriangular height)
    (hflat : ∀ s t, height s = height t → s ≠ t →
      ¬(s = x ∧ t = y) → ¬(s = y ∧ t = x) → A s t = 0)
    (hx0 : A x x = 0) (hy0 : A y y = 0) (hdiag : ∀ s, A s s ≤ 1)
    {q : ℕ} (hq : 0 < q) :
    Matrix.trace (A ^ q) = Matrix.trace A +
      if Even q then 2 * (A x y * A y x) ^ (q / 2) else 0 := by
  classical
  let B := pairBlock (fun s => A s s) x y (A x y) (A y x)
  have hB : B.BlockTriangular height := by
    intro s t hst
    have hsnt : s ≠ t := by intro h; subst t; omega
    have hxyt : ¬(s = x ∧ t = y) := by rintro ⟨rfl, rfl⟩; omega
    have hyxt : ¬(s = y ∧ t = x) := by rintro ⟨rfl, rfl⟩; omega
    simp only [B, pairBlock]
    split_ifs with hsx hty hsy htx
    all_goals first | rfl | exact (hxyt ⟨hsx, hty⟩).elim |
      exact (hyxt ⟨hsy, htx⟩).elim | exact (hsnt ‹s = t›).elim
  have heq : ∀ s t, height s = height t → A s t = B s t := by
    intro s t hst
    by_cases hsx : s = x
    · subst s
      by_cases hty : t = y
      · subst t; simp [B, pairBlock]
      by_cases htx : t = x
      · subst t; simp [B, pairBlock, hxy, hx0]
      have hz := hflat x t hst (Ne.symm htx) (by tauto) (by tauto)
      simp [B, pairBlock, hty, hz]
    by_cases hsy : s = y
    · subst s
      by_cases htx : t = x
      · subst t; simp [B, pairBlock, Ne.symm hxy]
      by_cases hty : t = y
      · subst t; simp [B, pairBlock, Ne.symm hxy, hy0]
      have hz := hflat y t hst (Ne.symm hty) (by tauto) (by tauto)
      simp [B, pairBlock, Ne.symm hxy, htx, hz]
    by_cases hst' : s = t
    · subst t; simp [B, pairBlock, hsx, hsy]
    have hz := hflat s t hst hst' (by tauto) (by tauto)
    simp [B, pairBlock, hsx, hsy, hst', hz]
  rw [trace_eq_on_height A B height hmono hB heq q]
  by_cases heven : Even q
  · have hex := heven
    obtain ⟨k, hk⟩ := hex
    have hqk : q = 2 * k := by omega
    have hk0 : 0 < k := by omega
    rw [if_pos heven, hqk, Nat.mul_div_right _ (by decide : 0 < 2)]
    exact pairBlock_trace_even (fun s => A s s) x y hxy (A x y) (A y x) hx0 hy0 hdiag k hk0
  · have hodd : Odd q := Nat.not_even_iff_odd.mp heven
    obtain ⟨k, hk⟩ := hodd
    have hqk : q = 2 * k + 1 := by omega
    rw [if_neg heven, add_zero, hqk]
    exact pairBlock_trace_odd (fun s => A s s) x y hxy (A x y) (A y x) hx0 hy0 hdiag k

end RigidGHZ.Supplement.Periodic.MatrixHeight
