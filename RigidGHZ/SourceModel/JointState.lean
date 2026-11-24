module

public import RigidGHZ.SourceModel.OptimalSuccess
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Normalization of the independent binary-source state before postselection,
and the exact success probability for identical in-phase sources. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V : Type*} [DecidableEq V] {H : Hypergraph V}

def emissionPatternEquiv (H : Hypergraph V) : EmissionPattern H ≃ ↥H.powerset where
  toFun S := ⟨S.val, Finset.mem_powerset.mpr S.property⟩
  invFun S := ⟨S.val, Finset.mem_powerset.mp S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance emissionPatternFintype (H : Hypergraph V) : Fintype (EmissionPattern H) :=
  Fintype.ofEquiv ↥H.powerset (emissionPatternEquiv H).symm

theorem patternAmplitude_normSq (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) (S : EmissionPattern H) :
    Complex.normSq (patternAmplitude p φ S) =
      (∏ e ∈ S.val, p e) * ∏ e ∈ H \ S.val, (1 - p e) := by
  unfold patternAmplitude
  rw [Complex.normSq_mul, map_prod, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact emissionAmplitude_normSq (hp e (S.property he)).1 (φ e)
  · apply Finset.prod_congr rfl
    intro e he
    exact vacuumAmplitude_normSq (hp e (Finset.mem_sdiff.mp he).1).2

/-- The tensor product's coefficient expansion has squared norm one. -/
theorem joint_binary_state_normalized (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) :
    stateNormSq (patternAmplitude p φ : EmissionPattern H → ℂ) = 1 := by
  classical
  let f : Hypergraph V → ℝ := fun S => (∏ e ∈ S, p e) * ∏ e ∈ H \ S, (1 - p e)
  calc
    stateNormSq (patternAmplitude p φ : EmissionPattern H → ℂ) = ∑ S : EmissionPattern H, f S.val := by
      exact Finset.sum_congr rfl (fun S _ => patternAmplitude_normSq p φ hp S)
    _ = ∑ S : ↥H.powerset, f S.val := (emissionPatternEquiv H).sum_comp (fun S => f S.val)
    _ = ∑ S ∈ H.powerset, f S := Finset.sum_coe_sort H.powerset f
    _ = ∏ e ∈ H, (p e + (1 - p e)) := (Finset.prod_add p (fun e => 1 - p e) H).symm
    _ = 1 := by simp

theorem commonAmplitude_sq {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N m : ℕ) :
    commonAmplitude p N m ^ 2 = p ^ m * (1 - p) ^ (N - m) := by
  unfold commonAmplitude
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m 2, Nat.mul_comm (N - m) 2,
    pow_mul, pow_mul, Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr hp1)]

/-- Identical sources have the explicit accepted probability stated in Section 5. -/
theorem uniform_binary_success [Fintype V] [Nonempty V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hH : Uniform H r)
    (hr : 0 < r) (hV : Fintype.card V = r * m)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    successProbability (MatchingDecomposition.ofRigidFamily G) (fun _ => p) (fun _ => 0) =
      (d : ℝ) * p ^ m * (1 - p) ^ (m * (d - 1)) := by
  unfold successProbability
  rw [postselectedState_eq_matchingState]
  rw [acceptedState_normSq_common G (nonempty_edges_of_uniform hH hr)
    (binaryMatchingAmplitude (fun _ => p) (fun _ => 0)) (commonAmplitude p H.card m)
    (binaryMatchingAmplitude_common hH hr hV p)]
  have hcard : H.card = d * m := by simpa using G.card_edges hH hr hV
  rw [Fintype.card_fin, ← pow_two, commonAmplitude_sq hp hp1, hcard]
  have he : d * m - m = m * (d - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm m d]
  rw [he]
  ring

theorem uniform_binary_success_pos [Fintype V] [Nonempty V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hH : Uniform H r)
    (hr : 0 < r) (hd : 0 < d) (hV : Fintype.card V = r * m)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < successProbability (MatchingDecomposition.ofRigidFamily G) (fun _ => p) (fun _ => 0) := by
  rw [uniform_binary_success G hH hr hV p hp.le hp1.le]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hd) (pow_pos hp _))
    (pow_pos (sub_pos.mpr hp1) _)

end RigidGHZ.SourceModel
