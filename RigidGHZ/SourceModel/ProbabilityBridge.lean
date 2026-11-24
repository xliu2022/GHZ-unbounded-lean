module

public import RigidGHZ.SourceModel.PhaseCorrection
public import RigidGHZ.SourceModel.Probability
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Source coefficients and the optimal success probability

The squared moduli of the binary-source amplitudes are exactly the independent
source probabilities. This connects the optimization to the actual finite
coefficient vector of the accepted optical state.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

theorem emissionAmplitude_normSq {p : ℝ} (hp : 0 ≤ p) (φ : ℝ) :
    Complex.normSq (emissionAmplitude p φ) = p := by
  rw [emissionAmplitude, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt hp, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

theorem vacuumAmplitude_normSq {p : ℝ} (hp : p ≤ 1) :
    Complex.normSq (vacuumAmplitude p) = 1 - p := by
  rw [vacuumAmplitude, Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr hp)]

theorem binaryMatchingAmplitude_normSq (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) (M : PerfectMatchings H) :
    Complex.normSq (binaryMatchingAmplitude p φ M) =
      (∏ e ∈ M.1, p e) * ∏ e ∈ H \ M.1, (1 - p e) := by
  unfold binaryMatchingAmplitude
  rw [Complex.normSq_mul, map_prod, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact emissionAmplitude_normSq (hp e (M.2.subset he)).1 (φ e)
  · apply Finset.prod_congr rfl
    intro e he
    exact vacuumAmplitude_normSq (hp e (Finset.mem_sdiff.mp he).1).2

namespace MatchingDecomposition

variable (F : MatchingDecomposition H I)

theorem edgeColor_eq_iff (e : H) (i : I) :
    F.edgeColor e = i ↔ e.1 ∈ F.matching i := by
  constructor
  · intro hi
    simpa only [hi] using F.edgeColor_mem e
  · exact F.edgeColor_eq_of_mem e

theorem edgeColor_fiber_card [DecidableEq I] (i : I) :
    (Finset.univ.filter (fun e : H => F.edgeColor e = i)).card = (F.matching i).card := by
  classical
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    exact (F.edgeColor_eq_iff e i).mp (Finset.mem_filter.mp he).2
  · intro e he f hf h
    exact Subtype.ext h
  · intro e he
    refine ⟨⟨e, (F.perfect i).subset he⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (F.edgeColor_eq_iff _ i).mpr he⟩

theorem prescribed_normSq_eq_branchProbability [DecidableEq I]
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) (i : I) :
    Complex.normSq (binaryMatchingAmplitude p φ (F.prescribed i)) =
      branchProbability F.edgeColor (fun e : H => p e.1) i := by
  classical
  rw [binaryMatchingAmplitude_normSq p φ hp]
  unfold branchProbability
  have hprod : (∏ e : H, if F.edgeColor e = i then p e.1 else 1 - p e.1) =
      ∏ e ∈ H, if e ∈ F.matching i then p e else 1 - p e := by
    simp_rw [F.edgeColor_eq_iff]
    exact Finset.prod_coe_sort H (fun e : Finset V =>
      if e ∈ F.matching i then p e else 1 - p e)
  rw [hprod, Finset.prod_ite]
  have hmem : H.filter (fun e => e ∈ F.matching i) = F.matching i := by
    ext e
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun he => (F.perfect i).subset he)
  have hnot : H.filter (fun e => ¬ e ∈ F.matching i) = H \ F.matching i := by
    ext e
    simp
  rw [hmem, hnot]
  rfl

end MatchingDecomposition

end RigidGHZ.SourceModel
