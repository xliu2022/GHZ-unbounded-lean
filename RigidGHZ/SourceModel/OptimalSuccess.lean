module

public import RigidGHZ.SourceModel.ProbabilityBridge

/-!
# The optimal probability for the actual postselected state

This file states Proposition 5.1 for the squared Hilbert norm of the explicitly
expanded binary-source state, with its unique equality condition and homogeneous
attainment. Equal branch magnitudes are the equal-weight GHZ constraint.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype V] [Fintype I] {H : Hypergraph V}

/-- Probability of the one-photon-per-path accepted event. -/
def successProbability (F : MatchingDecomposition H I) (p φ : Finset V → ℝ) : ℝ :=
  stateNormSq (postselectedState F p φ)

theorem acceptedState_normSq (F : MatchingDecomposition H I)
    (hnonempty : ∀ e ∈ H, e.Nonempty) (b : PerfectMatchings H → ℂ) :
    stateNormSq (F.acceptedState b) = ∑ M, Complex.normSq (b M) := by
  classical
  exact finitePushforward_normSq F.labelString b (F.labelString_injective hnonempty)

theorem successProbability_eq_branches [Nonempty V] [DecidableEq I]
    (G : RigidFamily H I) (hnonempty : ∀ e ∈ H, e.Nonempty)
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) :
    successProbability (MatchingDecomposition.ofRigidFamily G) p φ =
      ∑ i, branchProbability (MatchingDecomposition.ofRigidFamily G).edgeColor
        (fun e : H => p e.1) i := by
  let F := MatchingDecomposition.ofRigidFamily G
  unfold successProbability
  rw [postselectedState_eq_matchingState, acceptedState_normSq _ hnonempty]
  calc
    (∑ M, Complex.normSq (binaryMatchingAmplitude p φ M)) =
        ∑ i, Complex.normSq (binaryMatchingAmplitude p φ (F.prescribed i)) :=
      ((rigidMatchingEquiv G).sum_comp
        (fun M => Complex.normSq (binaryMatchingAmplitude p φ M))).symm
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      F.prescribed_normSq_eq_branchProbability p φ hp i)

/--
Proposition 5.1: the success probability of an equal-weight accepted GHZ state
is at most `d^(1-m) (1-1/d)^((d-1)m)`, and equality holds exactly when every
source has emission probability `1/d`. Here `d = n+1 ≥ 2`.
-/
theorem optimal_binary_success_probability [Nonempty V] {r m n : ℕ}
    (G : RigidFamily H (Fin (n + 1))) (hH : Uniform H r)
    (hr : 0 < r) (hn : 0 < n) (hV : Fintype.card V = r * m)
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 < p e ∧ p e < 1)
    (Q : ℝ) (hequal : ∀ i,
      Complex.normSq (binaryMatchingAmplitude p φ
        ((MatchingDecomposition.ofRigidFamily G).prescribed i)) = Q) :
    successProbability (MatchingDecomposition.ofRigidFamily G) p φ ≤
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) ∧
    (successProbability (MatchingDecomposition.ofRigidFamily G) p φ =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) ↔
      ∀ e ∈ H, p e = 1 / ((n : ℝ) + 1)) := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  have hpclosed : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1 :=
    fun e he => ⟨(hp e he).1.le, (hp e he).2.le⟩
  have hI : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
  have hE : Fintype.card H = m * (n + 1) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, Nat.mul_comm] using
      G.card_edges hH hr hV
  have hequal' : ∀ i, branchProbability F.edgeColor (fun e : H => p e.1) i = Q := by
    intro i
    rw [← F.prescribed_normSq_eq_branchProbability p φ hpclosed i]
    exact hequal i
  rw [successProbability_eq_branches G (nonempty_edges_of_uniform hH hr) p φ hpclosed]
  constructor
  · exact equal_weight_success_bound hn hI hE F.edgeColor (fun e : H => p e.1)
      (fun e => (hp e.1 e.2).1) (fun e => (hp e.1 e.2).2) Q hequal'
  · rw [equal_weight_success_eq_iff hn hI hE F.edgeColor (fun e : H => p e.1)
      (fun e => (hp e.1 e.2).1) (fun e => (hp e.1 e.2).2) Q hequal']
    exact ⟨fun h e he => h ⟨e, he⟩, fun h e => h e.1 e.2⟩

/-- The optimal pump values attain the probability bound for arbitrary source phases. -/
theorem optimal_binary_success_attained [Nonempty V] {r m n : ℕ}
    (G : RigidFamily H (Fin (n + 1))) (hH : Uniform H r)
    (hr : 0 < r) (hn : 0 < n) (hV : Fintype.card V = r * m)
    (φ : Finset V → ℝ) :
    successProbability (MatchingDecomposition.ofRigidFamily G)
      (fun _ => 1 / ((n : ℝ) + 1)) φ =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  have hp : ∀ _e ∈ H, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ∧
      1 / ((n : ℝ) + 1) ≤ 1 :=
    fun _ _ => ⟨(optimal_probability_pos n).le, (optimal_probability_lt_one hn).le⟩
  rw [successProbability_eq_branches G (nonempty_edges_of_uniform hH hr) _ φ hp]
  have hE : Fintype.card H = m * (n + 1) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, Nat.mul_comm] using
      G.card_edges hH hr hV
  apply homogeneous_success_probability (Fintype.card_fin _) hE F.edgeColor
  intro i
  rw [F.edgeColor_fiber_card]
  exact perfectMatching_card hH hr hV (F.prescribed i)

end RigidGHZ.SourceModel
