module

public import RigidGHZ.SourceModel.Postselection

/-!
# A phase correction on one output path

A diagonal phase map of squared modulus one on the labels of one fixed path
is linear, has its conjugate as inverse, and preserves the Hilbert norm.
Equal-modulus accepted branches can therefore be turned into the GHZ vector
by such a single-path diagonal unitary.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*}

/-- The action of a diagonal phase transformation on one path in the local label basis. -/
def localPhaseCorrection (phase : I → ℂ) (v : V) (ψ : (V → I) → ℂ) (s : V → I) : ℂ :=
  phase (s v) * ψ s

theorem localPhaseCorrection_add (phase : I → ℂ) (v : V)
    (ψ χ : (V → I) → ℂ) :
    localPhaseCorrection phase v (ψ + χ) =
      localPhaseCorrection phase v ψ + localPhaseCorrection phase v χ := by
  funext s
  exact mul_add _ _ _

theorem localPhaseCorrection_smul (phase : I → ℂ) (v : V)
    (ψ : (V → I) → ℂ) (z : ℂ) :
    localPhaseCorrection phase v (z • ψ) = z • localPhaseCorrection phase v ψ := by
  funext s
  change phase (s v) * (z * ψ s) = z * (phase (s v) * ψ s)
  ring

theorem localPhaseCorrection_inverse (phase : I → ℂ)
    (hphase : ∀ i, Complex.normSq (phase i) = 1)
    (v : V) (ψ : (V → I) → ℂ) :
    localPhaseCorrection (fun i => starRingEnd ℂ (phase i)) v
      (localPhaseCorrection phase v ψ) = ψ := by
  funext s
  change starRingEnd ℂ (phase (s v)) * (phase (s v) * ψ s) = ψ s
  rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self, hphase]
  simp

theorem localPhaseCorrection_normSq [DecidableEq V] [Fintype V] [Fintype I]
    (phase : I → ℂ) (hphase : ∀ i, Complex.normSq (phase i) = 1)
    (v : V) (ψ : (V → I) → ℂ) :
    stateNormSq (localPhaseCorrection phase v ψ) = stateNormSq ψ := by
  unfold stateNormSq
  apply Finset.sum_congr rfl
  intro s _
  simp [localPhaseCorrection, Complex.normSq_mul, hphase]

theorem localPhaseCorrection_normalized [DecidableEq V] [Fintype V] [Fintype I]
    (phase : I → ℂ) (hphase : ∀ i, Complex.normSq (phase i) = 1)
    (v : V) (ψ : (V → I) → ℂ) :
    localPhaseCorrection phase v (normalizedState ψ) =
      normalizedState (localPhaseCorrection phase v ψ) := by
  funext s
  change phase (s v) * (ψ s / (Real.sqrt (stateNormSq ψ) : ℂ)) =
    (phase (s v) * ψ s) /
      (Real.sqrt (stateNormSq (localPhaseCorrection phase v ψ)) : ℂ)
  rw [localPhaseCorrection_normSq phase hphase v ψ]
  exact (mul_div_assoc _ _ _).symm

variable [DecidableEq V] [Fintype I] {H : Hypergraph V}

theorem localPhaseCorrection_acceptedState
    (F : MatchingDecomposition H I) (phase : I → ℂ) (v : V)
    (b : PerfectMatchings H → ℂ) :
    localPhaseCorrection phase v (F.acceptedState b) =
      F.acceptedState (fun M => phase (F.labelString M v) * b M) := by
  classical
  funext s
  unfold localPhaseCorrection MatchingDecomposition.acceptedState finitePushforward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : F.labelString M = s
  · simp [h]
  · simp [h]

/--
The equal-modulus clause of Proposition 2.1: a single-path diagonal unitary
turns the normalized accepted state into the standard GHZ state.
-/
theorem equal_magnitude_phase_correction [Fintype V] [Nonempty V] {d : ℕ}
    (G : RigidFamily H (Fin d)) (hd : 0 < d)
    (hnonempty : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (q : ℝ) (hq : 0 < q)
    (hmod : ∀ M, Complex.normSq (b M) = q * q) (v : V) :
    ∃ phase : Fin d → ℂ,
      (∀ i, Complex.normSq (phase i) = 1) ∧
      localPhaseCorrection phase v
        (normalizedState ((MatchingDecomposition.ofRigidFamily G).acceptedState b)) =
          ghzState V d := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  have hb : ∀ M, b M ≠ 0 := by
    intro M
    apply Complex.normSq_pos.mp
    rw [hmod]
    exact mul_pos hq hq
  let phase : Fin d → ℂ := fun i => (q : ℂ) / b (F.prescribed i)
  have hphase : ∀ i, Complex.normSq (phase i) = 1 := by
    intro i
    dsimp [phase]
    rw [Complex.normSq_div, Complex.normSq_ofReal, hmod]
    exact div_self (ne_of_gt (mul_pos hq hq))
  have hcorrected : ∀ M, phase (F.labelString M v) * b M = (q : ℂ) := by
    intro M
    obtain ⟨i, hi⟩ := G.complete M.1 M.2
    have heq : M = F.prescribed i := Subtype.ext hi
    rw [heq, F.labelString_prescribed]
    exact div_mul_cancel₀ (q : ℂ) (hb (F.prescribed i))
  refine ⟨phase, hphase, ?_⟩
  rw [localPhaseCorrection_normalized phase hphase,
    localPhaseCorrection_acceptedState]
  exact normalized_common_eq_ghz G hd hnonempty
    (fun M => phase (F.labelString M v) * b M) q hq hcorrected

end RigidGHZ.SourceModel
