module

public import RigidGHZ.SourceModel.Normalization

/-!
# One-photon-per-path selection

A binary emission pattern is a subset of the source edges. Its photon count
at a vertex is the number of its incident emitting edges. We prove that the
accepted patterns, defined by photon counts equal to one, are exactly the
ordinary perfect matchings. Summing their independent-source amplitudes is
then the already verified matching-state formula.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- Every source either emits or remains in vacuum. -/
def EmissionPattern (H : Hypergraph V) := {S : Hypergraph V // S ⊆ H}

/-- Number of photons entering a path in the binary-source model. -/
def photonCount (S : EmissionPattern H) (v : V) : ℕ :=
  (S.1.filter (fun e => v ∈ e)).card

/-- Exact photon-number postselection: one photon in every output path. -/
def AcceptedPattern (S : EmissionPattern H) : Prop := ∀ v, photonCount S v = 1

def AcceptedPatterns (H : Hypergraph V) := {S : EmissionPattern H // AcceptedPattern S}

/-- Accepted emission patterns are exactly perfect matchings, with no physical approximation. -/
def acceptedPatternEquiv (H : Hypergraph V) : AcceptedPatterns H ≃ PerfectMatchings H where
  toFun S := ⟨S.1.1, S.1.2, S.2⟩
  invFun M := ⟨⟨M.1, M.2.1⟩, M.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem acceptedPatternEquiv_val (S : AcceptedPatterns H) :
    (acceptedPatternEquiv H S).1 = S.1.1 := rfl

instance acceptedPatternsFintype (H : Hypergraph V) : Fintype (AcceptedPatterns H) :=
  Fintype.ofEquiv (PerfectMatchings H) (acceptedPatternEquiv H).symm

/-- The product coefficient obtained by expanding independent binary source states. -/
def patternAmplitude (p φ : Finset V → ℝ) (S : EmissionPattern H) : ℂ :=
  (∏ e ∈ S.1, emissionAmplitude (p e) (φ e)) *
    ∏ e ∈ H \ S.1, vacuumAmplitude (p e)

/-- The accepted coefficient vector, defined directly from accepted emission patterns. -/
def postselectedState (F : MatchingDecomposition H I) (p φ : Finset V → ℝ) :
    (V → I) → ℂ :=
  finitePushforward
    (fun S : AcceptedPatterns H => F.labelString (acceptedPatternEquiv H S))
    (fun S => patternAmplitude p φ S.1)

/-- The matching expansion of the postselected state follows from the explicit pattern bijection. -/
theorem postselectedState_eq_matchingState (F : MatchingDecomposition H I)
    (p φ : Finset V → ℝ) :
    postselectedState F p φ = F.acceptedState (binaryMatchingAmplitude p φ) := by
  classical
  funext s
  simpa only [postselectedState, MatchingDecomposition.acceptedState,
    finitePushforward, patternAmplitude, binaryMatchingAmplitude, acceptedPatternEquiv_val] using
      (acceptedPatternEquiv H).sum_comp
        (fun M => if F.labelString M = s then binaryMatchingAmplitude p φ M else 0)

/-- Proposition 2.1's support equivalence expressed directly through source postselection. -/
theorem postselectedState_support_iff_isRigid [Nonempty V] {d : ℕ}
    (F : MatchingDecomposition H (Fin d))
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 < p e ∧ p e < 1)
    (hnonempty : ∀ e ∈ H, e.Nonempty) :
    {s | postselectedState F p φ s ≠ 0} = F.constantLabels ↔ IsRigid H d := by
  rw [postselectedState_eq_matchingState]
  exact binaryState_support_iff_isRigid F p φ hp hnonempty

/-- The normalized postselected state of a uniform rigid network is the GHZ state. -/
theorem postselected_uniform_binary_eq_ghz [Fintype V] [Nonempty V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hH : Uniform H r)
    (hr : 0 < r) (hd : 0 < d) (hV : Fintype.card V = r * m)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    normalizedState (postselectedState (MatchingDecomposition.ofRigidFamily G)
      (fun _ => p) (fun _ => 0)) = ghzState V d := by
  rw [postselectedState_eq_matchingState]
  exact uniform_binary_state_eq_ghz G hH hr hd hV p hp hp1

end RigidGHZ.SourceModel
