module

public import RigidGHZ.SourceModel.BinaryState
public import Mathlib.Data.Fintype.Pi

/-!
# Normalization to the GHZ coefficient vector

The local label basis identifies an `n`-path, `d`-label state with a function
from `V → Fin d` to the complex numbers. Its squared Hilbert norm is the sum
of squared moduli. The theorem below proves that identical positive binary
probabilities and zero relative phases yield the standard normalized GHZ
coefficient vector whenever the source hypergraph is rigid.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

/-- Squared Hilbert norm in a finite orthonormal basis. -/
def stateNormSq {B : Type*} [Fintype B] (ψ : B → ℂ) : ℝ :=
  ∑ b, Complex.normSq (ψ b)

/-- Normalize a finite coefficient vector by its Hilbert norm. -/
def normalizedState {B : Type*} [Fintype B] (ψ : B → ℂ) (b : B) : ℂ :=
  ψ b / (Real.sqrt (stateNormSq ψ) : ℂ)

/-- The standard GHZ vector in the local label basis. -/
def ghzState (V : Type*) (d : ℕ) (s : V → Fin d) : ℂ := by
  classical
  exact if s ∈ Set.range (fun i : Fin d => fun _ : V => i)
    then 1 / (Real.sqrt (d : ℝ) : ℂ) else 0

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- The actual perfect matchings of a rigid hypergraph are exactly its indices. -/
def rigidMatchingEquiv [Nonempty V] (G : RigidFamily H I) : I ≃ PerfectMatchings H :=
  Equiv.ofBijective (MatchingDecomposition.ofRigidFamily G).prescribed (by
    constructor
    · intro i j hij
      apply G.matching_injective
      exact congrArg Subtype.val hij
    · intro M
      obtain ⟨i, hi⟩ := G.complete M.1 M.2
      exact ⟨i, Subtype.ext hi.symm⟩)

theorem perfectMatchings_card [Nonempty V] (G : RigidFamily H I) :
    Fintype.card (PerfectMatchings H) = Fintype.card I :=
  (Fintype.card_congr (rigidMatchingEquiv G)).symm

/-- A state supported on the constant strings, with the same coefficient at each one. -/
def constantLabelState (F : MatchingDecomposition H I) (q : ℂ) (s : V → I) : ℂ := by
  classical
  exact if s ∈ F.constantLabels then q else 0

theorem acceptedState_common (G : RigidFamily H I)
    (hnonempty : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (q : ℂ) (hb : ∀ M, b M = q) :
    (MatchingDecomposition.ofRigidFamily G).acceptedState b =
      constantLabelState (MatchingDecomposition.ofRigidFamily G) q := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  have hsupport : F.acceptedLabels = F.constantLabels :=
    (F.acceptedLabels_eq_iff hnonempty).mpr G.complete
  funext s
  change F.acceptedState b s = constantLabelState F q s
  unfold constantLabelState
  by_cases hs : s ∈ F.constantLabels
  · rw [if_pos hs]
    obtain ⟨i, hi⟩ := hs
    have hlabel : F.labelString (F.prescribed i) = s :=
      (F.labelString_prescribed i).trans hi
    rw [← hlabel, F.acceptedState_at_matching b hnonempty]
    exact hb _
  · rw [if_neg hs]
    have hs' : s ∉ F.acceptedLabels := by simpa only [hsupport] using hs
    exact finitePushforward_outside F.labelString b hs'

theorem acceptedState_normSq_common [Fintype V] [Nonempty V]
    (G : RigidFamily H I) (hnonempty : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (q : ℝ) (hb : ∀ M, b M = (q : ℂ)) :
    stateNormSq ((MatchingDecomposition.ofRigidFamily G).acceptedState b)
      = (Fintype.card I : ℝ) * (q * q) := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  change (∑ s, Complex.normSq (finitePushforward F.labelString b s)) = _
  rw [finitePushforward_normSq F.labelString b (F.labelString_injective hnonempty)]
  simp [hb, Complex.normSq_ofReal, perfectMatchings_card G]

/-- Equal positive matching amplitudes normalize to the GHZ vector. -/
theorem normalized_common_eq_ghz [Fintype V] [Nonempty V] {d : ℕ}
    (G : RigidFamily H (Fin d)) (hd : 0 < d)
    (hnonempty : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (q : ℝ) (hq : 0 < q)
    (hb : ∀ M, b M = (q : ℂ)) :
    normalizedState ((MatchingDecomposition.ofRigidFamily G).acceptedState b) =
      ghzState V d := by
  classical
  let F := MatchingDecomposition.ofRigidFamily G
  have hnorm : stateNormSq (F.acceptedState b) = (d : ℝ) * (q * q) := by
    simpa using acceptedState_normSq_common G hnonempty b q hb
  have hsqrt : Real.sqrt (stateNormSq (F.acceptedState b)) = Real.sqrt (d : ℝ) * q := by
    rw [hnorm, Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_mul_self hq.le]
  have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdne : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hdreal)
  funext s
  change F.acceptedState b s / (Real.sqrt (stateNormSq (F.acceptedState b)) : ℂ) = _
  rw [hsqrt, acceptedState_common G hnonempty b (q : ℂ) hb]
  change constantLabelState F (q : ℂ) s / ((Real.sqrt (d : ℝ) * q : ℝ) : ℂ) = _
  unfold constantLabelState ghzState MatchingDecomposition.constantLabels
  split_ifs
  · rw [Complex.ofReal_mul]
    field_simp
  · simp

/-- A positive-uniformity source support cannot be empty. -/
theorem nonempty_edges_of_uniform {r : ℕ} (hH : Uniform H r) (hr : 0 < r) :
    ∀ e ∈ H, e.Nonempty := by
  intro e he
  apply Finset.card_pos.mp
  rw [hH e he]
  exact hr

/--
Identical binary source probabilities and zero relative phases give the exact
normalized GHZ state. This is the source-model bridge used by Theorem 1.1.
-/
theorem uniform_binary_state_eq_ghz [Fintype V] [Nonempty V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hH : Uniform H r)
    (hr : 0 < r) (hd : 0 < d) (hV : Fintype.card V = r * m)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    normalizedState ((MatchingDecomposition.ofRigidFamily G).acceptedState
      (binaryMatchingAmplitude (fun _ => p) (fun _ => 0))) = ghzState V d := by
  apply normalized_common_eq_ghz G hd (nonempty_edges_of_uniform hH hr)
    (binaryMatchingAmplitude (fun _ => p) (fun _ => 0)) (commonAmplitude p H.card m)
    (commonAmplitude_pos hp hp1 H.card m)
  exact binaryMatchingAmplitude_common hH hr hV p

end RigidGHZ.SourceModel
