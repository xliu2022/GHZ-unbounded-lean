module

public import RigidGHZ.SourceModel.FiniteState
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Independent coherent binary sources

The coefficient of an accepted matching is the product of its emission
amplitudes and all complementary vacuum amplitudes. This is precisely the
finite accepted-state formula in equations (2.2)--(2.3) of the article.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- Forget completeness while retaining the physically prescribed color classes. -/
def MatchingDecomposition.ofRigidFamily (G : RigidFamily H I) : MatchingDecomposition H I where
  matching := G.matching
  perfect := G.perfect
  edge_disjoint := G.edge_disjoint
  covers := G.covers

/-- Emission amplitude relative to the source's vacuum phase reference. -/
def emissionAmplitude (p φ : ℝ) : ℂ :=
  Complex.exp ((φ : ℂ) * Complex.I) * (Real.sqrt p : ℂ)

/-- Vacuum amplitude in the normalized binary-source model. -/
def vacuumAmplitude (p : ℝ) : ℂ := (Real.sqrt (1 - p) : ℂ)

/-- Coefficient of the source-emission pattern specified by a perfect matching. -/
def binaryMatchingAmplitude (p φ : Finset V → ℝ) (M : PerfectMatchings H) : ℂ :=
  (∏ e ∈ M.1, emissionAmplitude (p e) (φ e)) *
    ∏ e ∈ H \ M.1, vacuumAmplitude (p e)

theorem emissionAmplitude_ne_zero {p : ℝ} (hp : 0 < p) (φ : ℝ) :
    emissionAmplitude p φ ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hp)

theorem vacuumAmplitude_ne_zero {p : ℝ} (hp : p < 1) :
    vacuumAmplitude p ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (sub_pos.mpr hp))

theorem binaryMatchingAmplitude_ne_zero (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 < p e ∧ p e < 1) (M : PerfectMatchings H) :
    binaryMatchingAmplitude p φ M ≠ 0 := by
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact emissionAmplitude_ne_zero (hp e (M.2.subset he)).1 (φ e)
  · apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact vacuumAmplitude_ne_zero (hp e (Finset.mem_sdiff.mp he).1).2

/-- Proposition 2.1's support equivalence for the actual binary-source coefficients. -/
theorem binaryState_support_iff_isRigid [Nonempty V] {d : ℕ}
    (F : MatchingDecomposition H (Fin d))
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 < p e ∧ p e < 1)
    (hnonempty : ∀ e ∈ H, e.Nonempty) :
    {s | F.acceptedState (binaryMatchingAmplitude p φ) s ≠ 0} = F.constantLabels
      ↔ IsRigid H d :=
  acceptedState_support_iff_isRigid F (binaryMatchingAmplitude p φ) hnonempty
    (binaryMatchingAmplitude_ne_zero p φ hp)

/-- The common positive amplitude when all probabilities agree and phases vanish. -/
def commonAmplitude (p : ℝ) (edges matchingSize : ℕ) : ℝ :=
  (Real.sqrt p) ^ matchingSize * (Real.sqrt (1 - p)) ^ (edges - matchingSize)

theorem commonAmplitude_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (edges m : ℕ) :
    0 < commonAmplitude p edges m :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr hp) _)
    (pow_pos (Real.sqrt_pos.mpr (sub_pos.mpr hp1)) _)

theorem binaryMatchingAmplitude_uniform (p : ℝ) (M : PerfectMatchings H) :
    binaryMatchingAmplitude (fun _ => p) (fun _ => 0) M =
      (commonAmplitude p H.card M.1.card : ℂ) := by
  simp [binaryMatchingAmplitude, emissionAmplitude, vacuumAmplitude, commonAmplitude,
    Finset.card_sdiff_of_subset M.2.subset]

theorem perfectMatching_card [Fintype V] {r m : ℕ}
    (hH : Uniform H r) (hr : 0 < r) (hV : Fintype.card V = r * m)
    (M : PerfectMatchings H) : M.1.card = m := by
  have h := M.2.card_mul_eq hH
  rw [hV, Nat.mul_comm r m] at h
  exact Nat.eq_of_mul_eq_mul_right hr h

theorem binaryMatchingAmplitude_common [Fintype V] {r m : ℕ}
    (hH : Uniform H r) (hr : 0 < r) (hV : Fintype.card V = r * m)
    (p : ℝ) (M : PerfectMatchings H) :
    binaryMatchingAmplitude (fun _ => p) (fun _ => 0) M =
      (commonAmplitude p H.card m : ℂ) := by
  rw [binaryMatchingAmplitude_uniform, perfectMatching_card hH hr hV M]

end RigidGHZ.SourceModel
