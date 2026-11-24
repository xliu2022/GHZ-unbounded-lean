module

public import RigidGHZ.Construction.MainGrowth
public import RigidGHZ.SourceModel.JointState

/-!
# The physical GHZ growth theorem

A network contains the actual finite simple source hypergraph and its proved
perfect-matching labels. The coefficient vector is the explicit product expansion
of independent binary sources, with exact one-photon-per-path postselection.
The theorem below supplies such networks at every positive part size and proves
the stated quantitative GHZ dimension bound.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

/-- An actual coherent source network with `r` equal groups of `m` paths. -/
structure CoherentNetwork (r m d : ℕ) where
  support : Hypergraph (Fin r × Fin m)
  uniform : Uniform support r
  partite : BalancedPartite support r m
  family : RigidFamily support (Fin d)

namespace CoherentNetwork

variable {r m d : ℕ} (N : CoherentNetwork r m d)

def decomposition : MatchingDecomposition N.support (Fin d) :=
  MatchingDecomposition.ofRigidFamily N.family

def accepted (p : ℝ) : ((Fin r × Fin m) → Fin d) → ℂ :=
  postselectedState N.decomposition (fun _ => p) (fun _ => 0)

def probability (p : ℝ) : ℝ :=
  successProbability N.decomposition (fun _ => p) (fun _ => 0)

/-- There are exactly `d*m` independently pumped source configurations. -/
theorem source_count (hr : 0 < r) : N.support.card = d * m := by
  simpa only [Fintype.card_fin] using N.family.card_edges N.uniform hr
    (by simp : Fintype.card (Fin r × Fin m) = r * m)

/-- Identical positive pump probabilities and zero relative phases give GHZ exactly. -/
theorem normalized_eq_ghz (hr : 0 < r) (hm : 0 < m) (hd : 0 < d)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    normalizedState (N.accepted p) = ghzState (Fin r × Fin m) d := by
  letI : Nonempty (Fin r × Fin m) := ⟨(⟨0, hr⟩, ⟨0, hm⟩)⟩
  exact postselected_uniform_binary_eq_ghz (m := m) N.family N.uniform hr hd (by simp) p hp hp1

/-- Postselection has strictly positive probability, with the exact binary-source value. -/
theorem probability_formula (hr : 0 < r) (hm : 0 < m)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    N.probability p = (d : ℝ) * p ^ m * (1 - p) ^ (m * (d - 1)) := by
  letI : Nonempty (Fin r × Fin m) := ⟨(⟨0, hr⟩, ⟨0, hm⟩)⟩
  exact uniform_binary_success (m := m) N.family N.uniform hr (by simp) p hp hp1

theorem probability_pos (hr : 0 < r) (hm : 0 < m) (hd : 0 < d)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : 0 < N.probability p := by
  letI : Nonempty (Fin r × Fin m) := ⟨(⟨0, hr⟩, ⟨0, hm⟩)⟩
  exact uniform_binary_success_pos (m := m) N.family N.uniform hr hd (by simp) p hp hp1

/-- Both the initial normalization and the exact accepted GHZ vector are certified. -/
def ProducesGHZ (p : ℝ) : Prop :=
  stateNormSq (patternAmplitude (fun _ => p) (fun _ => 0) : EmissionPattern N.support → ℂ) = 1 ∧
    normalizedState (N.accepted p) = ghzState (Fin r × Fin m) d ∧ 0 < N.probability p

theorem producesGHZ (hr : 0 < r) (hm : 0 < m) (hd : 0 < d)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : N.ProducesGHZ p := by
  exact ⟨joint_binary_state_normalized _ _ (fun _ _ => ⟨hp.le, hp1.le⟩),
    N.normalized_eq_ghz hr hm hd p hp hp1, N.probability_pos hr hm hd p hp hp1⟩

end CoherentNetwork

/-- Quantitative source-model form of Theorem 1.1 at `n=r*m` paths. -/
theorem ghz_growth_quantitative (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ∃ N : CoherentNetwork r m d, 0 < d ∧
      ((m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3)) ^
        (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d ∧
      ∀ p : ℝ, 0 < p → p < 1 → N.ProducesGHZ p := by
  obtain ⟨d, ⟨H, hU, hP, ⟨G⟩⟩, hlower⟩ := Growth.balanced_growth r m hr hm
  have hk : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbase : (0 : ℝ) < (m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3) := by positivity
  have hd' : (0 : ℝ) < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hbase _) hlower
  have hd : 0 < d := by exact_mod_cast hd'
  let N : CoherentNetwork r m d := ⟨H, hU, hP, G⟩
  exact ⟨d, N, hd, hlower, fun p hp hp1 => N.producesGHZ (by omega) (by omega) hd p hp hp1⟩

/-- An explicit positive constant depending only on the source order. -/
def growthConstant (r : ℕ) : ℝ :=
  (1 / (128 * (r : ℝ) * ((r - 2 : ℕ) : ℝ) ^ 3)) ^
    (2 * ((r - 2 : ℕ) : ℝ) / 7)

theorem growthConstant_pos {r : ℕ} (hr : 3 ≤ r) : 0 < growthConstant r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hk : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
  apply Real.rpow_pos_of_pos
  positivity

theorem growthConstant_scaling (r m : ℕ) (hr : 3 ≤ r) :
    growthConstant r * ((r * m : ℕ) : ℝ) ^ (2 * ((r - 2 : ℕ) : ℝ) / 7) =
      ((m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3)) ^ (2 * ((r - 2 : ℕ) : ℝ) / 7) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hk : (0 : ℝ) < (r - 2 : ℕ) := by exact_mod_cast (show 0 < r - 2 by omega)
  have hden : (0 : ℝ) < 128 * r * ((r - 2 : ℕ) : ℝ) ^ 3 := by positivity
  unfold growthConstant
  rw [← Real.mul_rpow (one_div_pos.mpr hden).le (Nat.cast_nonneg (r * m))]
  congr 1
  push_cast
  field_simp

/--
Theorem 1.1: for every source order `r≥3`, a positive constant `c_r` works at
every positive multiple `n=r*m`. The same network produces normalized GHZ for
any common source probability in `(0,1)`, with every emission in phase with vacuum.
-/
theorem ghz_growth (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ d : ℕ, ∃ N : CoherentNetwork r m d, 0 < d ∧
        c * ((r * m : ℕ) : ℝ) ^ (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d ∧
        ∀ p : ℝ, 0 < p → p < 1 → N.ProducesGHZ p := by
  refine ⟨growthConstant r, growthConstant_pos hr, ?_⟩
  intro m hm
  obtain ⟨d, N, hd, hlower, hstate⟩ := ghz_growth_quantitative r m hr hm
  exact ⟨d, N, hd, by simpa only [growthConstant_scaling r m hr] using hlower, hstate⟩

end RigidGHZ.SourceModel
