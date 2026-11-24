module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Exact binary-source GHZ states

This self-contained statement file describes the finite coherent binary-source
model of the article. Each finite source support either emits once or stays
in vacuum. Its emission amplitude is exp(i*phase)*sqrt(p), and its vacuum
amplitude is sqrt(1-p). Accepted patterns have exactly one photon per path.
Their coefficients are summed at the observed string of source-class labels.
The squared norm is the finite sum of squared complex moduli.

Theorem 1.1 constructs an actual network at every positive part size and proves
initial normalization, the exact normalized GHZ coefficient vector, and a
positive success probability. Proposition 2.1 identifies GHZ label support with
ordinary hypergraph rigidity. Proposition 5.1 gives the sharp success bound and
its unique pump probabilities under the equal-branch-magnitude constraint.
The phase-correction theorem acts on one specified output path.

All definitions below are reproduced from the substantive development; they
have their ordinary finite-set and coefficient-vector meanings. Only the
selected theorem statements have deliberate holes. PhysicsSolution does not
import this file. The independent-source, simple-support, orthogonal-label,
and exact-photon-postselection assumptions are encoded explicitly here.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RigidGHZ


abbrev Hypergraph (V : Type*) := Finset (Finset V)

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. -/
def Uniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A perfect matching consists of edges of `H` and covers each vertex exactly once. -/
def PerfectMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ ∀ v : V, (M.filter (fun e => v ∈ e)).card = 1

/-- The number of edges containing a vertex. -/
def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- A specified, exhaustive decomposition into pairwise edge-disjoint perfect matchings. -/
structure RigidFamily (H : Hypergraph V) (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching
  complete : ∀ M, PerfectMatching H M → ∃ i, M = matching i

/-- `H` is `d`-rigid: its edges partition into `d` perfect matchings, and it has no others. -/
def IsRigid (H : Hypergraph V) (d : ℕ) : Prop :=
  Nonempty (RigidFamily H (Fin d))

namespace PerfectMatching
theorem subset {H M : Hypergraph V} (h : PerfectMatching H M) : M ⊆ H := h.1

 theorem existsUnique_edge {H M : Hypergraph V} (h : PerfectMatching H M) (v : V) :
    ∃! e, e ∈ M ∧ v ∈ e := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (h.2 v)
  have hem : e ∈ M.filter (fun e => v ∈ e) := by rw [he]; simp
  refine ⟨e, Finset.mem_filter.mp hem, ?_⟩
  intro f hf
  have hfm : f ∈ M.filter (fun e => v ∈ e) := Finset.mem_filter.mpr hf
  rw [he] at hfm
  exact Finset.mem_singleton.mp hfm

end PerfectMatching

end RigidGHZ

namespace RigidGHZ


/-- A balanced multipartition whose every edge meets every part exactly once. -/
def BalancedPartite {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (r m : ℕ) : Prop :=
  ∃ color : V → Fin r,
    (∀ i, (Finset.univ.filter (fun v => color v = i)).card = m) ∧
    ∀ e ∈ H, ∀ i, (e.filter (fun v => color v = i)).card = 1

end RigidGHZ

namespace RigidGHZ.SourceModel

variable {V I : Type*} [DecidableEq V] [Fintype I]

/-- A prescribed edge decomposition, without assuming that it is exhaustive on matchings. -/
structure MatchingDecomposition (H : Hypergraph V) (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching

/-- The actual perfect matchings of `H`, not just the prescribed ones. -/
def PerfectMatchings (H : Hypergraph V) := {M : Hypergraph V // PerfectMatching H M}

variable {H : Hypergraph V}
def incidentEdge (M : PerfectMatchings H) (v : V) : Finset V :=
  Classical.choose (M.2.existsUnique_edge v)

theorem incidentEdge_spec (M : PerfectMatchings H) (v : V) :
    incidentEdge M v ∈ M.1 ∧ v ∈ incidentEdge M v :=
  (Classical.choose_spec (M.2.existsUnique_edge v)).1

namespace MatchingDecomposition
variable (F : MatchingDecomposition H I)
theorem mem_iff {e : Finset V} : e ∈ H ↔ ∃ i, e ∈ F.matching i := by
  calc
    e ∈ H ↔ e ∈ Finset.univ.biUnion F.matching :=
      iff_of_eq (congrArg (fun K : Hypergraph V => e ∈ K) F.covers)
    _ ↔ ∃ i, e ∈ F.matching i := by simp

def edgeColor (e : H) : I := Classical.choose (F.mem_iff.mp e.2)
/-- The observed source-label string of a perfect matching. -/
def labelString (M : PerfectMatchings H) (v : V) : I :=
  F.edgeColor ⟨incidentEdge M v, M.2.subset (incidentEdge_spec M v).1⟩
/-- The prescribed class is itself an actual perfect matching. -/
def prescribed (i : I) : PerfectMatchings H := ⟨F.matching i, F.perfect i⟩
/-- The GHZ basis strings, one constant string for each prescribed class. -/
def constantLabels (_F : MatchingDecomposition H I) : Set (V → I) :=
  Set.range (fun i : I => fun _ : V => i)

end MatchingDecomposition

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

variable {α β : Type*} [Fintype α]

/-- Add amplitudes of all alternatives that produce the same output label. -/
def finitePushforward (f : α → β) (b : α → ℂ) (y : β) : ℂ := by
  classical
  exact ∑ x, if f x = y then b x else 0

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- There are finitely many perfect matchings, since each is a subset of `H`. -/
instance perfectMatchingsFintype (H : Hypergraph V) : Fintype (PerfectMatchings H) :=
  Fintype.ofInjective
    (fun M : PerfectMatchings H =>
      (⟨M.1, Finset.mem_powerset.mpr M.2.subset⟩ : H.powerset))
    (by
      intro M N h
      exact Subtype.ext (congrArg (fun s : H.powerset => s.1) h))

namespace MatchingDecomposition
variable (F : MatchingDecomposition H I)
/-- The coefficient of each output label string after one-photon-per-path selection. -/
def acceptedState (b : PerfectMatchings H → ℂ) : (V → I) → ℂ :=
  finitePushforward F.labelString b

end MatchingDecomposition

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

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

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel


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

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

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

/-- Proposition 2.1: exact accepted support iff ordinary rigidity. -/
theorem postselectedState_support_iff_isRigid [Nonempty V] {d : ℕ}
    (F : MatchingDecomposition H (Fin d))
    (p φ : Finset V → ℝ) (hp : ∀ e ∈ H, 0 < p e ∧ p e < 1)
    (hnonempty : ∀ e ∈ H, e.Nonempty) :
    {s | postselectedState F p φ s ≠ 0} = F.constantLabels ↔ IsRigid H d := by sorry

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

variable {V : Type*} [DecidableEq V] {H : Hypergraph V}

def emissionPatternEquiv (H : Hypergraph V) : EmissionPattern H ≃ ↥H.powerset where
  toFun S := ⟨S.val, Finset.mem_powerset.mpr S.property⟩
  invFun S := ⟨S.val, Finset.mem_powerset.mp S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance emissionPatternFintype (H : Hypergraph V) : Fintype (EmissionPattern H) :=
  Fintype.ofEquiv ↥H.powerset (emissionPatternEquiv H).symm

/-- The independent-source initial coefficient vector is normalized. -/
theorem joint_binary_state_normalized (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) :
    stateNormSq (patternAmplitude p φ : EmissionPattern H → ℂ) = 1 := by sorry

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

variable {V I : Type*} [DecidableEq V] [Fintype V] [Fintype I] {H : Hypergraph V}

/-- Probability of the one-photon-per-path accepted event. -/
def successProbability (F : MatchingDecomposition H I) (p φ : Finset V → ℝ) : ℝ :=
  stateNormSq (postselectedState F p φ)

/-- Proposition 5.1: sharp success bound and its unique equality case. -/
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
      ∀ e ∈ H, p e = 1 / ((n : ℝ) + 1)) := by sorry

/-- Uniform probabilities attain the success bound, for all phases. -/
theorem optimal_binary_success_attained [Nonempty V] {r m n : ℕ}
    (G : RigidFamily H (Fin (n + 1))) (hH : Uniform H r)
    (hr : 0 < r) (hn : 0 < n) (hV : Fintype.card V = r * m)
    (φ : Finset V → ℝ) :
    successProbability (MatchingDecomposition.ofRigidFamily G)
      (fun _ => 1 / ((n : ℝ) + 1)) φ =
      ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) ^ m *
        (1 - 1 / ((n : ℝ) + 1)) ^ (m * n) := by sorry

end RigidGHZ.SourceModel

namespace RigidGHZ.SourceModel

variable {V I : Type*}

/-- The action of a diagonal phase transformation on one path in the local label basis. -/
def localPhaseCorrection (phase : I → ℂ) (v : V) (ψ : (V → I) → ℂ) (s : V → I) : ℂ :=
  phase (s v) * ψ s

variable [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- Equal nonzero magnitudes can be corrected at one specified path. -/
theorem equal_magnitude_phase_correction [Fintype V] [Nonempty V] {d : ℕ}
    (G : RigidFamily H (Fin d)) (hd : 0 < d)
    (hnonempty : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (q : ℝ) (hq : 0 < q)
    (hmod : ∀ M, Complex.normSq (b M) = q * q) (v : V) :
    ∃ phase : Fin d → ℂ,
      (∀ i, Complex.normSq (phase i) = 1) ∧
      localPhaseCorrection phase v
        (normalizedState ((MatchingDecomposition.ofRigidFamily G).acceptedState b)) =
          ghzState V d := by sorry

end RigidGHZ.SourceModel

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
/-- Both the initial normalization and the exact accepted GHZ vector are certified. -/
def ProducesGHZ (p : ℝ) : Prop :=
  stateNormSq (patternAmplitude (fun _ => p) (fun _ => 0) : EmissionPattern N.support → ℂ) = 1 ∧
    normalizedState (N.accepted p) = ghzState (Fin r × Fin m) d ∧ 0 < N.probability p

end CoherentNetwork

/-- Theorem 1.1 with the quantitative dimension bound. -/
theorem ghz_growth_quantitative (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ∃ N : CoherentNetwork r m d, 0 < d ∧
      ((m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3)) ^
        (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d ∧
      ∀ p : ℝ, 0 < p → p < 1 → N.ProducesGHZ p := by sorry

/-- Theorem 1.1 in its constant-times-path-count formulation. -/
theorem ghz_growth (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ d : ℕ, ∃ N : CoherentNetwork r m d, 0 < d ∧
        c * ((r * m : ℕ) : ℝ) ^ (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d ∧
        ∀ p : ℝ, 0 < p → p < 1 → N.ProducesGHZ p := by sorry

end RigidGHZ.SourceModel
