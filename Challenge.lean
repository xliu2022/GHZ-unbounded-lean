module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rigid hypergraphs for unbounded GHZ dimension

The declarations below state the principal combinatorial results of
Heng Li and Xizhi Liu, *Unbounded GHZ dimension from fixed-order multiphoton
sources*.  A simple hypergraph is a finite set of finite vertex sets.  Its
specified perfect matchings partition its edges and exhaust ALL perfect
matchings; in particular no completeness assumption is hidden in a witness.

The growth theorem constructs such hypergraphs at every positive part size,
with the paper's explicit exponent and constant. The upper bounds apply to
every ordinary rigid hypergraph, with their exact floor and logarithmic
consequences. Finite extremal values and the physical source-state results
have separate statement files, FiniteChallenge.lean and PhysicsChallenge.lean.

Only this Challenge's deliberate theorem holes are unproved.  Solution.lean
imports the substantive proofs and never imports this module.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace RigidGHZ

/-- A finite simple hypergraph. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- Every edge has exactly `r` vertices. -/
def Uniform {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- Edges of `H` covering each vertex exactly once. -/
def PerfectMatching {V : Type*} [DecidableEq V] (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ ∀ v : V, (M.filter (fun e => v ∈ e)).card = 1

/-- An exhaustive, edge-disjoint perfect-matching decomposition. -/
structure RigidFamily {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching
  complete : ∀ M, PerfectMatching H M → ∃ i, M = matching i

/-- An exhaustive family of `d` edge-disjoint perfect matchings. For a nonempty
vertex set these are exactly `d` distinct matchings. -/
def IsRigid {V : Type*} [DecidableEq V] (H : Hypergraph V) (d : ℕ) : Prop :=
  Nonempty (RigidFamily H (Fin d))

/-- A coloring with `r` equal parts of size `m`, each met once by every edge. -/
def BalancedPartite {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (r m : ℕ) : Prop :=
  ∃ color : V → Fin r,
    (∀ i, (Finset.univ.filter (fun v => color v = i)).card = m) ∧
    ∀ e ∈ H, ∀ i, (e.filter (fun v => color v = i)).card = 1

namespace Growth

/-- Existence on the canonical vertex set of `r` parts, each of size `m`. -/
def ExistsRigid (r m d : ℕ) : Prop :=
  ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H d

/-- The explicit scale `128 k³` in the quantitative construction. -/
def scale (k : ℕ) : ℕ := 128 * k ^ 3

/-- The ceiling in Corollary 3.2, with `k=r−2`. -/
def prescribedSize (k d : ℕ) : ℕ :=
  ⌈(scale k : ℝ) * (d : ℝ) ^ ((7 : ℝ) / (2 * (k : ℝ)))⌉₊

/-- Theorem 3.1: the quantitative lower bound at EVERY positive part size. -/
theorem balanced_growth (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ExistsRigid r m d ∧
      ((m : ℝ) / (128 * ((r - 2 : ℕ) : ℝ) ^ 3)) ^
        (2 * ((r - 2 : ℕ) : ℝ) / 7) ≤ d := by sorry

/-- Exact integer-power formulation of the same growth guarantee. -/
theorem balanced_growth_integer (r m : ℕ) (hr : 3 ≤ r) (hm : 1 ≤ m) :
    ∃ d : ℕ, ExistsRigid r m d ∧
      m ^ (2 * (r - 2)) ≤ (128 * (r - 2) ^ 3) ^ (2 * (r - 2)) * d ^ 7 := by sorry

/-- Corollary 3.2: exactly the requested dimension and exactly `d*m` edges. -/
theorem prescribed_dimension (r d : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) :
    ∃ H : Hypergraph (Fin r × Fin (prescribedSize (r - 2) d)),
      Uniform H r ∧ BalancedPartite H r (prescribedSize (r - 2) d) ∧
      IsRigid H d ∧ H.card = d * prescribedSize (r - 2) d := by sorry

end Growth

namespace UpperBounds

/-- Finite harmonic sum with the indicated starting denominator. -/
def shiftedHarmonic (k : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, 1 / (k + j)

/-- `1 + 1/2 + ... + 1/m`. -/
def harmonic (m : ℕ) : ℝ := shiftedHarmonic 1 m

/-- The paper's coefficient, with the special value `β₁=1`. -/
def beta (m : ℕ) : ℝ := if m = 1 then 1 else min ((m : ℝ) / ((2 : ℕ) : ℝ)) (harmonic m)

/-- All `k`-element subsets contained in at least one edge. -/
def shadow {V : Type*} [DecidableEq V] (H : Hypergraph V) (k : ℕ) : Finset (Finset V) :=
  H.biUnion (fun e => e.powersetCard k)

/-- The number of edges containing the specified vertex set. -/
def codegree {V : Type*} [DecidableEq V] (H : Hypergraph V) (S : Finset V) : ℕ :=
  (H.filter (fun e => S ⊆ e)).card

/-- A shadow set's contribution to the unrestricted upper bound. -/
def shadowContribution {V : Type*} [DecidableEq V]
    (r : ℕ) (H : Hypergraph V) (S : Finset V) : ℝ :=
  1 - (1 - 1 / (r : ℝ)) ^ codegree H S

/-- Theorem 4.1: all three inequalities in the unrestricted shadow bound. -/
theorem unrestricted_harmonic_shadow {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d : ℕ}
    (hR : IsRigid H d) (hH : Uniform H r) (hr : 2 ≤ r)
    (hV : Fintype.card V = r * m) :
    (d : ℝ) * beta m ≤ ∑ S ∈ shadow H (r - 1), shadowContribution r H S ∧
      (∑ S ∈ shadow H (r - 1), shadowContribution r H S) ≤
        ((shadow H (r - 1)).card : ℝ) ∧
      (shadow H (r - 1)).card ≤ (r * m).choose (r - 1) := by sorry

universe u_4
/-- Theorem 4.1: the stronger balanced multipartite upper bound. -/
theorem balanced_partite_harmonic_bound {V : Type u_4} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d : ℕ} (hr : 2 ≤ r)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    (d : ℝ) * beta m ≤ (m : ℝ) ^ (r - 1) := by sorry

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Hypergraph V}

/-- The unrestricted floor bound in Theorem 4.1. -/
theorem unrestricted_floor_bound {r m d : ℕ} (hR : IsRigid H d) (hU : Uniform H r)
    (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) :
    d ≤ ⌊((r * m).choose (r - 1) : ℝ) / beta m⌋₊ := by sorry

/-- The balanced multipartite floor bound in Theorem 4.1. -/
theorem balanced_partite_floor_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    d ≤ ⌊(m : ℝ) ^ (r - 1) / beta m⌋₊ := by sorry

/-- The explicit logarithmic bound implied by the harmonic estimate. -/
theorem unrestricted_log_bound {r m d : ℕ} (hR : IsRigid H d) (hU : Uniform H r)
    (hr : 2 ≤ r) (hm : 5 ≤ m) (hV : Fintype.card V = r * m) :
    (d : ℝ) ≤ ((r * m).choose (r - 1) : ℝ) / Real.log ((m : ℝ) + 1) := by sorry

/-- The corresponding logarithmic bound for balanced multipartite graphs. -/
theorem balanced_partite_log_bound {r m d : ℕ} (hr : 2 ≤ r) (hm : 5 ≤ m)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    (d : ℝ) ≤ (m : ℝ) ^ (r - 1) / Real.log ((m : ℝ) + 1) := by sorry

end UpperBounds
end RigidGHZ
