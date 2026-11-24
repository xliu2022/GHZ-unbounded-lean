module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi

/-!
# Sharp finite rigid triple systems

This statement file records f3(6)=10, f3(9)=13, and g3(3)=6, together
with the within-parts uniqueness of the last extremizer.  Attainment and
universal upper bounds are stated separately in each conjunction. Rigidity
means an exhaustive edge-disjoint decomposition of the ordinary hypergraph's
perfect matchings. The unrestricted nine-vertex upper proof includes a proved
translation of those conditions into finite clauses and reconstructed Lean
proofs of six propositional refutations. No solver answer is an axiom.

These are the sharp finite conclusions of Li and Liu's article. Only the
Challenge statements have deliberate holes; FiniteSolution imports the proofs.
-/

@[expose] public section
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

/-- Exactly `d` prescribed perfect matchings, with no additional matching. -/
def IsRigid {V : Type*} [DecidableEq V] (H : Hypergraph V) (d : ℕ) : Prop :=
  Nonempty (RigidFamily H (Fin d))

/-- A coloring with `r` equal parts of size `m`, each met once by every edge. -/
def BalancedPartite {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (r m : ℕ) : Prop :=
  ∃ color : V → Fin r,
    (∀ i, (Finset.univ.filter (fun v => color v = i)).card = m) ∧
    ∀ e ∈ H, ∀ i, (e.filter (fun v => color v = i)).card = 1

/-- A transversal specified by one coordinate in each part. -/
def tupleEdge {A W : Type*} [Fintype A] [DecidableEq A] [DecidableEq W]
    (x : A → W) : Finset (A × W) :=
  Finset.univ.image (fun a => (a, x a))

/-- Image of an edge under a vertex equivalence. -/
def relabelEdge {V W : Type*}
    (f : V ≃ W) (e : Finset V) : Finset W := e.map f.toEmbedding

/-- Image of the whole edge set under a vertex equivalence. -/
def relabelHypergraph {V W : Type*} [DecidableEq W]
    (f : V ≃ W) (H : Hypergraph V) : Hypergraph W := H.image (relabelEdge f)

namespace Finite

/-- The exact value `f₃(6)=10`. -/
theorem six_vertex_exact :
    (∃ H : Hypergraph (Fin 6), Uniform H 3 ∧ IsRigid H 10) ∧
    (∀ (H : Hypergraph (Fin 6)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 10) := by sorry

/-- The exact value `g₃(3)=6` for three parts with three vertices each. -/
theorem tripartite_three_exact :
    (∃ H : Hypergraph (Fin 9), Uniform H 3 ∧ BalancedPartite H 3 3 ∧ IsRigid H 6) ∧
    (∀ (H : Hypergraph (Fin 9)) (d : ℕ), BalancedPartite H 3 3 → IsRigid H d → d ≤ 6) := by sorry

/-- The complement of the order-three addition table; addition is modulo 3. -/
def latinComplementGraph : Hypergraph (Fin 3 × Fin 3) :=
  ((Finset.univ : Finset (Fin 3 → Fin 3)).filter (fun x => x 0 ≠ x 1 + x 2)).image tupleEdge

/-- Equality in the tripartite bound is unique up to relabeling WITHIN parts. -/
theorem tripartite_three_unique {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) :
    ∃ f : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3),
      (∀ v, (f v).1 = v.1) ∧ relabelHypergraph f H = latinComplementGraph := by sorry

/-- The unrestricted nine-vertex optimum, including attainment. -/
theorem nine_vertex_exact :
    (∃ H : Hypergraph (Fin 9), Uniform H 3 ∧ IsRigid H 13) ∧
    (∀ H : Hypergraph (Fin 9), ∀ d : ℕ, Uniform H 3 → IsRigid H d → d ≤ 13) := by sorry

end Finite
end RigidGHZ
