module

public import RigidGHZ.Finite.ThreeEdgeCertificate
public import Mathlib.Data.Fin.VecNotation

/-!
# The thirteen matchings published by discrete_things in 2024

Source: the author's comment dated 2024-11-05 18:37 UTC at
https://math.stackexchange.com/questions/4994589/3-uniform-hypergraphs-with-only-disjoint-perfect-matchings
The original labels 1,...,9 are shifted down by one; row order is preserved.
The exact source data and provenance are in `DiscreteThings2024/source.json`.
-/

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The thirteen original matching rows, with zero-based vertex labels. -/
def discreteThings2024Matchings : Fin 13 → Hypergraph (Fin 9) := ![
  {{0,1,2}, {3,4,5}, {6,7,8}},
  {{0,1,7}, {2,5,8}, {3,4,6}},
  {{0,1,8}, {2,4,5}, {3,6,7}},
  {{0,2,3}, {1,6,8}, {4,5,7}},
  {{0,2,6}, {1,3,5}, {4,7,8}},
  {{0,3,4}, {1,2,7}, {5,6,8}},
  {{0,3,6}, {1,5,8}, {2,4,7}},
  {{0,3,8}, {1,5,7}, {2,4,6}},
  {{0,4,5}, {1,3,6}, {2,7,8}},
  {{0,4,8}, {1,3,7}, {2,5,6}},
  {{0,5,6}, {1,2,4}, {3,7,8}},
  {{0,5,7}, {1,4,6}, {2,3,8}},
  {{0,6,7}, {1,4,8}, {2,3,5}}]

/-- The exact thirty-nine triples in the original author's list. -/
def discreteThings2024Edges : List (Finset (Fin 9)) := [
  {0,1,2}, {3,4,5}, {6,7,8},
  {0,1,7}, {2,5,8}, {3,4,6},
  {0,1,8}, {2,4,5}, {3,6,7},
  {0,2,3}, {1,6,8}, {4,5,7},
  {0,2,6}, {1,3,5}, {4,7,8},
  {0,3,4}, {1,2,7}, {5,6,8},
  {0,3,6}, {1,5,8}, {2,4,7},
  {0,3,8}, {1,5,7}, {2,4,6},
  {0,4,5}, {1,3,6}, {2,7,8},
  {0,4,8}, {1,3,7}, {2,5,6},
  {0,5,6}, {1,2,4}, {3,7,8},
  {0,5,7}, {1,4,6}, {2,3,8},
  {0,6,7}, {1,4,8}, {2,3,5}]

def discreteThings2024Graph : Hypergraph (Fin 9) := discreteThings2024Edges.toFinset

theorem discreteThings2024_uniform : Uniform discreteThings2024Graph 3 := by
  unfold Uniform
  decide +kernel

theorem discreteThings2024_card : discreteThings2024Graph.card = 39 := by
  decide +kernel

theorem discreteThings2024_perfect :
    ∀ i, PerfectMatching discreteThings2024Graph (discreteThings2024Matchings i) := by
  unfold PerfectMatching
  decide +kernel

theorem discreteThings2024_disjoint :
    Pairwise (fun i j => Disjoint (discreteThings2024Matchings i)
      (discreteThings2024Matchings j)) := by
  unfold Pairwise
  decide +kernel

theorem discreteThings2024_completion :
    ∀ e ∈ discreteThings2024Graph, ∀ f ∈ discreteThings2024Graph,
      Disjoint e f → (Finset.univ \ (e ∪ f)) ∈ discreteThings2024Graph →
      ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) =
        discreteThings2024Matchings i := by
  have h : (discreteThings2024Edges.all (fun e => discreteThings2024Edges.all (fun f =>
      decide (Disjoint e f → (Finset.univ \ (e ∪ f)) ∈ discreteThings2024Graph →
        ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) =
          discreteThings2024Matchings i)))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq,
    discreteThings2024Graph, List.mem_toFinset] using h

/-- The source's completeness assertion is verified for ordinary matchings. -/
theorem discreteThings2024_rigid : IsRigid discreteThings2024Graph 13 := by
  refine ⟨{
    matching := discreteThings2024Matchings
    perfect := discreteThings2024_perfect
    edge_disjoint := discreteThings2024_disjoint
    covers := by decide +kernel
    complete := ?_ }⟩
  exact complete_of_pair_certificate (r := 3) (by decide) (by decide)
    discreteThings2024_uniform discreteThings2024Matchings discreteThings2024_completion

end RigidGHZ.Finite
