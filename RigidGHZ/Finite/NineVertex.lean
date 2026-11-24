module

public import RigidGHZ.Finite.ThreeEdgeCertificate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace RigidGHZ.Finite

/-- The thirteen perfect matchings in Table 1 of Li--Liu. -/
def thirteenMatchings : Fin 13 → Hypergraph (Fin 9) := ![
  {{0,1,2}, {3,4,5}, {6,7,8}},
  {{0,3,6}, {1,4,7}, {2,5,8}},
  {{0,4,8}, {1,5,6}, {2,3,7}},
  {{0,5,7}, {1,3,8}, {2,4,6}},
  {{0,1,5}, {2,6,7}, {3,4,8}},
  {{0,2,4}, {1,6,8}, {3,5,7}},
  {{0,7,8}, {1,2,3}, {4,5,6}},
  {{0,3,7}, {1,4,8}, {2,5,6}},
  {{0,4,6}, {1,5,7}, {2,3,8}},
  {{0,5,8}, {1,3,6}, {2,4,7}},
  {{0,1,3}, {2,6,8}, {4,5,7}},
  {{0,2,5}, {1,7,8}, {3,4,6}},
  {{0,6,7}, {1,2,4}, {3,5,8}}]

/-- The thirty-nine-edge, thirteen-matching witness on nine vertices. -/
def thirteenEdges : List (Finset (Fin 9)) := [
  {0,1,2}, {3,4,5}, {6,7,8},
  {0,3,6}, {1,4,7}, {2,5,8},
  {0,4,8}, {1,5,6}, {2,3,7},
  {0,5,7}, {1,3,8}, {2,4,6},
  {0,1,5}, {2,6,7}, {3,4,8},
  {0,2,4}, {1,6,8}, {3,5,7},
  {0,7,8}, {1,2,3}, {4,5,6},
  {0,3,7}, {1,4,8}, {2,5,6},
  {0,4,6}, {1,5,7}, {2,3,8},
  {0,5,8}, {1,3,6}, {2,4,7},
  {0,1,3}, {2,6,8}, {4,5,7},
  {0,2,5}, {1,7,8}, {3,4,6},
  {0,6,7}, {1,2,4}, {3,5,8}]

def thirteenGraph : Hypergraph (Fin 9) := thirteenEdges.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem thirteen_uniform : Uniform thirteenGraph 3 := by
  unfold Uniform
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem thirteen_card : thirteenGraph.card = 39 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem thirteen_prescribed_perfect : ∀ i, PerfectMatching thirteenGraph (thirteenMatchings i) := by
  unfold PerfectMatching
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem thirteen_prescribed_disjoint : Pairwise (fun i j => Disjoint (thirteenMatchings i) (thirteenMatchings j)) := by
  unfold Pairwise
  decide

/- A finite certificate: two disjoint edges whose complementary triple is an edge
already determine one of the thirteen prescribed perfect matchings. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
 theorem thirteen_completion_certificate :
    ∀ e ∈ thirteenGraph, ∀ f ∈ thirteenGraph,
      Disjoint e f →
      (Finset.univ \ (e ∪ f)) ∈ thirteenGraph →
      ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) = thirteenMatchings i := by
  have h : (thirteenEdges.all (fun e => thirteenEdges.all (fun f =>
      decide (Disjoint e f → (Finset.univ \ (e ∪ f)) ∈ thirteenGraph →
        ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) = thirteenMatchings i)))) = true := by
    decide
  simpa only [List.all_eq_true, decide_eq_true_eq, thirteenGraph, List.mem_toFinset] using h

/-- The explicit nine-vertex witness is thirteen-rigid in the standard sense. -/
 theorem thirteen_rigid : IsRigid thirteenGraph 13 := by
  refine ⟨{
    matching := thirteenMatchings
    perfect := thirteen_prescribed_perfect
    edge_disjoint := thirteen_prescribed_disjoint
    covers := by decide
    complete := ?_ }⟩
  exact complete_of_pair_certificate (r := 3) (by decide) (by decide)
    thirteen_uniform thirteenMatchings thirteen_completion_certificate

/-- The lower-bound half of the unrestricted nine-vertex extremal theorem. -/
 theorem thirteen_witness : ∃ H : Hypergraph (Fin 9), Uniform H 3 ∧ IsRigid H 13 :=
  ⟨thirteenGraph, thirteen_uniform, thirteen_rigid⟩

end RigidGHZ.Finite
