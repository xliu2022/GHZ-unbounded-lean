module

public import RigidGHZ.Finite.ThreeEdgeCertificate
public import RigidGHZ.Partite
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace RigidGHZ.Finite

set_option maxRecDepth 10000

/-- The six matchings from `a+b+c ∈ {0,2}` over `ZMod 3`, encoded on
three consecutive parts `{0,1,2}`, `{3,4,5}`, `{6,7,8}`. -/
def sixMatchings : Fin 6 → Hypergraph (Fin 9) := ![
  {{0,3,6}, {1,4,7}, {2,5,8}},
  {{0,4,8}, {1,5,6}, {2,3,7}},
  {{0,5,7}, {1,3,8}, {2,4,6}},
  {{0,3,8}, {1,4,6}, {2,5,7}},
  {{0,4,7}, {1,5,8}, {2,3,6}},
  {{0,5,6}, {1,3,7}, {2,4,8}}]

/-- The eighteen-edge six-rigid tripartite witness. -/
def sixEdges : List (Finset (Fin 9)) := [
  {0,3,6}, {1,4,7}, {2,5,8},
  {0,4,8}, {1,5,6}, {2,3,7},
  {0,5,7}, {1,3,8}, {2,4,6},
  {0,3,8}, {1,4,6}, {2,5,7},
  {0,4,7}, {1,5,8}, {2,3,6},
  {0,5,6}, {1,3,7}, {2,4,8}]

def sixGraph : Hypergraph (Fin 9) := sixEdges.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem six_uniform : Uniform sixGraph 3 := by
  unfold Uniform
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem six_card : sixGraph.card = 18 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem six_prescribed_perfect : ∀ i, PerfectMatching sixGraph (sixMatchings i) := by
  unfold PerfectMatching
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
 theorem six_prescribed_disjoint : Pairwise (fun i j => Disjoint (sixMatchings i) (sixMatchings j)) := by
  unfold Pairwise
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
 theorem six_completion_certificate :
    ∀ e ∈ sixGraph, ∀ f ∈ sixGraph,
      Disjoint e f →
      (Finset.univ \ (e ∪ f)) ∈ sixGraph →
      ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) = sixMatchings i := by
  have h : (sixEdges.all (fun e => sixEdges.all (fun f =>
      decide (Disjoint e f → (Finset.univ \ (e ∪ f)) ∈ sixGraph →
        ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph (Fin 9)) = sixMatchings i)))) = true := by
    decide
  simpa only [List.all_eq_true, decide_eq_true_eq, sixGraph, List.mem_toFinset] using h

/-- The natural three-part coloring of the nine vertices. -/
def sixColor (v : Fin 9) : Fin 3 := ⟨v.val / 3, by omega⟩

 theorem six_color_classes : ∀ i : Fin 3,
    (Finset.univ.filter (fun v : Fin 9 => sixColor v = i)).card = 3 := by decide

 theorem six_transversal_edges : ∀ e ∈ sixGraph, ∀ i : Fin 3,
    (e.filter (fun v => sixColor v = i)).card = 1 := by decide

/-- The displayed tripartite witness has precisely six perfect matchings. -/
 theorem six_rigid : IsRigid sixGraph 6 := by
  refine ⟨{
    matching := sixMatchings
    perfect := six_prescribed_perfect
    edge_disjoint := six_prescribed_disjoint
    covers := by decide
    complete := ?_ }⟩
  exact complete_of_pair_certificate (r := 3) (by decide) (by decide)
    six_uniform sixMatchings six_completion_certificate

/-- Each part of the natural coloring has size three, and every edge is transversal. -/
 theorem six_balanced_partite : BalancedPartite sixGraph 3 3 :=
  ⟨sixColor, six_color_classes, six_transversal_edges⟩

/-- The lower-bound half of the tripartite nine-vertex extremal theorem. -/
 theorem six_witness : ∃ H : Hypergraph (Fin 9),
    Uniform H 3 ∧ BalancedPartite H 3 3 ∧ IsRigid H 6 :=
  ⟨sixGraph, six_uniform, six_balanced_partite, six_rigid⟩

end RigidGHZ.Finite
