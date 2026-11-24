module

public import RigidGHZ.Finite.TwoEdgeCertificate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset

@[expose] public section
namespace RigidGHZ.Finite

/-- The ten complementary pairs of triples on six vertices. -/
def tenMatchings : Fin 10 → Hypergraph (Fin 6) := ![
  {{0,1,2}, {3,4,5}}, {{0,1,3}, {2,4,5}},
  {{0,1,4}, {2,3,5}}, {{0,1,5}, {2,3,4}},
  {{0,2,3}, {1,4,5}}, {{0,2,4}, {1,3,5}},
  {{0,2,5}, {1,3,4}}, {{0,3,4}, {1,2,5}},
  {{0,3,5}, {1,2,4}}, {{0,4,5}, {1,2,3}}]

/-- The complete three-uniform hypergraph on six vertices. -/
def tenGraph : Hypergraph (Fin 6) := {
  {0,1,2}, {3,4,5}, {0,1,3}, {2,4,5},
  {0,1,4}, {2,3,5}, {0,1,5}, {2,3,4},
  {0,2,3}, {1,4,5}, {0,2,4}, {1,3,5},
  {0,2,5}, {1,3,4}, {0,3,4}, {1,2,5},
  {0,3,5}, {1,2,4}, {0,4,5}, {1,2,3}}

set_option maxRecDepth 10000 in
 theorem ten_uniform : Uniform tenGraph 3 := by
  unfold Uniform
  decide

set_option maxRecDepth 10000 in
 theorem ten_prescribed_perfect : ∀ i, PerfectMatching tenGraph (tenMatchings i) := by
  unfold PerfectMatching
  decide

set_option maxRecDepth 10000 in
 theorem ten_prescribed_disjoint : Pairwise (fun i j => Disjoint (tenMatchings i) (tenMatchings j)) := by
  unfold Pairwise
  decide

set_option maxRecDepth 10000 in
 theorem ten_complement_certificate :
    ∀ e ∈ tenGraph, ∃ i, ({e, Finset.univ \ e} : Hypergraph (Fin 6)) = tenMatchings i := by
  decide

set_option maxRecDepth 10000 in
 theorem ten_rigid : IsRigid tenGraph 10 := by
  refine ⟨{
    matching := tenMatchings
    perfect := ten_prescribed_perfect
    edge_disjoint := ten_prescribed_disjoint
    covers := by decide
    complete := ?_ }⟩
  exact complete_of_complement_certificate (r := 3) (by decide) (by decide)
    ten_uniform tenMatchings ten_complement_certificate

set_option maxRecDepth 10000 in
 theorem tenGraph_complete : ∀ e : Finset (Fin 6), e.card = 3 → e ∈ tenGraph := by decide

/-- No three-uniform rigid hypergraph on six vertices can have more than ten
perfect matchings. -/
theorem six_vertex_upper {H : Hypergraph (Fin 6)} {d : ℕ}
    (hH : Uniform H 3) (hR : IsRigid H d) : d ≤ 10 := by
  obtain ⟨F⟩ := hR
  have hsub : H.filter (fun e => (0 : Fin 6) ∈ e) ⊆
      tenGraph.filter (fun e => (0 : Fin 6) ∈ e) := by
    intro e he
    obtain ⟨heH, he0⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨tenGraph_complete e (hH e heH), he0⟩
  have hb := Finset.card_le_card hsub
  change degree H 0 ≤ degree tenGraph 0 at hb
  rw [F.regular, Fintype.card_fin] at hb
  have ht : degree tenGraph 0 = 10 := by unfold degree; decide
  simpa only [ht] using hb

/-- A complete extremal formulation of `f₃(6)=10`, without introducing an
auxiliary maximum convention. -/
theorem six_vertex_exact :
    (∃ H : Hypergraph (Fin 6), Uniform H 3 ∧ IsRigid H 10) ∧
    (∀ (H : Hypergraph (Fin 6)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 10) :=
  ⟨⟨tenGraph, ten_uniform, ten_rigid⟩, fun _ _ => six_vertex_upper⟩

end RigidGHZ.Finite
