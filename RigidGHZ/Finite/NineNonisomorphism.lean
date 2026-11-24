module

public import RigidGHZ.Finite.NineDiscreteThings
public import RigidGHZ.Finite.NineAlgebraic
public import RigidGHZ.Supplement.DegreeRelabel

/-!
# The algebraic example differs from the 2024 example

We count hyperedges whose three vertex pairs all have codegree four. The count
is invariant under every vertex equivalence. It is three for the algebraic
construction and two for the exact list in the original author's 2024 comment.
-/

@[expose] public section
namespace RigidGHZ.Finite
open RigidGHZ.UpperBounds RigidGHZ.Supplement

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- A hyperedge whose vertex set is a triangle in the codegree-four graph. -/
def FourCodegreeTriangle (H : Hypergraph V) (e : Finset V) : Prop :=
  e.card = 3 ∧ ∀ a ∈ e, ∀ b ∈ e, a ≠ b → codegree H {a,b} = 4

instance fourCodegreeTriangleDecidable (H : Hypergraph V) (e : Finset V) :
    Decidable (FourCodegreeTriangle H e) := by
  unfold FourCodegreeTriangle
  infer_instance

/-- Only triangles that are also actual hyperedges are counted. -/
def fourCodegreeHyperedges (H : Hypergraph V) : Hypergraph V :=
  H.filter (FourCodegreeTriangle H)

theorem relabelEdge_pair (f : V ≃ W) (a b : V) :
    relabelEdge f {a,b} = {f a,f b} := by
  simp [relabelEdge]

theorem fourCodegreeTriangle_relabel (f : V ≃ W) (H : Hypergraph V)
    (e : Finset V) :
    FourCodegreeTriangle (relabelHypergraph f H) (relabelEdge f e) ↔
      FourCodegreeTriangle H e := by
  constructor
  · rintro ⟨hcard,hpairs⟩
    refine ⟨by simpa only [relabelEdge_card] using hcard, ?_⟩
    intro a ha b hb hab
    have hfa : f a ∈ relabelEdge f e := by simpa only [mem_relabelEdge,
      Equiv.symm_apply_apply] using ha
    have hfb : f b ∈ relabelEdge f e := by simpa only [mem_relabelEdge,
      Equiv.symm_apply_apply] using hb
    have h := hpairs (f a) hfa (f b) hfb (fun h => hab (f.injective h))
    rw [← relabelEdge_pair f a b, codegree_relabel] at h
    exact h
  · rintro ⟨hcard,hpairs⟩
    refine ⟨by simpa only [relabelEdge_card] using hcard, ?_⟩
    intro a ha b hb hab
    have h := hpairs (f.symm a) ((mem_relabelEdge f e a).mp ha)
      (f.symm b) ((mem_relabelEdge f e b).mp hb)
      (fun h => hab (f.symm.injective h))
    have hp : relabelEdge f {f.symm a,f.symm b} = {a,b} := by
      simp only [relabelEdge_pair, Equiv.apply_symm_apply]
    rw [← hp, codegree_relabel]
    exact h

theorem fourCodegreeHyperedges_relabel (f : V ≃ W) (H : Hypergraph V) :
    fourCodegreeHyperedges (relabelHypergraph f H) =
      relabelHypergraph f (fourCodegreeHyperedges H) := by
  change (H.image (relabelEdge f)).filter (FourCodegreeTriangle (relabelHypergraph f H)) =
    (H.filter (FourCodegreeTriangle H)).image (relabelEdge f)
  rw [Finset.filter_image]
  apply congrArg (fun S : Hypergraph V => S.image (relabelEdge f))
  apply Finset.filter_congr
  intro e _
  exact fourCodegreeTriangle_relabel f H e

/-- The count used to separate the examples is a genuine isomorphism invariant. -/
theorem fourCodegreeHyperedges_card_relabel (f : V ≃ W) (H : Hypergraph V) :
    (fourCodegreeHyperedges (relabelHypergraph f H)).card =
      (fourCodegreeHyperedges H).card := by
  rw [fourCodegreeHyperedges_relabel, relabelHypergraph,
    Finset.card_image_of_injective _ (relabelEdge_injective f)]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- These nine pairs form the three disjoint triangles 057, 138, and 246. -/
def thirteenFourPairs : Hypergraph (Fin 9) :=
  {{0,5},{0,7},{5,7},{1,3},{1,8},{3,8},{2,4},{2,6},{4,6}}

/-- These nine pairs form the three disjoint triangles 036, 178, and 245. -/
def discreteThings2024FourPairs : Hypergraph (Fin 9) :=
  {{0,3},{0,6},{3,6},{1,7},{1,8},{7,8},{2,4},{2,5},{4,5}}

theorem thirteen_codegree_four (a b : Fin 9) :
    codegree thirteenGraph {a,b} = 4 ↔ {a,b} ∈ thirteenFourPairs := by
  have h : ∀ a b : Fin 9,
      codegree thirteenGraph {a,b} = 4 ↔ {a,b} ∈ thirteenFourPairs := by
    decide +kernel
  exact h a b

theorem discreteThings2024_codegree_four (a b : Fin 9) :
    codegree discreteThings2024Graph {a,b} = 4 ↔
      {a,b} ∈ discreteThings2024FourPairs := by
  have h : ∀ a b : Fin 9,
      codegree discreteThings2024Graph {a,b} = 4 ↔
        {a,b} ∈ discreteThings2024FourPairs := by
    decide +kernel
  exact h a b

theorem thirteen_fourCodegreeHyperedges :
    fourCodegreeHyperedges thirteenGraph = {{0,5,7},{1,3,8},{2,4,6}} := by
  unfold fourCodegreeHyperedges FourCodegreeTriangle
  simp_rw [thirteen_codegree_four]
  decide +kernel

theorem discreteThings2024_fourCodegreeHyperedges :
    fourCodegreeHyperedges discreteThings2024Graph = {{0,3,6},{2,4,5}} := by
  unfold fourCodegreeHyperedges FourCodegreeTriangle
  simp_rw [discreteThings2024_codegree_four]
  decide +kernel

theorem thirteen_fourCodegree_count : (fourCodegreeHyperedges thirteenGraph).card = 3 := by
  rw [thirteen_fourCodegreeHyperedges]
  decide

theorem discreteThings2024_fourCodegree_count :
    (fourCodegreeHyperedges discreteThings2024Graph).card = 2 := by
  rw [discreteThings2024_fourCodegreeHyperedges]
  decide

/-- No permutation of the nine vertices carries the paper's table to the 2024 list. -/
theorem thirteen_not_isomorphic_discreteThings2024 :
    ¬ ∃ f : Equiv.Perm (Fin 9),
      relabelHypergraph f thirteenGraph = discreteThings2024Graph := by
  rintro ⟨f,hf⟩
  have h := fourCodegreeHyperedges_card_relabel f thirteenGraph
  rw [hf, discreteThings2024_fourCodegree_count, thirteen_fourCodegree_count] at h
  omega

theorem algebraic_fourCodegree_count : (fourCodegreeHyperedges algebraicGraph).card = 3 := by
  rw [← thirteen_relabel_eq_algebraicGraph, fourCodegreeHyperedges_card_relabel]
  exact thirteen_fourCodegree_count

/-- The same distinction for the actual four-sum-class graph on the affine plane. -/
theorem algebraic_not_isomorphic_discreteThings2024 :
    ¬ ∃ f : AffinePlane ≃ Fin 9,
      relabelHypergraph f algebraicGraph = discreteThings2024Graph := by
  rintro ⟨f,hf⟩
  have h := fourCodegreeHyperedges_card_relabel f algebraicGraph
  rw [hf, discreteThings2024_fourCodegree_count, algebraic_fourCodegree_count] at h
  omega

end RigidGHZ.Finite
