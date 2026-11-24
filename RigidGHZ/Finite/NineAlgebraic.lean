module

public import RigidGHZ.Finite.NineVertex
public import RigidGHZ.Relabel
public import Mathlib.Data.ZMod.Basic

/-! The algebraic meaning of the printed thirteen-matching table. The finite
identity below uses the exact path numbering `(x,y) ↦ 3*x+y` in the paper. -/

@[expose] public section

namespace RigidGHZ.Finite

abbrev AffinePlane := ZMod 3 × ZMod 3

/-- The inverse of the printed path numbering. -/
def planePoint (v : Fin 9) : AffinePlane :=
  ((v.val / 3 : ℕ), (v.val % 3 : ℕ))

theorem planePoint_bijective : Function.Bijective planePoint := by
  decide +kernel

noncomputable def planeEquiv : Fin 9 ≃ AffinePlane :=
  Equiv.ofBijective planePoint planePoint_bijective

/-- All triples in one vector-sum class. -/
def sumClass (σ : AffinePlane) : Hypergraph AffinePlane :=
  (Finset.univ.powersetCard 3).filter (fun e => ∑ v ∈ e, v = σ)

def allowedSums : Finset AffinePlane :=
  ({0, 1} : Finset (ZMod 3)).product {0, 1}

/-- The four vector-sum classes `{0,1}²`, as an ordinary simple hypergraph. -/
def algebraicGraph : Hypergraph AffinePlane :=
  (Finset.univ.powersetCard 3).filter (fun e => (∑ v ∈ e, v) ∈ allowedSums)

theorem algebraicGraph_eq_sumClass_union :
    algebraicGraph = allowedSums.biUnion sumClass := by
  ext e
  simp only [algebraicGraph, sumClass, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨_, h.2, h.1, rfl⟩
  · rintro ⟨σ, hσ, he, hs⟩
    exact ⟨he, hs ▸ hσ⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- A kernel-checked finite identity, rather than an assumed interpretation of
the table. -/
theorem thirteen_image_eq_algebraicGraph :
    thirteenGraph.image (fun e => e.image planePoint) = algebraicGraph := by
  decide +kernel

theorem thirteen_relabel_eq_algebraicGraph :
    relabelHypergraph planeEquiv thirteenGraph = algebraicGraph := by
  change thirteenGraph.image (fun e => e.map planeEquiv.toEmbedding) = algebraicGraph
  simpa only [Finset.map_eq_image, planeEquiv, Equiv.coe_toEmbedding, Equiv.coe_ofBijective]
    using thirteen_image_eq_algebraicGraph

theorem algebraic_uniform : Uniform algebraicGraph 3 := by
  rw [← thirteen_relabel_eq_algebraicGraph]
  exact thirteen_uniform.relabel planeEquiv

theorem algebraic_rigid : IsRigid algebraicGraph 13 := by
  rw [← thirteen_relabel_eq_algebraicGraph]
  exact thirteen_rigid.relabel planeEquiv

theorem algebraic_card : algebraicGraph.card = 39 := by
  rw [← thirteen_relabel_eq_algebraicGraph]
  unfold relabelHypergraph
  rw [Finset.card_image_of_injective _ (relabelEdge_injective planeEquiv)]
  exact thirteen_card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sumClass_card (σ : AffinePlane) :
    (sumClass σ).card = if σ = 0 then 12 else 9 := by
  have h : ∀ σ : AffinePlane, (sumClass σ).card = if σ = 0 then 12 else 9 := by
    decide +kernel
  exact h σ

end RigidGHZ.Finite
