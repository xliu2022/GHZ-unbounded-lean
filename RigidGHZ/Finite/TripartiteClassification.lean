module

public import RigidGHZ.Finite.TripartiteUnique
public import RigidGHZ.Finite.TripartiteExact

@[expose] public section
namespace RigidGHZ.Finite

theorem finite_relabel_trans {V W U : Type*}
    [DecidableEq V] [DecidableEq W] [DecidableEq U]
    (f : V ≃ W) (g : W ≃ U) (H : Hypergraph V) :
    relabelHypergraph (f.trans g) H = relabelHypergraph g (relabelHypergraph f H) := by
  have he : ∀ e : Finset V,
      relabelEdge (f.trans g) e = relabelEdge g (relabelEdge f e) := by
    intro e
    ext u
    simp
  simp only [relabelHypergraph,Finset.image_image,Function.comp_def]
  congr 1
  funext e
  exact he e

/-- The extremal balanced tripartite hypergraph on an arbitrary finite vertex
set is isomorphic to the complement of the order-three addition table. -/
theorem balanced_tripartite_three_unique {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} (hP : BalancedPartite H 3 3) (hR : IsRigid H 6) :
    ∃ f : V ≃ (Fin 3 × Fin 3), relabelHypergraph f H = latinComplementGraph := by
  obtain ⟨f,htrans⟩ := hP.canonical
  obtain ⟨g,hg,hiso⟩ := tripartite_three_unique htrans (hR.relabel f)
  exact ⟨f.trans g,by rw [finite_relabel_trans,hiso]⟩

end RigidGHZ.Finite
