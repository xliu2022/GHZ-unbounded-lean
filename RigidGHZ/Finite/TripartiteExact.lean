module

public import RigidGHZ.Relabel
public import RigidGHZ.Finite.TripartiteUpper
public import RigidGHZ.Finite.TripartiteSix

@[expose] public section
namespace RigidGHZ.Finite

/-- The upper bound is independent of the vertex labels and the choice of the
three balanced parts. -/
theorem balanced_tripartite_three_upper {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {d : ℕ}
    (hP : BalancedPartite H 3 3) (hR : IsRigid H d) : d ≤ 6 := by
  obtain ⟨K, hKR, htrans⟩ := hR.canonical hP
  exact tripartite_three_upper htrans hKR

/-- The exact numerical extremal statement `g₃(3)=6` in standard hypergraph
language. The classification of equality examples is a separate claim. -/
theorem tripartite_three_exact :
    (∃ H : Hypergraph (Fin 9), Uniform H 3 ∧ BalancedPartite H 3 3 ∧ IsRigid H 6) ∧
    (∀ (H : Hypergraph (Fin 9)) (d : ℕ), BalancedPartite H 3 3 → IsRigid H d → d ≤ 6) :=
  ⟨six_witness, fun _ _ => balanced_tripartite_three_upper⟩

end RigidGHZ.Finite
