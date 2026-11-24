module

public import RigidGHZ.Finite.NineConflict
public import RigidGHZ.Finite.NineIncident
public import RigidGHZ.Finite.NineFan

@[expose] public section
namespace RigidGHZ.Finite

 theorem nine_initial_pair_edge (j : Fin 7) :
    nineEdge ⟨j.val, by omega⟩ = {0,1,(⟨j.val + 2, by omega⟩ : Fin 9)} := by
  have hc : (List.finRange 7).all (fun j => decide
    (nineEdge ⟨j.val, by omega⟩ = {0,1,(⟨j.val + 2, by omega⟩ : Fin 9)})) = true := by decide +kernel
  have h : ∀ j : Fin 7, nineEdge ⟨j.val, by omega⟩ =
      {0,1,(⟨j.val + 2, by omega⟩ : Fin 9)} := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using hc
  exact h j

end RigidGHZ.Finite
