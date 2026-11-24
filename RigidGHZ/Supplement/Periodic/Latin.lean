module

public import RigidGHZ.Supplement.Periodic.LatinCheck18

/-! The eight prescribed transversal lifts are all perfect matchings at every
positive odd period. The resulting ordinary hypergraph is linear and balanced. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Latin

theorem finite_certificate :
    (scheme.enumerateGroups groups ∅).all (fun A => decide (Certificate A)) = true :=
  row_node_299

theorem certificate {A : Finset (Fin 64)} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_group_enumeration groups groups_pairwise groups_cover
    (fun B hB => groups_unique hB) Certificate finite_certificate hA

noncomputable def rigidFamily {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin 8) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.odd_configurations_complete hq hodd color height x y (by decide)
      class_inputs_injective (fun A hA he => by
        obtain ⟨i, hi⟩ := (certificate hA).2.2.1 he
        exact ⟨i, hi.trans (classes_eq i).symm⟩) class_inputs_avoid
      (fun A hA => (certificate hA).1) (fun A hA => (certificate hA).2.1))

theorem uniform (q : ℕ) : Uniform (scheme.graph (finRotate q)) 3 :=
  scheme.graph_uniform (finRotate q) (by decide)

theorem edge_count (q : ℕ) : (scheme.graph (finRotate q)).card = 64 * q := by
  simpa using scheme.graph_card (finRotate q)

theorem balanced (q : ℕ) : BalancedPartite (scheme.graph (finRotate q)) 3 (8 * q) := by
  simpa using scheme.graph_balanced (finRotate q) part part_size edge_part

theorem linear (q : ℕ) : IsLinear (scheme.graph (finRotate q)) :=
  scheme.graph_linear (finRotate q) base_linear

end RigidGHZ.Supplement.Periodic.Latin
