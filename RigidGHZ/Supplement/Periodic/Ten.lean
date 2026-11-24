module

public import RigidGHZ.Supplement.Periodic.TenCheck04

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Ten

theorem finite_certificate :
    (scheme.enumerateFrom (List.finRange 20) ∅).all (fun A => decide (Certificate A)) = true := by
  exact node_139

theorem certificate {A : Finset (Fin 20)} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_enumeration (List.finRange 20) (List.nodup_finRange _) (by simp)
    Certificate finite_certificate hA

noncomputable def rigidFamily {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin 10) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.odd_configurations_complete hq hodd color height ∅ Finset.univ (by decide)
      class_inputs_injective (fun A hA => (certificate hA).2.2.1) class_inputs_avoid
      (fun A hA => (certificate hA).1) (fun A hA => (certificate hA).2.1))

theorem uniform (q : ℕ) : Uniform (scheme.graph (finRotate q)) 3 :=
  scheme.graph_uniform (finRotate q) (by decide)

theorem edge_count (q : ℕ) : (scheme.graph (finRotate q)).card = 20 * q := by
  simpa using scheme.graph_card (finRotate q)

end RigidGHZ.Supplement.Periodic.Ten
