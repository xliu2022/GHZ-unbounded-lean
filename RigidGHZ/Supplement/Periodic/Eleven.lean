module

public import RigidGHZ.Supplement.Periodic.ElevenCheck19

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem finite_certificate :
    (scheme.enumerateFrom (List.finRange 33) ∅).all (fun A => decide (Certificate A)) = true := by
  exact node_639

theorem certificate {A : Finset (Fin 33)} (hA : scheme.LocalConfig A) : Certificate A :=
  scheme.property_of_enumeration (List.finRange 33) (List.nodup_finRange _) (by simp)
    Certificate finite_certificate hA

noncomputable def rigidFamily {q : ℕ} (hq : 0 < q) :
    RigidFamily (scheme.graph (finRotate q)) (Fin 11) :=
  scheme.rigidFamily_of_configurations (finRotate q) color classes_local classes_loop
    (scheme.strict_configurations_complete hq color height class_inputs_injective
      (fun A hA => (certificate hA).2) (fun A hA => (certificate hA).1))

theorem uniform (q : ℕ) : Uniform (scheme.graph (finRotate q)) 3 :=
  scheme.graph_uniform (finRotate q) (by decide)

theorem edge_count (q : ℕ) : (scheme.graph (finRotate q)).card = 33 * q := by
  simpa using scheme.graph_card (finRotate q)

end RigidGHZ.Supplement.Periodic.Eleven
