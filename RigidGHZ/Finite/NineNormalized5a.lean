module

public import RigidGHZ.Finite.NineSATAssemble
public import RigidGHZ.Finite.NineSATCertificate5a

@[expose] public section
namespace RigidGHZ.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Refutation of the fully normalized finite case 5a. -/
theorem no_fourteen_normalized_5a (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 5)
    (hE0 : ({3,7,8} : Finset (Fin 9)) ∈ H) (hE1 : ({4,5,6} : Finset (Fin 9)) ∈ H) : False := by
  nine_sat_finish_edges nineUnsat5a (include_str "Certificates/core5a.json") H hU F hnorm hE0 hE1

end RigidGHZ.Finite
