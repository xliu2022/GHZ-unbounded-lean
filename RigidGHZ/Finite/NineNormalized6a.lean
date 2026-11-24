module

public import RigidGHZ.Finite.NineSATAssemble
public import RigidGHZ.Finite.NineSATCertificate6a

@[expose] public section
namespace RigidGHZ.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Refutation of the fully normalized finite case 6a. -/
theorem no_fourteen_normalized_6a (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 6)
    (hE0 : ({3,4,8} : Finset (Fin 9)) ∈ H) (hE1 : ({5,6,7} : Finset (Fin 9)) ∈ H) : False := by
  nine_sat_finish_edges nineUnsat6a (include_str "Certificates/core6a.json") H hU F hnorm hE0 hE1

end RigidGHZ.Finite
