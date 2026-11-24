module

public import RigidGHZ.Finite.NineSATAssemble
public import RigidGHZ.Finite.NineSATCertificate7

@[expose] public section
namespace RigidGHZ.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The normalized codegree-7 instance has no ordinary 14-rigid realization. -/
theorem no_fourteen_normalized_7 (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 7) : False := by
  nine_sat_finish nineUnsat7 (include_str "Certificates/core7.json") H hU F hnorm

end RigidGHZ.Finite
