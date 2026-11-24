module

public import RigidGHZ.Finite.NineSATAssemble
public import RigidGHZ.Finite.NineSATCertificate4b

@[expose] public section
namespace RigidGHZ.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Refutation of the fully normalized finite case 4b. -/
theorem no_fourteen_normalized_4b (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 4)
    (hmax : ∀ a b : Fin 9, a ≠ b → (pairCompletions H a b).card ≤ 4)
    (hE0 : ({3,4,6} : Finset (Fin 9)) ∈ H) (hE1 : ({5,7,8} : Finset (Fin 9)) ∈ H) : False := by
  nine_sat_finish_max_edges nineUnsat4b (include_str "Certificates/core4b.json") H hU F hnorm hmax hE0 hE1

end RigidGHZ.Finite
