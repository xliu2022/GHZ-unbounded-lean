module

public import RigidGHZ.Finite.Seeds.A29Case5Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod 29))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex 5) ∈ M)
    (hlower : ∀ i : Fin 174, i.val < 5 * 29 → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/A29Case5.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.A29.Case5
