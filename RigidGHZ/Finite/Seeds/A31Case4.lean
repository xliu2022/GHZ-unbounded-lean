module

public import RigidGHZ.Finite.Seeds.A31Case4Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod 31))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex 4) ∈ M)
    (hlower : ∀ i : Fin 186, i.val < 4 * 31 → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/A31Case4.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.A31.Case4
