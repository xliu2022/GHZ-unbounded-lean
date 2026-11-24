module

public import RigidGHZ.Finite.Seeds.A41Case0Proof.Chunk008
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A41.Case0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod 41))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex 0) ∈ M)
    (hlower : ∀ i : Fin 205, i.val < 0 * 41 → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/A41Case0.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.A41.Case0
