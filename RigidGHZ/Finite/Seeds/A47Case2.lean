module

public import RigidGHZ.Finite.Seeds.A47Case2Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47.Case2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod 47))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex 2) ∈ M)
    (hlower : ∀ i : Fin 235, i.val < 2 * 47 → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/A47Case2.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.A47.Case2
