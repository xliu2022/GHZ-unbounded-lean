module

public import RigidGHZ.Finite.Seeds.A47Case1Proof.Chunk001
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47.Case1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod 47))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex 1) ∈ M)
    (hlower : ∀ i : Fin 235, i.val < 1 * 47 → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/A47Case1.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.A47.Case1
