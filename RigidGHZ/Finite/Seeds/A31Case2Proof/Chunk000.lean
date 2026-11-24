module

public import RigidGHZ.Finite.Seeds.A31Case2Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A31Case2.core.cnf")
  (include_str "../../ExactCoverCertificates/A31Case2.core.lrat") 0 179
end RigidGHZ.Finite.Seeds.A31.Case2
