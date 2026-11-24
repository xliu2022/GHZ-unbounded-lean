module

public import RigidGHZ.Finite.Seeds.A31Case5Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A31Case5.core.cnf")
  (include_str "../../ExactCoverCertificates/A31Case5.core.lrat") 0 79
end RigidGHZ.Finite.Seeds.A31.Case5
