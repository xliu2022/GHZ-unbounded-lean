module

public import RigidGHZ.Finite.Seeds.A17Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A17
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A17.core.cnf")
  (include_str "../../ExactCoverCertificates/A17.core.lrat") 0 600
end RigidGHZ.Finite.Seeds.A17
