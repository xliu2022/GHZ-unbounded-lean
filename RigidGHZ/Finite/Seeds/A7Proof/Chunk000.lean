module

public import RigidGHZ.Finite.Seeds.A7Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A7
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A7.core.cnf")
  (include_str "../../ExactCoverCertificates/A7.core.lrat") 0 30
end RigidGHZ.Finite.Seeds.A7
