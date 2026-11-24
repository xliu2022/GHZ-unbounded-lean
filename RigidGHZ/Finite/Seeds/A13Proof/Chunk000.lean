module

public import RigidGHZ.Finite.Seeds.A13Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A13
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A13.core.cnf")
  (include_str "../../ExactCoverCertificates/A13.core.lrat") 0 786
end RigidGHZ.Finite.Seeds.A13
