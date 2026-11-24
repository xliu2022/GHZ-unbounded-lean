module

public import RigidGHZ.Finite.Seeds.A11Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A11.core.cnf")
  (include_str "../../ExactCoverCertificates/A11.core.lrat") 0 121
end RigidGHZ.Finite.Seeds.A11
