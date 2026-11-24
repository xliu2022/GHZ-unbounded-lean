module

public import RigidGHZ.Finite.Seeds.U12Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/U12.core.cnf")
  (include_str "../../ExactCoverCertificates/U12.core.lrat") 0 188
end RigidGHZ.Finite.Seeds.U12
