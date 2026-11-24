module

public import RigidGHZ.Finite.Seeds.U15Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/U15.core.cnf")
  (include_str "../../ExactCoverCertificates/U15.core.lrat") 0 161
end RigidGHZ.Finite.Seeds.U15
