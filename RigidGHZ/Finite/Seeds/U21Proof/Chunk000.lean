module

public import RigidGHZ.Finite.Seeds.U21Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U21
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/U21.core.cnf")
  (include_str "../../ExactCoverCertificates/U21.core.lrat") 0 533
end RigidGHZ.Finite.Seeds.U21
