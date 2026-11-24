module

public import RigidGHZ.Finite.Seeds.A29Case4Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case4.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case4.core.lrat") 0 67
end RigidGHZ.Finite.Seeds.A29.Case4
