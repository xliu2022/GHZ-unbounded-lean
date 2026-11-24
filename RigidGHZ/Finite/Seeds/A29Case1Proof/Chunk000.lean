module

public import RigidGHZ.Finite.Seeds.A29Case1Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case1.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case1.core.lrat") 0 1000
end RigidGHZ.Finite.Seeds.A29.Case1
