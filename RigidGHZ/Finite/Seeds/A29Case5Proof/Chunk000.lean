module

public import RigidGHZ.Finite.Seeds.A29Case5Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case5.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case5.core.lrat") 0 69
end RigidGHZ.Finite.Seeds.A29.Case5
