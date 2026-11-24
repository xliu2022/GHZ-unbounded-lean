module

public import RigidGHZ.Finite.Seeds.A29Case3Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case3.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case3.core.lrat") 0 80
end RigidGHZ.Finite.Seeds.A29.Case3
