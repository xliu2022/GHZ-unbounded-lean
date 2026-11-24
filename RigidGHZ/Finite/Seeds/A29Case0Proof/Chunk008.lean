module

public import RigidGHZ.Finite.Seeds.A29Case0Proof.Chunk007

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case0.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case0.core.lrat") 8000 9000
end RigidGHZ.Finite.Seeds.A29.Case0
