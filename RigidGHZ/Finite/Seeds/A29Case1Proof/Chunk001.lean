module

public import RigidGHZ.Finite.Seeds.A29Case1Proof.Chunk000

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A29Case1.core.cnf")
  (include_str "../../ExactCoverCertificates/A29Case1.core.lrat") 1000 1746
end RigidGHZ.Finite.Seeds.A29.Case1
