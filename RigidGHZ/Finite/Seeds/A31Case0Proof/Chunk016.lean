module

public import RigidGHZ.Finite.Seeds.A31Case0Proof.Chunk015

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A31Case0.core.cnf")
  (include_str "../../ExactCoverCertificates/A31Case0.core.lrat") 16000 17000
end RigidGHZ.Finite.Seeds.A31.Case0
