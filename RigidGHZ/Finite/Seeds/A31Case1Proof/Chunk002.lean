module

public import RigidGHZ.Finite.Seeds.A31Case1Proof.Chunk001

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A31Case1.core.cnf")
  (include_str "../../ExactCoverCertificates/A31Case1.core.lrat") 2000 2166
end RigidGHZ.Finite.Seeds.A31.Case1
