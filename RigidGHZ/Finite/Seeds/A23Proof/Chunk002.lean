module

public import RigidGHZ.Finite.Seeds.A23Proof.Chunk001

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A23
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A23.core.cnf")
  (include_str "../../ExactCoverCertificates/A23.core.lrat") 2000 3000
end RigidGHZ.Finite.Seeds.A23
