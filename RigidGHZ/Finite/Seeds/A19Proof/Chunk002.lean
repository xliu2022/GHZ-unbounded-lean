module

public import RigidGHZ.Finite.Seeds.A19Proof.Chunk001

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A19
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A19.core.cnf")
  (include_str "../../ExactCoverCertificates/A19.core.lrat") 2000 3000
end RigidGHZ.Finite.Seeds.A19
