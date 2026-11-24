module

public import RigidGHZ.Finite.Seeds.A19Proof.Chunk002

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A19
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/A19.core.cnf")
  (include_str "../../ExactCoverCertificates/A19.core.lrat") 3000 3833
end RigidGHZ.Finite.Seeds.A19
