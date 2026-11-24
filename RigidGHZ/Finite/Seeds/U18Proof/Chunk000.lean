module

public import RigidGHZ.Finite.Seeds.U18Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U18
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/U18.core.cnf")
  (include_str "../../ExactCoverCertificates/U18.core.lrat") 0 749
end RigidGHZ.Finite.Seeds.U18
