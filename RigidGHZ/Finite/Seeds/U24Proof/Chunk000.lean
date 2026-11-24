module

public import RigidGHZ.Finite.Seeds.U24Proof.Context

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U24
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/U24.core.cnf")
  (include_str "../../ExactCoverCertificates/U24.core.lrat") 0 907
end RigidGHZ.Finite.Seeds.U24
