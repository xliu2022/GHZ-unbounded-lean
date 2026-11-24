module

public import RigidGHZ.Finite.SatLRATPremises

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U21
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/U21.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/U21.core.cnf")
end RigidGHZ.Finite.Seeds.U21
