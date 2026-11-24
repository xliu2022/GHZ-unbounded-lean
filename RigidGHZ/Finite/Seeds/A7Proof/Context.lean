module

public import RigidGHZ.Finite.SatLRATPremises

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A7
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/A7.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/A7.core.cnf")
end RigidGHZ.Finite.Seeds.A7
