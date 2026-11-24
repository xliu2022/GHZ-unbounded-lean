module

public import RigidGHZ.Finite.SatLRATPremises
public import RigidGHZ.Finite.Seeds.A29Case3

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29.Case4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/A29Case4.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/A29Case4.core.cnf")
end RigidGHZ.Finite.Seeds.A29.Case4
