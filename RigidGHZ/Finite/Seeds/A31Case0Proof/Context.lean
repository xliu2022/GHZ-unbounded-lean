module

public import RigidGHZ.Finite.SatLRATPremises
public import RigidGHZ.Finite.Seeds.A31Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31.Case0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/A31Case0.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/A31Case0.core.cnf")
end RigidGHZ.Finite.Seeds.A31.Case0
