module

public import RigidGHZ.Finite.Seeds.A47Case4Proof.Context
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47.Case4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/A47Case4.chunk000.lrat")
end RigidGHZ.Finite.Seeds.A47.Case4
