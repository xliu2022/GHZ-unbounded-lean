module

public import RigidGHZ.Finite.Seeds.A41Case4Proof.Context
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A41.Case4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/A41Case4.chunk000.lrat")
end RigidGHZ.Finite.Seeds.A41.Case4
