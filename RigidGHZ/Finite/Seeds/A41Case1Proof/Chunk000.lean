module

public import RigidGHZ.Finite.Seeds.A41Case1Proof.Context
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A41.Case1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/A41Case1.chunk000.lrat")
end RigidGHZ.Finite.Seeds.A41.Case1
