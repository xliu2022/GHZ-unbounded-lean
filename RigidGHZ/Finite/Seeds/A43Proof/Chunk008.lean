module

public import RigidGHZ.Finite.Seeds.A43Proof.Chunk007
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A43
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/A43.chunk008.lrat")
end RigidGHZ.Finite.Seeds.A43
