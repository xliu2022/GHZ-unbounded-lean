module

public import RigidGHZ.Finite.Seeds.A37Proof.Chunk005
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A37
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/A37.chunk006.lrat")
end RigidGHZ.Finite.Seeds.A37
