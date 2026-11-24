module

public import RigidGHZ.Finite.SatLRATChunk
public import RigidGHZ.Finite.NineSATCertificate7

/-! The CNF context for the independently checked LRAT chunks. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context nineUnsat4a (include_str "../Certificates/core4a.cnf")
end RigidGHZ.Finite
