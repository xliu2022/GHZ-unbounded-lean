module

public import RigidGHZ.Finite.SatLRATChunk

/-! The CNF context for the independently checked LRAT chunks. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context nineUnsat7 (include_str "../Certificates/core7.cnf")
end RigidGHZ.Finite
