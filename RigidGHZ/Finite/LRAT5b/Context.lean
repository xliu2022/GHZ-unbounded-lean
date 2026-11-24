module

public import RigidGHZ.Finite.SatLRATPremises
public import RigidGHZ.Finite.NineSATCertificate5a

/-! The CNF context for the independently checked LRAT chunks. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context nineUnsat5b (include_str "../Certificates/core5b.cnf")
kernel_lrat_premises nineUnsat5b (include_str "../Certificates/core5b.cnf")
end RigidGHZ.Finite
