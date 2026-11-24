module

public import RigidGHZ.Finite.LRAT6a.Context

/-! Kernel reconstruction of learned clauses 0 through 499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat6a (include_str "../Certificates/core6a.cnf")
  (include_str "../Certificates/core6a.lrat") 0 500
end RigidGHZ.Finite
