module

public import RigidGHZ.Finite.LRAT7.Context

/-! Kernel reconstruction of learned clauses 0 through 499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat7 (include_str "../Certificates/core7.cnf")
  (include_str "../Certificates/core7.lrat") 0 500
end RigidGHZ.Finite
