module

public import RigidGHZ.Finite.LRAT5a.Chunk013

/-! Kernel reconstruction of learned clauses 7000 through 7499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5a (include_str "../Certificates/core5a.cnf")
  (include_str "../Certificates/core5a.lrat") 7000 7500
end RigidGHZ.Finite
