module

public import RigidGHZ.Finite.LRAT5a.Chunk004

/-! Kernel reconstruction of learned clauses 2500 through 2999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5a (include_str "../Certificates/core5a.cnf")
  (include_str "../Certificates/core5a.lrat") 2500 3000
end RigidGHZ.Finite
