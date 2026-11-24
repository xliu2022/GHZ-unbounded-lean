module

public import RigidGHZ.Finite.LRAT5a.Chunk016

/-! Kernel reconstruction of learned clauses 8500 through 8999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5a (include_str "../Certificates/core5a.cnf")
  (include_str "../Certificates/core5a.lrat") 8500 9000
end RigidGHZ.Finite
