module

public import RigidGHZ.Finite.LRAT5b.Chunk016

/-! Kernel reconstruction of learned clauses 8500 through 8999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 8500 9000
end RigidGHZ.Finite
