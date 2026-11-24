module

public import RigidGHZ.Finite.LRAT5b.Chunk015

/-! Kernel reconstruction of learned clauses 8000 through 8499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 8000 8500
end RigidGHZ.Finite
