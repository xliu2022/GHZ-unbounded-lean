module

public import RigidGHZ.Finite.LRAT5b.Chunk021

/-! Kernel reconstruction of learned clauses 11000 through 11499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 11000 11500
end RigidGHZ.Finite
