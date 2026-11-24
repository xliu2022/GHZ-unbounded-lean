module

public import RigidGHZ.Finite.LRAT5b.Chunk011

/-! Kernel reconstruction of learned clauses 6000 through 6499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 6000 6500
end RigidGHZ.Finite
