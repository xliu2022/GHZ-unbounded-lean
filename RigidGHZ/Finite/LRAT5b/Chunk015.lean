module

public import RigidGHZ.Finite.LRAT5b.Chunk014

/-! Kernel reconstruction of learned clauses 7500 through 7999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 7500 8000
end RigidGHZ.Finite
