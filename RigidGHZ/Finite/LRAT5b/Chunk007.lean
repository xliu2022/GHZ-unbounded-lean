module

public import RigidGHZ.Finite.LRAT5b.Chunk006

/-! Kernel reconstruction of learned clauses 3500 through 3999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 3500 4000
end RigidGHZ.Finite
