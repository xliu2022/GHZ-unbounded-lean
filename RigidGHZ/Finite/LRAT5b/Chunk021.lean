module

public import RigidGHZ.Finite.LRAT5b.Chunk020

/-! Kernel reconstruction of learned clauses 10500 through 10999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 10500 11000
end RigidGHZ.Finite
