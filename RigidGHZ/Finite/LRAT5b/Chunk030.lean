module

public import RigidGHZ.Finite.LRAT5b.Chunk029

/-! Kernel reconstruction of learned clauses 15000 through 15499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 15000 15500
end RigidGHZ.Finite
