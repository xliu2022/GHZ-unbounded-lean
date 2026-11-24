module

public import RigidGHZ.Finite.LRAT4b.Chunk017

/-! Kernel reconstruction of learned clauses 9000 through 9499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4b (include_str "../Certificates/core4b.cnf")
  (include_str "../Certificates/core4b.lrat") 9000 9500
end RigidGHZ.Finite
