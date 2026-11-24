module

public import RigidGHZ.Finite.LRAT4b.Chunk023

/-! Kernel reconstruction of learned clauses 12000 through 12499. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4b (include_str "../Certificates/core4b.cnf")
  (include_str "../Certificates/core4b.lrat") 12000 12500
end RigidGHZ.Finite
