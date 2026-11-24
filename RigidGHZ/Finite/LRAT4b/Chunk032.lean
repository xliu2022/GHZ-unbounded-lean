module

public import RigidGHZ.Finite.LRAT4b.Chunk031

/-! Kernel reconstruction of learned clauses 16000 through 16122. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4b (include_str "../Certificates/core4b.cnf")
  (include_str "../Certificates/core4b.lrat") 16000 16123
end RigidGHZ.Finite
