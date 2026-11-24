module

public import RigidGHZ.Finite.LRAT4b.Chunk004

/-! Kernel reconstruction of learned clauses 2500 through 2999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4b (include_str "../Certificates/core4b.cnf")
  (include_str "../Certificates/core4b.lrat") 2500 3000
end RigidGHZ.Finite
