module

public import RigidGHZ.Finite.LRAT4a.Chunk019

/-! Kernel reconstruction of learned clauses 10000 through 10026. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4a (include_str "../Certificates/core4a.cnf")
  (include_str "../Certificates/core4a.lrat") 10000 10027
end RigidGHZ.Finite
