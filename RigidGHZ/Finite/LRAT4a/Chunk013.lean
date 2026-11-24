module

public import RigidGHZ.Finite.LRAT4a.Chunk012

/-! Kernel reconstruction of learned clauses 6500 through 6999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4a (include_str "../Certificates/core4a.cnf")
  (include_str "../Certificates/core4a.lrat") 6500 7000
end RigidGHZ.Finite
