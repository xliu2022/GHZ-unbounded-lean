module

public import RigidGHZ.Finite.LRAT7.Chunk002

/-! Kernel reconstruction of learned clauses 1500 through 1646. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat7 (include_str "../Certificates/core7.cnf")
  (include_str "../Certificates/core7.lrat") 1500 1647
end RigidGHZ.Finite
