module

public import RigidGHZ.Finite.LRAT6a.Chunk000

/-! Kernel reconstruction of learned clauses 500 through 852. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat6a (include_str "../Certificates/core6a.cnf")
  (include_str "../Certificates/core6a.lrat") 500 853
end RigidGHZ.Finite
