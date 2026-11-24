module

public import RigidGHZ.Finite.LRAT4b.Chunk030

/-! Kernel reconstruction of learned clauses 15500 through 15999. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat4b (include_str "../Certificates/core4b.cnf")
  (include_str "../Certificates/core4b.lrat") 15500 16000
end RigidGHZ.Finite
