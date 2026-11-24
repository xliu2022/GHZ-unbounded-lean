module

public import RigidGHZ.Finite.LRAT5b.Chunk030

/-! Kernel reconstruction of learned clauses 15500 through 15878. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5b (include_str "../Certificates/core5b.cnf")
  (include_str "../Certificates/core5b.lrat") 15500 15879
end RigidGHZ.Finite
