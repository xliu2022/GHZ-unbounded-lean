module

public import RigidGHZ.Finite.LRAT5a.Chunk028

/-! Kernel reconstruction of learned clauses 14500 through 14542. -/
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk nineUnsat5a (include_str "../Certificates/core5a.cnf")
  (include_str "../Certificates/core5a.lrat") 14500 14543
end RigidGHZ.Finite
