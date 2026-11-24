module
public import RigidGHZ.Finite.NineCoverComplete
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem nineCover_correct (e : Fin 84) (i : Fin 280) :
    nineEdge e ∈ ninePartition i ↔ i ∈ nineCoverIndices e := by
  rw [ninePartitionCode_mem]
  constructor
  · intro h
    rcases h with h | h | h
    · rw [h]; exact (nineCover_complete i).1
    · rw [h]; exact (nineCover_complete i).2.1
    · rw [h]; exact (nineCover_complete i).2.2
  · exact nineCover_sound e i

end RigidGHZ.Finite
