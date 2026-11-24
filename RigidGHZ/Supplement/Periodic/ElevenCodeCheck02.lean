module

public import RigidGHZ.Supplement.Periodic.ElevenCodeCheck01

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem pair_code_chunk02 :
    configurationChunk02.map (fun A => finitePairCode (scheme.input A, scheme.output A)) =
      pairCodeChunk02 := by decide

end RigidGHZ.Supplement.Periodic.Eleven
