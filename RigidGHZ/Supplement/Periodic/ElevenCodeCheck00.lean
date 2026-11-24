module

public import RigidGHZ.Supplement.Periodic.ElevenCodeData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem pair_code_chunk00 :
    configurationChunk00.map (fun A => finitePairCode (scheme.input A, scheme.output A)) =
      pairCodeChunk00 := by decide

end RigidGHZ.Supplement.Periodic.Eleven
