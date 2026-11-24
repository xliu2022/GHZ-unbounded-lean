module

public import RigidGHZ.Supplement.Periodic.ElevenData
public import RigidGHZ.Supplement.Periodic.BitEnumerationFrom

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

def localMasks : Fin 33 → ℕ := ![3, 56, 448, 3, 292, 80, 259, 52, 200, 1, 322, 176, 65, 10, 400, 17, 134, 256, 65, 256, 144, 257, 130, 80, 17, 138, 100, 65, 18, 264, 65, 274, 4]
def outMasks : Fin 33 → ℕ := ![4, 0, 0, 128, 0, 8, 0, 0, 0, 12, 0, 0, 4, 32, 0, 8, 0, 96, 8, 34, 4, 8, 32, 4, 256, 0, 0, 32, 4, 128, 128, 0, 40]

def bits : BitScheme scheme where
  label := ⟨Fin.val, Fin.val_injective⟩
  localMask := localMasks
  outMask := outMasks
  full := 511
  allowed := 494
  local_correct := by decide
  out_correct := by decide
  full_correct := by decide
  allowed_correct := by decide

end RigidGHZ.Supplement.Periodic.Eleven
