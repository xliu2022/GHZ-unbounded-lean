module

public import RigidGHZ.Supplement.Periodic.TenData
public import RigidGHZ.Supplement.Periodic.BitEnumerationFrom

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

def localMasks : Fin 20 → ℕ := ![2, 2, 3, 35, 1, 5, 32, 25, 1, 33, 4, 22, 2, 26, 2, 34, 24, 44, 4, 24]
def outMasks : Fin 20 → ℕ := ![5, 9, 16, 0, 12, 16, 5, 0, 40, 16, 10, 0, 36, 0, 40, 16, 4, 0, 48, 32]

def bits : BitScheme scheme where
  label := ⟨Fin.val, Fin.val_injective⟩
  localMask := localMasks
  outMask := outMasks
  full := 63
  allowed := 63
  local_correct := by decide
  out_correct := by decide
  full_correct := by decide
  allowed_correct := by decide

end RigidGHZ.Supplement.Periodic.Ten
