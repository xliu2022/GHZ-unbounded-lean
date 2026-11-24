module

public import RigidGHZ.Supplement.Periodic.LatinData
public import RigidGHZ.Supplement.Periodic.BitEnumeration

/-! Verified integer encodings of the actual Latin local and outgoing sets. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

def localMasks : Fin 8 → Fin 8 → ℕ :=
  ![
    ![8388609, 66049, 263169, 1048577, 135169, 532481, 2113537, 4227073],
    ![65538, 8389122, 524290, 264194, 4098, 139266, 4210690, 2129922],
    ![4194308, 2097668, 1028, 131076, 528388, 73732, 278532, 8421380],
    ![2097160, 4194824, 131080, 524296, 69640, 1056776, 8405000, 294920],
    ![524560, 131600, 2097168, 4194320, 8392720, 270352, 81936, 1081360],
    ![131104, 544, 4194336, 2097184, 266272, 8396832, 540704, 98336],
    ![1048896, 262720, 8389696, 67648, 2101312, 4202560, 147520, 557120],
    ![262272, 524928, 66688, 8390784, 4198528, 2105472, 16512, 163968]]

def outMasks : Fin 8 → Fin 8 → ℕ :=
  ![
    ![256, 0, 0, 2048, 0, 0, 0, 0],
    ![256, 0, 1024, 0, 1048576, 0, 0, 0],
    ![256, 0, 1048576, 2048, 0, 0, 0, 0],
    ![256, 0, 1024, 2048, 0, 0, 0, 0],
    ![0, 0, 1024, 2048, 0, 0, 0, 0],
    ![256, 1048576, 1024, 2048, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![256, 0, 0, 0, 0, 0, 1048576, 0]]

def row (e : Fin 64) : Fin 8 := ⟨e.val / 8, by omega⟩
def col (e : Fin 64) : Fin 8 := ⟨e.val % 8, by omega⟩

def bits : BitScheme scheme where
  label := ⟨Fin.val, Fin.val_injective⟩
  localMask := fun e => localMasks (row e) (col e)
  outMask := fun e => outMasks (row e) (col e)
  full := 16777215
  allowed := 1051904
  local_correct := by intro e; fin_cases e <;> decide
  out_correct := by intro e; fin_cases e <;> decide
  full_correct := by decide
  allowed_correct := by decide

end RigidGHZ.Supplement.Periodic.Latin
