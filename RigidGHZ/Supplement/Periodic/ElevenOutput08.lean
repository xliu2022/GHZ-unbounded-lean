module

public import RigidGHZ.Supplement.Periodic.ElevenOutput07
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_081 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 0} 451 4 = [{7, 2, 0}] := by decide

theorem output_086 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {1, 0} 59 4 = [{1, 0}, {32, 1, 0}, {19, 1, 0}, {17, 1, 0}] := by decide

theorem output_090 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1, 0} 507 4 = [{2, 1, 0}, {32, 2, 1, 0}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
