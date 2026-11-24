module

public import RigidGHZ.Supplement.Periodic.ElevenOutput05
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_057 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {1} 56 0 = [{30, 1}, {32, 30, 1}, {27, 1}, {30, 22, 1}, {21, 1}, {22, 21, 1}, {30, 19, 1}, {18, 1}, {22, 18, 1}, {19, 18, 1}, {30, 17, 1}, {18, 17, 1}, {30, 16, 1}, {27, 16, 1}, {21, 16, 1}, {30, 19, 16, 1}, {18, 16, 1}, {19, 18, 16, 1}, {30, 17, 16, 1}, {18, 17, 16, 1}, {12, 1}, {32, 12, 1}, {22, 12, 1}, {19, 12, 1}, {17, 12, 1}, {16, 12, 1}, {19, 16, 12, 1}, {17, 16, 12, 1}, {9, 1}, {22, 9, 1}, {19, 9, 1}, {17, 9, 1}, {16, 9, 1}, {19, 16, 9, 1}, {17, 16, 9, 1}, {10, 9, 1}, {6, 1}, {32, 6, 1}] := by decide

theorem output_060 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} 59 128 = [{3, 1}, {32, 3, 1}, {19, 3, 1}, {17, 3, 1}] := by decide

theorem output_064 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} 504 0 = [{9, 2, 1}] := by decide

theorem output_067 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} 507 128 = [{3, 2, 1}, {32, 3, 2, 1}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
