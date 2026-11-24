module

public import RigidGHZ.Supplement.Periodic.ElevenOutput04
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_044 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4, 3} 295 128 = [{23, 4, 3}, {20, 4, 3}] := by decide

theorem output_045 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4, 3} 375 136 = [{5, 4, 3}] := by decide

theorem output_049 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2} 448 0 = [{24, 2}, {32, 24, 2}, {15, 2}, {24, 13, 2}, {15, 13, 2}, {9, 7, 2}, {13, 9, 7, 2}] := by decide

theorem output_052 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2} 451 128 = [{7, 3, 2}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
