module

public import RigidGHZ.Supplement.Periodic.ElevenOutput03
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_037 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} 292 0 = [{30, 28, 4}, {28, 27, 4}, {24, 4}, {25, 24, 4}, {24, 22, 4}, {30, 20, 4}, {27, 20, 4}, {28, 18, 4}, {20, 18, 4}, {15, 4}, {25, 15, 4}, {22, 15, 4}, {24, 13, 4}, {30, 20, 13, 4}, {20, 18, 13, 4}, {15, 13, 4}, {24, 8, 4}, {15, 8, 4}] := by decide

theorem output_038 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} 372 8 = [] := by decide

theorem output_041 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} 3 128 = [{23, 3}, {32, 23, 3}, {20, 3}, {32, 20, 3}, {26, 20, 3}, {23, 19, 3}, {20, 19, 3}, {26, 20, 19, 3}, {23, 17, 3}, {20, 17, 3}, {26, 20, 17, 3}, {14, 3}, {32, 14, 3}, {26, 14, 3}, {11, 3}, {32, 11, 3}, {19, 11, 3}, {17, 11, 3}, {7, 3}, {19, 7, 3}, {17, 7, 3}, {8, 7, 3}, {19, 8, 7, 3}, {17, 8, 7, 3}] := by decide

theorem output_042 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} 83 136 = [{5, 3}, {19, 5, 3}, {17, 5, 3}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
