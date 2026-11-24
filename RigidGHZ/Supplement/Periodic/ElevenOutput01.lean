module

public import RigidGHZ.Supplement.Periodic.ElevenOutput00
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_023 : bits.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} 17 8 = [{15}, {29, 15}, {26, 15}, {29, 26, 15}, {25, 15}, {26, 25, 15}, {22, 15}, {29, 22, 15}, {26, 22, 15}, {29, 26, 22, 15}, {19, 15}, {26, 19, 15}, {25, 19, 15}, {26, 25, 19, 15}, {17, 15}, {26, 17, 15}, {25, 17, 15}, {26, 25, 17, 15}, {16, 15}, {29, 16, 15}, {19, 16, 15}, {17, 16, 15}] := by decide

theorem output_024 : bits.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} 400 0 = [{30, 14}, {32, 30, 14}, {27, 14}, {18, 14}] := by decide

theorem output_025 : bits.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} 10 32 = [{24, 13}, {26, 24, 13}, {23, 21, 13}, {30, 20, 13}, {21, 20, 13}, {26, 21, 20, 13}, {20, 18, 13}, {15, 13}, {26, 15, 13}, {30, 14, 13}, {18, 14, 13}] := by decide

theorem output_026 : bits.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} 65 4 = [{31, 12}, {32, 31, 12}, {14, 12}, {32, 14, 12}, {14, 13, 12}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
