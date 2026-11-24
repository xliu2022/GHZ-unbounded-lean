module

public import RigidGHZ.Supplement.Periodic.ElevenOutput01
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_027 : bits.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} 176 0 = [{30, 11}, {32, 30, 11}, {27, 11}, {29, 27, 11}, {21, 11}, {30, 19, 11}, {18, 11}, {29, 18, 11}, {19, 18, 11}, {30, 17, 11}, {18, 17, 11}, {30, 13, 11}, {21, 13, 11}, {18, 13, 11}, {12, 11}, {32, 12, 11}, {29, 12, 11}, {32, 29, 12, 11}, {19, 12, 11}, {17, 12, 11}, {13, 12, 11}] := by decide

theorem output_028 : bits.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} 322 0 = [{24, 10}, {32, 24, 10}, {15, 10}] := by decide

theorem output_029 : bits.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} 1 12 = [{31, 9}, {31, 26, 9}, {14, 9}, {26, 14, 9}, {14, 13, 9}, {26, 14, 13, 9}, {11, 9}, {29, 11, 9}, {19, 11, 9}, {17, 11, 9}, {13, 11, 9}, {11, 10, 9}] := by decide

theorem output_030 : bits.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} 200 0 = [{24, 8}, {32, 24, 8}, {28, 21, 8}, {24, 19, 8}, {24, 17, 8}, {15, 8}, {19, 15, 8}, {17, 15, 8}, {31, 9, 8}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
