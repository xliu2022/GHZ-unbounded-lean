module

public import RigidGHZ.Supplement.Periodic.ElevenOutput06
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_073 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} 3 4 = [{14, 0}, {32, 14, 0}, {26, 14, 0}, {11, 0}, {32, 11, 0}, {29, 11, 0}, {32, 29, 11, 0}, {19, 11, 0}, {17, 11, 0}, {7, 0}, {29, 7, 0}, {19, 7, 0}, {17, 7, 0}, {8, 7, 0}, {19, 8, 7, 0}, {17, 8, 7, 0}] := by decide

theorem output_074 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 0} 83 12 = [{5, 0}, {29, 5, 0}, {19, 5, 0}, {17, 5, 0}] := by decide

theorem output_076 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4, 0} 295 4 = [] := by decide

theorem output_077 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4, 0} 375 12 = [{5, 4, 0}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
