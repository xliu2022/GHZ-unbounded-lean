module

public import RigidGHZ.Supplement.Periodic.LatinOutput11
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem output_057 : bits.enumerate [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {11, 7} 4491267 0 = [{57, 52, 45, 38, 26, 18, 11, 7}, {57, 54, 45, 34, 28, 18, 11, 7}, {61, 50, 41, 38, 26, 20, 11, 7}] := by decide

theorem output_058 : bits.enumerate [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 7} 4231171 1048576 = [] := by decide

theorem output_059 : bits.enumerate [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {13, 7} 4366339 0 = [{59, 48, 44, 38, 27, 17, 13, 7}, {59, 49, 46, 34, 28, 18, 13, 7}, {57, 51, 44, 34, 30, 18, 13, 7}, {56, 51, 41, 34, 30, 20, 13, 7}] := by decide

end RigidGHZ.Supplement.Periodic.Latin
