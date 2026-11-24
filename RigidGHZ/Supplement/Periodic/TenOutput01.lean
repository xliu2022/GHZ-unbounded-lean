module

public import RigidGHZ.Supplement.Periodic.TenOutput00
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem output_016 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} 3 16 = [{2}, {19, 2}, {17, 2}, {16, 2}, {10, 2}, {19, 10, 2}, {16, 10, 2}, {6, 2}, {19, 6, 2}, {10, 6, 2}, {19, 10, 6, 2}] := by decide

theorem output_021 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} 2 9 = [{1}, {19, 1}, {18, 1}, {17, 1}, {16, 1}, {18, 16, 1}, {9, 1}, {19, 9, 1}, {16, 9, 1}, {7, 1}, {18, 7, 1}] := by decide

theorem output_022 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} 7 25 = [{5, 1}, {19, 5, 1}, {16, 5, 1}] := by decide

theorem output_028 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} 2 5 = [{0}, {19, 0}, {18, 0}, {17, 0}, {10, 0}, {19, 10, 0}, {9, 0}, {19, 9, 0}, {10, 9, 0}, {19, 10, 9, 0}, {8, 0}, {17, 8, 0}, {7, 0}, {18, 7, 0}, {10, 7, 0}] := by decide

end RigidGHZ.Supplement.Periodic.Ten
