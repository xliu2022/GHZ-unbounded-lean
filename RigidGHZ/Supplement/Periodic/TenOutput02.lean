module

public import RigidGHZ.Supplement.Periodic.TenOutput01
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem output_029 : bits.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} 7 21 = [{5, 0}, {19, 5, 0}] := by decide

end RigidGHZ.Supplement.Periodic.Ten
