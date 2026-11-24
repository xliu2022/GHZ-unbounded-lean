module

public import RigidGHZ.Supplement.UnrestrictedThresholdAssembly
public import RigidGHZ.Finite.SixVertex
public import RigidGHZ.Finite.NineVertex
public import RigidGHZ.Finite.Seeds.U12
public import RigidGHZ.Finite.Seeds.U15
public import RigidGHZ.Finite.Seeds.U18
public import RigidGHZ.Finite.Seeds.U21
public import RigidGHZ.Finite.Seeds.U24

/-! Actual unrestricted finite witnesses used in the grafting thresholds. -/

@[expose] public section

namespace RigidGHZ.Supplement.FreeSeeds

open ThresholdAssembly

theorem at2_10 : FreeSeed 2 10 :=
  BoundedUnrestricted.of_witness Finite.ten_uniform Finite.ten_rigid

theorem at3_13 : FreeSeed 3 13 :=
  BoundedUnrestricted.of_witness Finite.thirteen_uniform Finite.thirteen_rigid

theorem at3_12 : FreeSeed 3 12 := at3_13.restrict (by decide) (by decide) (by decide)
theorem at3_10 : FreeSeed 3 10 := at3_13.restrict (by decide) (by decide) (by decide)

theorem at4_12 : FreeSeed 4 12 :=
  BoundedUnrestricted.of_witness Finite.Seeds.U12.uniform Finite.Seeds.U12.rigid

theorem at4_10 : FreeSeed 4 10 := at4_12.restrict (by decide) (by decide) (by decide)

theorem at5_10 : FreeSeed 5 10 :=
  BoundedUnrestricted.of_witness Finite.Seeds.U15.uniform Finite.Seeds.U15.rigid

theorem at6_13 : FreeSeed 6 13 :=
  BoundedUnrestricted.of_witness Finite.Seeds.U18.uniform Finite.Seeds.U18.rigid

theorem at6_12 : FreeSeed 6 12 := at6_13.restrict (by decide) (by decide) (by decide)
theorem at6_10 : FreeSeed 6 10 := at6_13.restrict (by decide) (by decide) (by decide)

theorem at7_10 : FreeSeed 7 10 :=
  BoundedUnrestricted.of_witness Finite.Seeds.U21.uniform Finite.Seeds.U21.rigid

theorem at8_10 : FreeSeed 8 10 :=
  BoundedUnrestricted.of_witness Finite.Seeds.U24.uniform Finite.Seeds.U24.rigid

end RigidGHZ.Supplement.FreeSeeds
