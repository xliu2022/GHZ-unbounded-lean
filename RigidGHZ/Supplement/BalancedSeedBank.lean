module

public import RigidGHZ.Supplement.AffineBounded
public import RigidGHZ.Supplement.AffineOddSizes
public import RigidGHZ.Supplement.BalancedThresholdAssembly
public import RigidGHZ.Finite.Seeds.A11Seed
public import RigidGHZ.Finite.Seeds.A13Seed
public import RigidGHZ.Finite.Seeds.A17Seed
public import RigidGHZ.Finite.Seeds.A19Seed
public import RigidGHZ.Finite.Seeds.A23Seed

/-! Actual affine seed witnesses for the non-linear threshold tables. -/

@[expose] public section

namespace RigidGHZ.Supplement.BalancedSeeds

open ThresholdAssembly

theorem at5_8 : PairSeed 5 8 := Affine.eight_at_five
theorem at7_8 : PairSeed 7 8 := Affine.eight_at_seven

theorem at10_8 : PairSeed 10 8 := by
  have h := Affine.seed5.bounded_cyclic (L := 2) (by decide) (by decide) (by decide)
    (by rw [Affine.shifts5_card]; decide)
  simpa only [Affine.shifts5_card] using h

theorem at11_10 : PairSeed 11 10 := by
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide
  simpa only [hc] using Finite.Seeds.A11.seed.bounded_double (by decide) (by decide)

theorem at13_12 : PairSeed 13 12 := by
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide
  simpa only [hc] using Finite.Seeds.A13.seed.bounded_double (by decide) (by decide)

theorem at13_10 : PairSeed 13 10 :=
  at13_12.restrict_pair (by decide) (by decide) (by decide)

theorem at17_10 : PairSeed 17 10 := by
  have hc : Finite.Seeds.A17.shifts.card = 5 := by decide
  simpa only [hc] using Finite.Seeds.A17.seed.bounded_double (by decide) (by decide)

theorem at19_12 : PairSeed 19 12 := by
  have hc : Finite.Seeds.A19.shifts.card = 6 := by decide
  simpa only [hc] using Finite.Seeds.A19.seed.bounded_double (by decide) (by decide)

theorem at19_10 : PairSeed 19 10 :=
  at19_12.restrict_pair (by decide) (by decide) (by decide)

theorem at23_12 : PairSeed 23 12 := by
  have hc : Finite.Seeds.A23.shifts.card = 6 := by decide
  simpa only [hc] using Finite.Seeds.A23.seed.bounded_double (by decide) (by decide)

theorem at22_10 : PairSeed 22 10 := by
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide
  have h := Finite.Seeds.A11.seed.bounded_cyclic (L := 2)
    (by decide) (by decide) (by decide) (by rw [hc]; decide)
  simpa only [hc] using h

theorem at26_12 : PairSeed 26 12 := by
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide
  have h := Finite.Seeds.A13.seed.bounded_cyclic (L := 2)
    (by decide) (by decide) (by decide) (by rw [hc]; decide)
  simpa only [hc] using h

theorem at26_10 : PairSeed 26 10 :=
  at26_12.restrict_pair (by decide) (by decide) (by decide)

theorem at39_12 : PairSeed 39 12 := by
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide
  have h := Finite.Seeds.A13.seed.bounded_cyclic (L := 3)
    (by decide) (by decide) (by decide) (by rw [hc]; decide)
  simpa only [hc] using h

theorem at46_12 : PairSeed 46 12 := by
  have hc : Finite.Seeds.A23.shifts.card = 6 := by decide
  have h := Finite.Seeds.A23.seed.bounded_cyclic (L := 2)
    (by decide) (by decide) (by decide) (by rw [hc]; decide)
  simpa only [hc] using h

theorem at52_12 : PairSeed 52 12 := by
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide
  have h := Finite.Seeds.A13.seed.bounded_cyclic (L := 4)
    (by decide) (by decide) (by decide) (by rw [hc]; decide)
  simpa only [hc] using h

end RigidGHZ.Supplement.BalancedSeeds
