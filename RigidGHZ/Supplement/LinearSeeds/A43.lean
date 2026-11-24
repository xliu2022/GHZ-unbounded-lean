module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A43Seed

/-! Printed linear-seed bank, with affine base size 43. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

theorem q86 : LinearSeed 86 10 := by
  have hu : IsUnit (8 : ZMod 43) :=
    (ZMod.isUnit_iff_coprime 8 43).mpr (by decide)
  have h := bank_two Finite.Seeds.A43.seed (by decide) (by decide) (by decide +kernel) 8 hu
  have hc : 2 * Finite.Seeds.A43.shifts.card - (shiftOverlap Finite.Seeds.A43.shifts 8).card = 10 := by
    decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
