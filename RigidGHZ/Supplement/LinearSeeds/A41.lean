module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A41Seed

/-! Printed linear-seed bank, with affine base size 41. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

theorem q82 : LinearSeed 82 10 := by
  have hu : IsUnit (6 : ZMod 41) :=
    (ZMod.isUnit_iff_coprime 6 41).mpr (by decide)
  have h := bank_two Finite.Seeds.A41.seed (by decide) (by decide) (by decide +kernel) 6 hu
  have hc : 2 * Finite.Seeds.A41.shifts.card - (shiftOverlap Finite.Seeds.A41.shifts 6).card = 10 := by
    decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
