module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Supplement.AffineSmallSeeds

/-! Printed linear-seed bank, with affine base size 5. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

theorem q20 : LinearSeed 20 8 := by
  have h := bank_large (L := 4) Affine.seed5 (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Affine.shifts5.card = 4 := by decide +kernel
  simpa only [hc] using h

theorem q30 : LinearSeed 30 8 := by
  have h := bank_large (L := 6) Affine.seed5 (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Affine.shifts5.card = 4 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
