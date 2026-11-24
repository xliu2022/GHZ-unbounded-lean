module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A23Seed

/-! Printed linear-seed bank, with affine base size 23. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code23 (s : Finite.Seeds.A23.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 9 => 5
  | 10 => 1
  | 11 => 0
  | _ => 0

theorem code23_injective : Function.Injective code23 := by decide +kernel

def embedding23 : Finite.Seeds.A23.shifts ↪ Fin 8 := ⟨code23, code23_injective⟩

theorem code23_monotone : ∀ s t : Finite.Seeds.A23.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding23 t) k) ≤ bit (binaryTriple (embedding23 s) k) := by
  decide +kernel

theorem q46 : LinearSeed 46 12 := by
  have hu : IsUnit (3 : ZMod 23) :=
    (ZMod.isUnit_iff_coprime 3 23).mpr (by decide)
  have h := bank_two Finite.Seeds.A23.seed (by decide) (by decide) (by decide +kernel) 3 hu
  have hc : 2 * Finite.Seeds.A23.shifts.card - (shiftOverlap Finite.Seeds.A23.shifts 3).card = 12 := by
    decide +kernel
  simpa only [hc] using h

theorem q69 : LinearSeed 69 12 := by
  have h := bank_three Finite.Seeds.A23.seed (by decide) (by decide) (by decide)
    embedding23 code23_monotone
  have hc : Finite.Seeds.A23.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q92 : LinearSeed 92 12 := by
  have h := bank_large (L := 4) Finite.Seeds.A23.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A23.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q138 : LinearSeed 138 12 := by
  have h := bank_large (L := 6) Finite.Seeds.A23.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A23.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
