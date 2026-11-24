module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A29Seed

/-! Printed linear-seed bank, with affine base size 29. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code29 (s : Finite.Seeds.A29.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 7 => 3
  | 20 => 5
  | 21 => 1
  | _ => 0

theorem code29_injective : Function.Injective code29 := by decide +kernel

def embedding29 : Finite.Seeds.A29.shifts ↪ Fin 8 := ⟨code29, code29_injective⟩

theorem code29_monotone : ∀ s t : Finite.Seeds.A29.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding29 t) k) ≤ bit (binaryTriple (embedding29 s) k) := by
  decide +kernel

theorem q58 : LinearSeed 58 12 := by
  have hu : IsUnit (3 : ZMod 29) :=
    (ZMod.isUnit_iff_coprime 3 29).mpr (by decide)
  have h := bank_two Finite.Seeds.A29.seed (by decide) (by decide) (by decide +kernel) 3 hu
  have hc : 2 * Finite.Seeds.A29.shifts.card - (shiftOverlap Finite.Seeds.A29.shifts 3).card = 12 := by
    decide +kernel
  simpa only [hc] using h

theorem q87 : LinearSeed 87 12 := by
  have h := bank_three Finite.Seeds.A29.seed (by decide) (by decide) (by decide)
    embedding29 code29_monotone
  have hc : Finite.Seeds.A29.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q116 : LinearSeed 116 12 := by
  have h := bank_large (L := 4) Finite.Seeds.A29.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A29.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
