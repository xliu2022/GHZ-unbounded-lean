module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A31Seed

/-! Printed linear-seed bank, with affine base size 31. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code31 (s : Finite.Seeds.A31.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 3 => 5
  | 16 => 3
  | 21 => 4
  | 28 => 2
  | _ => 0

theorem code31_injective : Function.Injective code31 := by decide +kernel

def embedding31 : Finite.Seeds.A31.shifts ↪ Fin 8 := ⟨code31, code31_injective⟩

theorem code31_monotone : ∀ s t : Finite.Seeds.A31.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding31 t) k) ≤ bit (binaryTriple (embedding31 s) k) := by
  decide +kernel

theorem q62 : LinearSeed 62 12 := by
  have hu : IsUnit (8 : ZMod 31) :=
    (ZMod.isUnit_iff_coprime 8 31).mpr (by decide)
  have h := bank_two Finite.Seeds.A31.seed (by decide) (by decide) (by decide +kernel) 8 hu
  have hc : 2 * Finite.Seeds.A31.shifts.card - (shiftOverlap Finite.Seeds.A31.shifts 8).card = 12 := by
    decide +kernel
  simpa only [hc] using h

theorem q93 : LinearSeed 93 12 := by
  have h := bank_three Finite.Seeds.A31.seed (by decide) (by decide) (by decide)
    embedding31 code31_monotone
  have hc : Finite.Seeds.A31.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q124 : LinearSeed 124 12 := by
  have h := bank_large (L := 4) Finite.Seeds.A31.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A31.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
