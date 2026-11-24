module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A19Seed

/-! Printed linear-seed bank, with affine base size 19. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code19 (s : Finite.Seeds.A19.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 3 => 3
  | 12 => 2
  | 14 => 5
  | 15 => 4
  | _ => 0

theorem code19_injective : Function.Injective code19 := by decide +kernel

def embedding19 : Finite.Seeds.A19.shifts ↪ Fin 8 := ⟨code19, code19_injective⟩

theorem code19_monotone : ∀ s t : Finite.Seeds.A19.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding19 t) k) ≤ bit (binaryTriple (embedding19 s) k) := by
  decide +kernel

theorem q38 : LinearSeed 38 11 := by
  have hu : IsUnit (4 : ZMod 19) :=
    (ZMod.isUnit_iff_coprime 4 19).mpr (by decide)
  have h := bank_two Finite.Seeds.A19.seed (by decide) (by decide) (by decide +kernel) 4 hu
  have hc : 2 * Finite.Seeds.A19.shifts.card - (shiftOverlap Finite.Seeds.A19.shifts 4).card = 11 := by
    decide +kernel
  simpa only [hc] using h

theorem q57 : LinearSeed 57 12 := by
  have h := bank_three Finite.Seeds.A19.seed (by decide) (by decide) (by decide)
    embedding19 code19_monotone
  have hc : Finite.Seeds.A19.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q76 : LinearSeed 76 12 := by
  have h := bank_large (L := 4) Finite.Seeds.A19.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A19.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
