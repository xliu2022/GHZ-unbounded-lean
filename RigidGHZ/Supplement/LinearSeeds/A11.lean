module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A11Seed

/-! Printed linear-seed bank, with affine base size 11. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code11 (s : Finite.Seeds.A11.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 3 => 0
  | 5 => 5
  | _ => 0

theorem code11_injective : Function.Injective code11 := by decide +kernel

def embedding11 : Finite.Seeds.A11.shifts ↪ Fin 8 := ⟨code11, code11_injective⟩

theorem code11_monotone : ∀ s t : Finite.Seeds.A11.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding11 t) k) ≤ bit (binaryTriple (embedding11 s) k) := by
  decide +kernel

theorem q22 : LinearSeed 22 9 := by
  have hu : IsUnit (4 : ZMod 11) :=
    (ZMod.isUnit_iff_coprime 4 11).mpr (by decide)
  have h := bank_two Finite.Seeds.A11.seed (by decide) (by decide) (by decide +kernel) 4 hu
  have hc : 2 * Finite.Seeds.A11.shifts.card - (shiftOverlap Finite.Seeds.A11.shifts 4).card = 9 := by
    decide +kernel
  simpa only [hc] using h

theorem q33 : LinearSeed 33 10 := by
  have h := bank_three Finite.Seeds.A11.seed (by decide) (by decide) (by decide)
    embedding11 code11_monotone
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q44 : LinearSeed 44 10 := by
  have h := bank_large (L := 4) Finite.Seeds.A11.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q55 : LinearSeed 55 10 := by
  have h := bank_large (L := 5) Finite.Seeds.A11.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q66 : LinearSeed 66 10 := by
  have h := bank_large (L := 6) Finite.Seeds.A11.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q77 : LinearSeed 77 10 := by
  have h := bank_large (L := 7) Finite.Seeds.A11.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A11.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
