module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A17Seed

/-! Printed linear-seed bank, with affine base size 17. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code17 (s : Finite.Seeds.A17.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 4 => 5
  | 5 => 1
  | _ => 0

theorem code17_injective : Function.Injective code17 := by decide +kernel

def embedding17 : Finite.Seeds.A17.shifts ↪ Fin 8 := ⟨code17, code17_injective⟩

theorem code17_monotone : ∀ s t : Finite.Seeds.A17.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding17 t) k) ≤ bit (binaryTriple (embedding17 s) k) := by
  decide +kernel

theorem q34 : LinearSeed 34 10 := by
  have hu : IsUnit (6 : ZMod 17) :=
    (ZMod.isUnit_iff_coprime 6 17).mpr (by decide)
  have h := bank_two Finite.Seeds.A17.seed (by decide) (by decide) (by decide +kernel) 6 hu
  have hc : 2 * Finite.Seeds.A17.shifts.card - (shiftOverlap Finite.Seeds.A17.shifts 6).card = 10 := by
    decide +kernel
  simpa only [hc] using h

theorem q51 : LinearSeed 51 10 := by
  have h := bank_three Finite.Seeds.A17.seed (by decide) (by decide) (by decide)
    embedding17 code17_monotone
  have hc : Finite.Seeds.A17.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q68 : LinearSeed 68 10 := by
  have h := bank_large (L := 4) Finite.Seeds.A17.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A17.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

theorem q85 : LinearSeed 85 10 := by
  have h := bank_large (L := 5) Finite.Seeds.A17.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A17.shifts.card = 5 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
