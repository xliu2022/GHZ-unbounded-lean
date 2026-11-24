module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Finite.Seeds.A13Seed

/-! Printed linear-seed bank, with affine base size 13. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code13 (s : Finite.Seeds.A13.shifts) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 4 => 5
  | 5 => 1
  | 8 => 3
  | _ => 0

theorem code13_injective : Function.Injective code13 := by decide +kernel

def embedding13 : Finite.Seeds.A13.shifts ↪ Fin 8 := ⟨code13, code13_injective⟩

theorem code13_monotone : ∀ s t : Finite.Seeds.A13.shifts, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding13 t) k) ≤ bit (binaryTriple (embedding13 s) k) := by
  decide +kernel

theorem q26 : LinearSeed 26 10 := by
  have hu : IsUnit (2 : ZMod 13) :=
    (ZMod.isUnit_iff_coprime 2 13).mpr (by decide)
  have h := bank_two Finite.Seeds.A13.seed (by decide) (by decide) (by decide +kernel) 2 hu
  have hc : 2 * Finite.Seeds.A13.shifts.card - (shiftOverlap Finite.Seeds.A13.shifts 2).card = 10 := by
    decide +kernel
  simpa only [hc] using h

theorem q39 : LinearSeed 39 12 := by
  have h := bank_three Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    embedding13 code13_monotone
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q52 : LinearSeed 52 12 := by
  have h := bank_large (L := 4) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q65 : LinearSeed 65 12 := by
  have h := bank_large (L := 5) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q78 : LinearSeed 78 12 := by
  have h := bank_large (L := 6) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q91 : LinearSeed 91 12 := by
  have h := bank_large (L := 7) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q104 : LinearSeed 104 12 := by
  have h := bank_large (L := 8) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q117 : LinearSeed 117 12 := by
  have h := bank_large (L := 9) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

theorem q143 : LinearSeed 143 12 := by
  have h := bank_large (L := 11) Finite.Seeds.A13.seed (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide)
  have hc : Finite.Seeds.A13.shifts.card = 6 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
