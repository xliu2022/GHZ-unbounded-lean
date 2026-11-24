module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Supplement.AffineSmallSeeds

/-! Printed linear-seed bank, with affine base size 7. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.LinearSeeds

open RigidGHZ.Supplement.Affine

def code7 (s : Affine.shifts7) : Fin 8 :=
  match s.val.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 3 => 0
  | _ => 0

theorem code7_injective : Function.Injective code7 := by decide +kernel

def embedding7 : Affine.shifts7 ↪ Fin 8 := ⟨code7, code7_injective⟩

theorem code7_monotone : ∀ s t : Affine.shifts7, t.val = s.val + 1 → ∀ k : Fin 3,
    bit (binaryTriple (embedding7 t) k) ≤ bit (binaryTriple (embedding7 s) k) := by
  decide +kernel

theorem q21 : LinearSeed 21 8 := by
  have h := bank_three Affine.seed7 (by decide) (by decide) (by decide)
    embedding7 code7_monotone
  have hc : Affine.shifts7.card = 4 := by decide +kernel
  simpa only [hc] using h

end RigidGHZ.Supplement.LinearSeeds
