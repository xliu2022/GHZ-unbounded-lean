module

public import RigidGHZ.Supplement.Periodic.EnumerationStats
public import Mathlib.Combinatorics.Colex

/-! An injective numerical coding used only to shorten kernel finite checks. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic

def finiteSetCode {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ e ∈ S, 2 ^ e.val

 theorem finiteSetCode_injective {n : ℕ} : Function.Injective (@finiteSetCode n) := by
  intro S T h
  apply Finset.image_injective Fin.val_injective
  apply Finset.geomSum_injective (by omega : 2 ≤ 2)
  simpa only [Finset.sum_image, Fin.val_injective.injOn, finiteSetCode] using h

def finitePairCode {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) : ℕ × ℕ :=
  (finiteSetCode p.1, finiteSetCode p.2)

 theorem finitePairCode_injective {n : ℕ} : Function.Injective (@finitePairCode n) := by
  intro p q h
  exact Prod.ext (finiteSetCode_injective (congrArg Prod.fst h))
    (finiteSetCode_injective (congrArg Prod.snd h))

end RigidGHZ.Supplement.Periodic
