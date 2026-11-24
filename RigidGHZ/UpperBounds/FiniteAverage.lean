module

public import RigidGHZ.UpperBounds.Reciprocal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Prod

/-! Elementary finite averages used in the representative argument. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

/-- The average over a finite sample space, expressed without measure theory. -/
def finiteAverage {E : Type*} [Fintype E] (f : E → ℝ) : ℝ :=
  (∑ e, f e) / Fintype.card E

variable {E F : Type*} [Fintype E] [Fintype F]

theorem finiteAverage_mono (f g : E → ℝ) (h : ∀ e, f e ≤ g e) :
    finiteAverage f ≤ finiteAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun e _ => h e)) (Nat.cast_nonneg _)

theorem finiteAverage_const [Nonempty E] (a : ℝ) :
    finiteAverage (fun _ : E => a) = a := by
  unfold finiteAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))

theorem finiteAverage_sum (f : E → F → ℝ) :
    finiteAverage (fun e => ∑ x : F, f e x) = ∑ x : F, finiteAverage (fun e => f e x) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_equiv (e : E ≃ F) (f : F → ℝ) :
    finiteAverage (fun x => f (e x)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_prod (f : E × F → ℝ) :
    finiteAverage f = finiteAverage (fun e => finiteAverage (fun x => f (e, x))) := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Nat.cast_mul, Finset.sum_div, div_div, mul_comm]

theorem finiteAverage_split {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (b : B) (f : C → ({x : B // x ≠ b} → C) → ℝ) :
    finiteAverage (fun q : B → C => f (q b) (fun x => q x)) =
      finiteAverage (fun c : C => finiteAverage (f c)) := by
  have h := finiteAverage_equiv (Equiv.funSplitAt b C) (fun x => f x.1 x.2)
  exact h.trans (finiteAverage_prod (fun x => f x.1 x.2))

theorem finiteAverage_sum_subtype {B : Type*} [Fintype B] [DecidableEq B]
    (s : Finset B) (f : B → ℝ) :
    (∑ x : s, f x) = ∑ x ∈ s, f x := Finset.sum_coe_sort s f

end RigidGHZ.UpperBounds
