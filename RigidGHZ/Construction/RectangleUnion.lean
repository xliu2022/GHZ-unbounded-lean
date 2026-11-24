module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Finset.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

/-!
# Exact count of a monotone family of translated rectangles

This is the total-owner count used in Lemma A.2. The rectangles are written
with positive shifts; translating and reflecting a finite set preserves its
cardinality. The classification into prefix, suffix, and internal owners is
not asserted by this file.
-/

@[expose] public section

namespace RigidGHZ.Rectangle

open scoped Finset

def gamma (b : ℕ) : ℕ := b.choose 2

@[simp] theorem gamma_zero : gamma 0 = 0 := rfl

theorem gamma_succ (b : ℕ) : gamma (b + 1) = gamma b + b := by
  simpa [gamma, Nat.add_comm] using Nat.choose_succ_succ b 1

theorem gamma_mono {a b : ℕ} (h : a ≤ b) : gamma a ≤ gamma b :=
  Nat.choose_le_choose 2 h

def rectangle (W J b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico b (b + W)) ×ˢ (Finset.Ico (gamma b) (gamma b + J))

@[simp] theorem rectangle_card (W J b : ℕ) : (rectangle W J b).card = W * J := by
  simp [rectangle]

def rectangleUnion (W J T : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (T + 1)).biUnion (rectangle W J)

theorem rectangleUnion_succ (W J T : ℕ) :
    rectangleUnion W J (T + 1) = rectangleUnion W J T ∪ rectangle W J (T + 1) := by
  simp only [rectangleUnion, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- A point in the new rectangle and any earlier rectangle is already in the
immediately preceding rectangle. -/
theorem union_inter_next (W J T : ℕ) :
    rectangleUnion W J T ∩ rectangle W J (T + 1) =
      rectangle W J T ∩ rectangle W J (T + 1) := by
  ext x
  simp only [Finset.mem_inter, rectangleUnion, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨⟨b, hb, hxb⟩, hxn⟩
    refine ⟨?_, hxn⟩
    have hg : gamma b ≤ gamma T := gamma_mono (by omega)
    have hgn : gamma T ≤ gamma (T + 1) := gamma_mono (by omega)
    simp only [rectangle, Finset.mem_product, Finset.mem_Ico] at hxb hxn ⊢
    omega
  · rintro ⟨hxt, hxn⟩
    exact ⟨⟨T, by omega, hxt⟩, hxn⟩

theorem consecutive_inter_card (W J T : ℕ) :
    (rectangle W J T ∩ rectangle W J (T + 1)).card =
      (W - 1) * (J - T) := by
  have hT : T ≤ T + 1 := Nat.le_succ T
  have hg : gamma T ≤ gamma (T + 1) := gamma_mono hT
  unfold rectangle
  rw [Finset.product_inter_product, Finset.Ico_inter_Ico, Finset.Ico_inter_Ico]
  rw [max_eq_right hT, min_eq_left (Nat.add_le_add_right hT W),
    max_eq_right hg, min_eq_left (Nat.add_le_add_right hg J)]
  simp only [Finset.card_product, Nat.card_Ico, gamma_succ]
  congr 1 <;> omega

/-- The exact total number of owners for a rectangle:
`(W+T) J + (W-1) choose(T,2)`. This is a universal symbolic count. -/
theorem rectangleUnion_card (W J T : ℕ) (hW : 1 ≤ W) (hT : T ≤ J + 1) :
    (rectangleUnion W J T).card = (W + T) * J + (W - 1) * gamma T := by
  induction T with
  | zero => simp [rectangleUnion]
  | succ T ih =>
    have hTJ : T ≤ J := by omega
    have hi := ih (by omega)
    have hc := Finset.card_union_add_card_inter
      (rectangleUnion W J T) (rectangle W J (T + 1))
    rw [union_inter_next, consecutive_inter_card, rectangle_card] at hc
    have harea : (W - 1) * (J - T) + (J + (W - 1) * T) = W * J := by
      calc
        (W - 1) * (J - T) + (J + (W - 1) * T) =
            (W - 1) * ((J - T) + T) + J := by ring
        _ = (W - 1) * J + J := by rw [Nat.sub_add_cancel hTJ]
        _ = W * J := by
          rw [← Nat.add_one_mul, Nat.sub_add_cancel hW]
    have hrec : (rectangleUnion W J (T + 1)).card =
        (rectangleUnion W J T).card + J + (W - 1) * T := by
      rw [rectangleUnion_succ]
      omega
    rw [hrec, hi, gamma_succ]
    ring

end RigidGHZ.Rectangle
