module

public import RigidGHZ.Supplement.AffineDoubling

/-! Explicit coordinate permutations and the global-bit obstruction for the
marked cyclic lift. The base and sheet congruences are both proved from the
bijections in a standard perfect matching. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m L : ℕ} [NeZero m] [NeZero L]

/-- A superincreasing marked code for the prescribed shifts. -/
structure Marking (S : Finset (ZMod m)) where
  marked : Finset (Fin m)
  sum_lt : ∑ a ∈ marked, a.val < m
  superincreasing : Marked.Superincreasing marked
  code : S → ZMod m → Bool
  outside : ∀ s a, (ZMod.finEquiv m).symm a ∉ marked → code s a = false
  injective : Function.Injective code

/-- The sheet offsets at the three coordinates. `β` may be any integer
represented by a natural number; the paper uses zero or one. -/
def sheetOffset {S : Finset (ZMod m)} (C : Marking S) (β : ℕ)
    (h : Bool) (s : S) : Fin 3 → ZMod m → ZMod L :=
  ![(fun _ => 0), (fun a => (bit (C.code s a) : ZMod L) + β * (bit h : ZMod L)),
    (fun a => (bit (C.code s a) : ZMod L) + (β + 1) * (bit h : ZMod L))]

/-- A base permutation together with translations in its individual fibers. -/
def skewPerm {A K : Type*} [AddGroup K] (p : Equiv.Perm A) (c : A → K) :
    Equiv.Perm (A × K) where
  toFun w := (p w.1, w.2 + c w.1)
  invFun w := (p.symm w.1, w.2 - c (p.symm w.1))
  left_inv w := by simp
  right_inv w := by simp

@[simp] theorem skewPerm_apply {A K : Type*} [AddGroup K]
    (p : Equiv.Perm A) (c : A → K) (w : A × K) :
    skewPerm p c w = (p w.1, w.2 + c w.1) := rfl

/-- The printed coordinate formula for the cyclic lift. -/
def liftMap {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S) (β : ℕ)
    (hs : Bool × S) (j : Fin 3) (w : ZMod m × ZMod L) : ZMod m × ZMod L :=
  (doubleMap lam δ hs.1 hs.2.val j w.1, w.2 + sheetOffset C β hs.1 hs.2 j w.1)

 def liftPerm {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (δ : ZMod m) (C : Marking S) (β : ℕ) (hs : Bool × S) (j : Fin 3) :
    Equiv.Perm (ZMod m × ZMod L) :=
  skewPerm (doublePerm B.unit_left B.unit_right δ hs.1 hs.2.val j)
    (sheetOffset C β hs.1 hs.2 j)

@[simp] theorem liftPerm_apply {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (δ : ZMod m) (C : Marking S) (β : ℕ) (hs : Bool × S) (j : Fin 3)
    (w : ZMod m × ZMod L) : liftPerm B δ C β hs j w = liftMap lam δ C β hs j w := rfl

 theorem lift_zero {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (hs : Bool × S) (w : ZMod m × ZMod L) : liftMap lam δ C β hs 0 w = w := by
  simp [liftMap, doubleMap, sheetOffset]

 theorem lift_base_sum {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (hs : Bool × S) (w : ZMod m × ZMod L) :
    w.1 + (liftMap lam δ C β hs 1 w).1 + (liftMap lam δ C β hs 2 w).1 =
      δ * (bit hs.1 : ZMod m) := double_sum lam δ w.1 hs.2.val hs.1

 theorem lift_sheet_difference {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (hs : Bool × S) (w : ZMod m × ZMod L) :
    (liftMap lam δ C β hs 2 w).2 - (liftMap lam δ C β hs 1 w).2 =
      (bit hs.1 : ZMod L) := by
  simp [liftMap, sheetOffset]
  ring

 theorem sum_base_product (hodd : Odd m) :
    ∑ w : ZMod m × ZMod L, w.1 = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_zmod_eq_zero hodd, mul_zero]

/-- Counting the bit-one edges in two coprime moduli forces one common bit.
Both congruences follow directly from the coordinate bijections. -/
 theorem lift_bit_constant {S : Finset (ZMod m)} (lam δ : ZMod m) (hδ : IsUnit δ)
    (hodd : Odd m) (hcop : m.Coprime L) (C : Marking S) (β : ℕ)
    (q r : Equiv.Perm (ZMod m × ZMod L)) (hs : (ZMod m × ZMod L) → Bool × S)
    (hq : ∀ w, q w = liftMap lam δ C β (hs w) 1 w)
    (hr : ∀ w, r w = liftMap lam δ C β (hs w) 2 w) :
    ∃ h, ∀ w, (hs w).1 = h := by
  let u := ∑ w, bit (hs w).1
  have hmzero : δ * (u : ZMod m) = 0 := by
    calc
      _ = ∑ w, (w.1 + (q w).1 + (r w).1) := by
        rw [show (u : ZMod m) = ∑ w, (bit (hs w).1 : ZMod m) from Nat.cast_sum _ _,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        rw [hq, hr]
        exact (lift_base_sum lam δ C β (hs w) w).symm
      _ = 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Equiv.sum_comp q Prod.fst, Equiv.sum_comp r Prod.fst, sum_base_product hodd]
        simp
  have hLzero : (u : ZMod L) = 0 := by
    calc
      _ = ∑ w, ((r w).2 - (q w).2) := by
        rw [show (u : ZMod L) = ∑ w, (bit (hs w).1 : ZMod L) from Nat.cast_sum _ _]
        apply Finset.sum_congr rfl
        intro w hw
        rw [hq, hr]
        exact (lift_sheet_difference lam δ C β (hs w) w).symm
      _ = 0 := by
        rw [Finset.sum_sub_distrib, Equiv.sum_comp r Prod.snd, Equiv.sum_comp q Prod.snd, sub_self]
  have hmdiv : m ∣ u := (ZMod.natCast_eq_zero_iff u m).mp
    (hδ.mul_left_cancel (by simpa using hmzero))
  have hLdiv : L ∣ u := (ZMod.natCast_eq_zero_iff u L).mp hLzero
  apply constant_bit_of_card_dvd (fun w => (hs w).1)
  simpa only [Fintype.card_prod, ZMod.card, ← sum_bit] using
    hcop.mul_dvd_of_dvd_of_dvd hmdiv hLdiv

end RigidGHZ.Supplement.Affine
