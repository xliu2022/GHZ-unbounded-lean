module

public import RigidGHZ.Supplement.MarkedProjection

/-! A perfect matching with one common global bit decomposes into slices.
Marked multiplicity recovery proves that each slice is an actual affine seed
perfect matching, rather than merely a covering with repeated first vertices. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m L : ℕ} [NeZero m] [NeZero L]

/-- Coordinate data of an arbitrary selected perfect matching after its global
bit has been proved constant. -/
structure Selection {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (h : Bool) where
  second : Equiv.Perm (ZMod m × ZMod L)
  third : Equiv.Perm (ZMod m × ZMod L)
  shift : (ZMod m × ZMod L) → S
  second_eq : ∀ w, second w = liftMap lam δ C β (h, shift w) 1 w
  third_eq : ∀ w, third w = liftMap lam δ C β (h, shift w) 2 w

namespace Selection

variable {S : Finset (ZMod m)} {lam δ : ZMod m} {C : Marking S} {β : ℕ} {h : Bool}
  (P : Selection (L := L) lam δ C β h)

 def row (y : ZMod L) (b : ZMod m) : ZMod m × ZMod L := P.second.symm (b, y)
 def first (y : ZMod L) (b : ZMod m) : ZMod m := (P.row y b).1
 def rowShift (y : ZMod L) (b : ZMod m) : S := P.shift (P.row y b)
 def last (y : ZMod L) (b : ZMod m) : ZMod m := (P.third (P.row y b)).1

 theorem row_second (y : ZMod L) (b : ZMod m) : P.second (P.row y b) = (b, y) :=
  P.second.apply_symm_apply _

 theorem second_base (y : ZMod L) (b : ZMod m) :
    b = lam * P.first y b + (P.rowShift y b).val := by
  have he := P.second_eq (P.row y b)
  rw [P.row_second] at he
  exact congrArg Prod.fst he

 theorem second_sheet (y : ZMod L) (b : ZMod m) :
    y = (P.row y b).2 + (bit (C.code (P.rowShift y b) (P.first y b)) : ZMod L) +
      β * (bit h : ZMod L) := by
  have he := P.second_eq (P.row y b)
  rw [P.row_second] at he
  simpa [liftMap, sheetOffset, rowShift, first, add_assoc] using congrArg Prod.snd he

 theorem third_base (y : ZMod L) (b : ZMod m) :
    P.last y b = δ * (bit h : ZMod m) - (lam + 1) * P.first y b - (P.rowShift y b).val :=
  congrArg Prod.fst (P.third_eq (P.row y b))

 theorem third_sheet (y : ZMod L) (b : ZMod m) :
    (P.third (P.row y b)).2 = y + (bit h : ZMod L) := by
  have he := lift_sheet_difference lam δ C β (h, P.shift (P.row y b)) (P.row y b)
  rw [← P.third_eq, ← P.second_eq, P.row_second] at he
  exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)

 theorem last_bijective (y : ZMod L) : Function.Bijective (P.last y) := by
  apply Finite.injective_iff_bijective.mp
  intro b c he
  have hrow : P.row y b = P.row y c := by
    apply P.third.injective
    exact Prod.ext he (by rw [P.third_sheet, P.third_sheet])
  have hbc := congrArg (fun w => (P.second w).1) hrow
  simpa only [P.row_second] using hbc

 theorem row_eq_of_first_code (y : ZMod L) (b c : ZMod m)
    (ha : P.first y b = P.first y c)
    (hc : C.code (P.rowShift y b) (P.first y b) = C.code (P.rowShift y c) (P.first y c)) :
    b = c := by
  have hxb := P.second_sheet y b
  have hxc := P.second_sheet y c
  rw [hc] at hxb
  have hrow : P.row y b = P.row y c := by
    apply Prod.ext ha
    exact add_right_cancel (add_right_cancel (hxb.symm.trans hxc))
  have hbc := congrArg (fun w => (P.second w).1) hrow
  simpa only [P.row_second] using hbc

 theorem first_fiber_le_two (y : ZMod L) (a : ZMod m) :
    (Finset.univ.filter (fun b => P.first y b = a)).card ≤ 2 := by
  classical
  calc
    _ ≤ (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn (fun b => C.code (P.rowShift y b) (P.first y b))
      · intro b hb
        exact Finset.mem_univ _
      · intro b hb c hc he
        exact P.row_eq_of_first_code y b c
          ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm) he
    _ = 2 := by simp

 theorem first_fiber_one_outside (y : ZMod L) (a : ZMod m)
    (ha : (ZMod.finEquiv m).symm a ∉ C.marked) :
    (Finset.univ.filter (fun b => P.first y b = a)).card = 1 := by
  classical
  have hle : (Finset.univ.filter (fun b => P.first y b = a)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro b hb c hc
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    apply P.row_eq_of_first_code y b c (hb'.trans hc'.symm)
    rw [hb', hc', C.outside _ _ ha, C.outside _ _ ha]
  let w : ZMod m × ZMod L := (a, y - β * (bit h : ZMod L))
  have hsheet : (P.second w).2 = y := by
    rw [P.second_eq]
    simp [liftMap, sheetOffset, w, C.outside _ a ha]
  have hrow : P.row y (P.second w).1 = w := by
    apply P.second.injective
    rw [P.row_second]
    exact Prod.ext rfl hsheet.symm
  have hmem : (P.second w).1 ∈ Finset.univ.filter (fun b => P.first y b = a) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by dsimp [first]; rw [hrow]⟩
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

 theorem first_sum (hodd : Odd m) (y : ZMod L) :
    ∑ b, P.first y b = ∑ a : ZMod m, a := by
  let e := Equiv.ofBijective (P.last y) (P.last_bijective y)
  have hlast : ∑ b, P.last y b = 0 := by
    exact (Equiv.sum_comp e (fun a => a)).trans (sum_zmod_eq_zero hodd)
  have hbase : ∑ b, (P.first y b + b + P.last y b) = 0 := by
    calc
      _ = ∑ _b : ZMod m, δ * (bit h : ZMod m) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hb := P.second_base y b
        have hc := P.third_base y b
        linear_combination hb + hc
      _ = 0 := by simp [ZMod.card, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hlast, sum_zmod_eq_zero hodd] at hbase
  simpa [sum_zmod_eq_zero hodd] using hbase

 theorem first_bijective (hodd : Odd m) (y : ZMod L) : Function.Bijective (P.first y) :=
  marked_projection_bijective C (P.first y) (P.first_fiber_one_outside y)
    (fun a _ => P.first_fiber_le_two y a) (P.first_sum hodd y)

/-- Every slice has exactly one of the original seed shifts, proved through
ordinary seed perfect matchings after recovering the first-coordinate bijection. -/
 theorem slice_shift (B : Seed lam S) (hodd : Odd m) (y : ZMod L) :
    ∃ s : S, ∀ b, P.rowShift y b = s := by
  let a : Equiv.Perm (ZMod m) := Equiv.ofBijective (P.first y) (P.first_bijective hodd y)
  let c : Equiv.Perm (ZMod m) := Equiv.ofBijective (P.last y) (P.last_bijective y)
  let q := a.symm
  let r := (a.symm.trans c).trans (Equiv.addRight (-δ * (bit h : ZMod m)))
  have ha (b : ZMod m) : P.first y (a.symm b) = b := a.apply_symm_apply b
  obtain ⟨s, hq, hr⟩ := B.coordinate_complete q r (by
    intro b
    refine ⟨P.rowShift y (a.symm b), ?_, ?_⟩
    · exact (P.second_base y (a.symm b)).trans (by rw [ha])
    · change P.last y (a.symm b) + -δ * (bit h : ZMod m) = _
      rw [P.third_base, ha]
      ring)
  refine ⟨s, ?_⟩
  intro b
  apply Subtype.ext
  have hq' := hq (P.first y b)
  have hab : a.symm (P.first y b) = b := a.symm_apply_apply b
  change a.symm (P.first y b) = _ at hq'
  rw [hab] at hq'
  exact add_left_cancel ((P.second_base y b).symm.trans hq')

end Selection
end RigidGHZ.Supplement.Affine
