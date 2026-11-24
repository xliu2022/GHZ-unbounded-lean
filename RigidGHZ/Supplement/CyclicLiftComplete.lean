module

public import RigidGHZ.Supplement.CyclicLiftSlices

/-! Slice signatures propagate around the sheet cycle, and therefore every
ordinary perfect matching of the marked cyclic lift is prescribed. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m L : ℕ} [NeZero m] [NeZero L]

namespace Selection

variable {S : Finset (ZMod m)} {lam δ : ZMod m} {C : Marking S} {β : ℕ} {h : Bool}
  (P : Selection (L := L) lam δ C β h)

 theorem shift_at_row (t : ZMod L → S) (ht : ∀ y b, P.rowShift y b = t y)
    (w : ZMod m × ZMod L) : P.shift w = t (P.second w).2 := by
  have hrow : P.row (P.second w).2 (P.second w).1 = w := by
    exact P.second.symm_apply_apply w
  have h := ht (P.second w).2 (P.second w).1
  simpa only [rowShift, hrow] using h

 theorem slice_input (hodd : Odd m) (t : ZMod L → S)
    (ht : ∀ y b, P.rowShift y b = t y) (y : ZMod L) (a : ZMod m) :
    P.second (a, y - (bit (C.code (t y) a) : ZMod L) - β * (bit h : ZMod L)) =
      (lam * a + (t y).val, y) := by
  obtain ⟨b, hb⟩ := (P.first_bijective hodd y).surjective a
  have hs := P.second_sheet y b
  rw [ht, hb] at hs
  have hrow : P.row y b = (a, y - (bit (C.code (t y) a) : ZMod L) - β * (bit h : ZMod L)) := by
    apply Prod.ext hb
    linear_combination -hs
  rw [← hrow, P.row_second]
  apply Prod.ext
  · simpa only [ht, hb] using P.second_base y b
  · rfl

 theorem adjacent_codes (hodd : Odd m) (hL : 2 ≤ L) (t : ZMod L → S)
    (ht : ∀ y b, P.rowShift y b = t y) (y : ZMod L) (a : ZMod m) :
    C.code (t (y + 1)) a = C.code (t y) a := by
  letI : Fact (1 < L) := ⟨hL⟩
  cases h0 : C.code (t y) a <;> cases h1 : C.code (t (y + 1)) a
  · rfl
  · have he0 := P.slice_input hodd t ht y a
    have he1 := P.slice_input hodd t ht (y + 1) a
    simp only [h0, h1, bit_false, bit_true, Nat.cast_zero, Nat.cast_one, sub_zero,
      add_sub_cancel_right] at he0 he1
    have hbad : y = y + 1 := congrArg Prod.snd (he0.symm.trans he1)
    have : (0 : ZMod L) = 1 := by simpa using hbad
    exact (zero_ne_one this).elim
  · let w : ZMod m × ZMod L := (a, y - β * (bit h : ZMod L))
    have hs := P.shift_at_row t ht w
    have he := congrArg Prod.snd (P.second_eq w)
    have hsheet : (P.second w).2 = y + (bit (C.code (P.shift w) a) : ZMod L) := by
      simpa [liftMap, sheetOffset, w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using he
    cases hb : C.code (P.shift w) a
    · have hy : (P.second w).2 = y := by simpa [hb] using hsheet
      rw [hy] at hs
      have hc := congrArg (fun s : S => C.code s a) hs
      simp only [hb, h0] at hc
      exact Bool.noConfusion hc
    · have hy : (P.second w).2 = y + 1 := by simpa [hb] using hsheet
      rw [hy] at hs
      have hc := congrArg (fun s : S => C.code s a) hs
      simp only [hb, h1] at hc
      exact Bool.noConfusion hc
  · rfl

 theorem complete (B : Seed lam S) (hodd : Odd m) : ∃ s : S, ∀ w, P.shift w = s := by
  choose t ht using P.slice_shift B hodd
  have hstep : ∀ y : ZMod L, t (y + 1) = t y := by
    intro y
    by_cases hL : 2 ≤ L
    · apply C.injective
      funext a
      exact P.adjacent_codes hodd hL t ht y a
    · have hL1 : L = 1 := by have := NeZero.ne L; omega
      have h1 : (1 : ZMod L) = 0 := by
        simpa using (ZMod.natCast_eq_zero_iff 1 L).mpr (by simp [hL1])
      rw [h1, add_zero]
  have hnat : ∀ n : ℕ, t (n : ZMod L) = t 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, hstep] using ih
  have ht0 : ∀ y : ZMod L, t y = t 0 := by
    intro y
    simpa only [ZMod.natCast_zmod_val] using hnat y.val
  refine ⟨t 0, ?_⟩
  intro w
  exact (P.shift_at_row t ht w).trans (ht0 _)

end Selection

/-- Coordinate classification of every marked cyclic-lift perfect matching.
The seed premise is exactly its ordinary perfect-matching completeness. -/
 theorem lift_complete {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (δ : ZMod m) (hδ : IsUnit δ) (hodd : Odd m) (hcop : m.Coprime L)
    (C : Marking S) (β : ℕ) (q r : Equiv.Perm (ZMod m × ZMod L))
    (hlocal : ∀ w, ∃ hs : Bool × S,
      q w = liftMap lam δ C β hs 1 w ∧ r w = liftMap lam δ C β hs 2 w) :
    ∃ hs : Bool × S, (∀ w, q w = liftMap lam δ C β hs 1 w) ∧
      (∀ w, r w = liftMap lam δ C β hs 2 w) := by
  choose hs hq hr using hlocal
  obtain ⟨h, hh⟩ := lift_bit_constant lam δ hδ hodd hcop C β q r hs hq hr
  have hpair : ∀ w, hs w = (h, (hs w).2) := fun w => Prod.ext (hh w) rfl
  let P : Selection lam δ C β h := {
    second := q
    third := r
    shift := fun w => (hs w).2
    second_eq := by intro w; rw [← hpair w]; exact hq w
    third_eq := by intro w; rw [← hpair w]; exact hr w }
  obtain ⟨s, hs⟩ := P.complete B hodd
  refine ⟨(h, s), ?_, ?_⟩
  · intro w
    have he := P.second_eq w
    rw [hs w] at he
    exact he
  · intro w
    have he := P.third_eq w
    rw [hs w] at he
    exact he

/-- The prescribed rigid family on the ordinary finite lifted hypergraph. -/
def Seed.cyclicFamily {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S) (β : ℕ) :
    RigidFamily (coordinateHypergraph (fun hs : Bool × S => liftMap (L := L) lam δ C β hs))
      (Bool × S) := by
  let p := liftPerm (L := L) B δ C β
  apply rigidFamily_of_coordinates 0 p
  · intro hs
    apply Equiv.ext
    intro w
    exact lift_zero lam δ C β hs w
  · intro i j hij w
    by_contra hn
    push_neg at hn
    have hs : i.2 = j.2 := by
      apply Subtype.ext
      have h := congrArg Prod.fst (hn 1)
      simpa [p, liftMap, doubleMap] using h
    have hh : i.1 = j.1 := by
      apply bit_cast_injective (m := m) (by omega)
      apply hδ.mul_left_cancel
      have h := congrArg Prod.fst (hn 2)
      simpa [p, liftMap, doubleMap, hs] using h
    exact hij (Prod.ext hh hs)
  · intro q hq0 hq
    obtain ⟨hs, h1, h2⟩ := lift_complete B δ hδ hodd hcop C β (q 1) (q 2) (by
      intro w
      obtain ⟨hs, hhs⟩ := hq w
      exact ⟨hs, hhs 1, hhs 2⟩)
    refine ⟨hs, ?_⟩
    funext j
    apply Equiv.ext
    intro w
    fin_cases j
    · change q 0 w = liftMap lam δ C β hs 0 w
      rw [hq0, lift_zero]
      rfl
    · exact h1 w
    · exact h2 w

end RigidGHZ.Supplement.Affine
