module

public import RigidGHZ.Supplement.CyclicLiftDegrees

/-! Pair collision analysis for beta-one cyclic lifts. This separates the
three possible pairs of parts and records exactly the small-period obstruction. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open UpperBounds

variable {m L : ℕ} [NeZero m] [NeZero L]

 theorem cross_pair_01 {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (hL : 2 ≤ L) (s t : S) (w v : ZMod m × ZMod L)
    (h0 : liftMap lam δ C 1 (false, s) 0 w = liftMap lam δ C 1 (true, t) 0 v)
    (h1 : liftMap lam δ C 1 (false, s) 1 w = liftMap lam δ C 1 (true, t) 1 v) : False := by
  letI : Fact (1 < L) := ⟨hL⟩
  have hw : w = v := by simpa only [lift_zero] using h0
  subst v
  have hst : s = t := by
    apply Subtype.ext
    simpa [liftMap, doubleMap] using congrArg Prod.fst h1
  subst t
  have hs := congrArg Prod.snd h1
  have hbad : (0 : ZMod L) = 1 := by simpa [liftMap, sheetOffset, add_assoc] using hs
  exact zero_ne_one hbad

 theorem cross_pair_12 {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (hL : 2 ≤ L) (s t : S) (w v : ZMod m × ZMod L)
    (h1 : liftMap lam δ C 1 (false, s) 1 w = liftMap lam δ C 1 (true, t) 1 v)
    (h2 : liftMap lam δ C 1 (false, s) 2 w = liftMap lam δ C 1 (true, t) 2 v) : False := by
  letI : Fact (1 < L) := ⟨hL⟩
  have hbad : (0 : ZMod L) = 1 := by
    calc
      _ = (liftMap lam δ C 1 (false, s) 2 w).2 - (liftMap lam δ C 1 (false, s) 1 w).2 := by
        simpa using (lift_sheet_difference lam δ C 1 (false, s) w).symm
      _ = (liftMap lam δ C 1 (true, t) 2 v).2 - (liftMap lam δ C 1 (true, t) 1 v).2 := by
        rw [h1, h2]
      _ = _ := by simpa using lift_sheet_difference lam δ C 1 (true, t) v
  exact zero_ne_one hbad

 theorem cross_pair_02 {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (s t : S) (w v : ZMod m × ZMod L)
    (hsep : ∀ a, t.val = s.val + δ →
      (bit (C.code t a) : ZMod L) + 2 ≠ (bit (C.code s a) : ZMod L))
    (h0 : liftMap lam δ C 1 (false, s) 0 w = liftMap lam δ C 1 (true, t) 0 v)
    (h2 : liftMap lam δ C 1 (false, s) 2 w = liftMap lam δ C 1 (true, t) 2 v) : False := by
  have hw : w = v := by simpa only [lift_zero] using h0
  subst v
  have hbase := congrArg Prod.fst h2
  have hshift : t.val = s.val + δ := by
    change δ * (bit false : ZMod m) - (lam + 1) * w.1 - s.val =
      δ * (bit true : ZMod m) - (lam + 1) * w.1 - t.val at hbase
    simp only [bit_false, bit_true, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] at hbase
    linear_combination hbase
  have hsheet := congrArg Prod.snd h2
  have hbad : (bit (C.code t w.1) : ZMod L) + 2 = (bit (C.code s w.1) : ZMod L) := by
    simpa [liftMap, sheetOffset, one_add_one_eq_two] using hsheet.symm
  exact hsep w.1 hshift hbad

 theorem cross_pair_impossible {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (hL : 2 ≤ L) (s t : S) (w v : ZMod m × ZMod L)
    (hsep : ∀ a, t.val = s.val + δ →
      (bit (C.code t a) : ZMod L) + 2 ≠ (bit (C.code s a) : ZMod L))
    (i j : Fin 3) (hij : i ≠ j)
    (hi : liftMap lam δ C 1 (false, s) i w = liftMap lam δ C 1 (true, t) i v)
    (hj : liftMap lam δ C 1 (false, s) j w = liftMap lam δ C 1 (true, t) j v) : False := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hij rfl
    | exact cross_pair_01 lam δ C hL s t w v hi hj
    | exact cross_pair_01 lam δ C hL s t w v hj hi
    | exact cross_pair_12 lam δ C hL s t w v hi hj
    | exact cross_pair_12 lam δ C hL s t w v hj hi
    | exact cross_pair_02 lam δ C s t w v hsep hi hj
    | exact cross_pair_02 lam δ C s t w v hsep hj hi

/-- The complete algebraic criterion for linearity after retaining any chosen
matching classes. It reduces all cross-bit collisions to the 0--2 part pair. -/
 theorem retained_codegree_one {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (hL : 2 ≤ L) (R : Finset (Bool × S))
    (hsep : ∀ s t : S, (false, s) ∈ R → (true, t) ∈ R → ∀ a,
      t.val = s.val + δ →
        (bit (C.code t a) : ZMod L) + 2 ≠ (bit (C.code s a) : ZMod L))
    (X : Finset (Fin 3 × (ZMod m × ZMod L))) (hX : X.card = 2) :
    codegree (coordinateHypergraph (fun hs : R => liftMap lam δ C 1 hs.val)) X ≤ 1 := by
  apply coordinate_codegree_one _ _ X hX
  intro s t w v i j hij hi hj
  rcases s with ⟨⟨h, s⟩, hs⟩
  rcases t with ⟨⟨k, t⟩, ht⟩
  cases h <;> cases k
  · exact lift_same_bit_pair lam δ C 1 false s t w v i j hij hi hj
  · exact (cross_pair_impossible lam δ C hL s t w v (hsep s t hs ht) i j hij hi hj).elim
  · exact (cross_pair_impossible lam δ C hL t s v w (hsep t s ht hs) i j hij hi.symm hj.symm).elim
  · exact lift_same_bit_pair lam δ C 1 true s t w v i j hij hi hj

 theorem cast_small_ne_zero {n : ℕ} (hn : 0 < n) (hnL : n < L) : (n : ZMod L) ≠ 0 := by
  intro he
  have hd := (ZMod.natCast_eq_zero_iff n L).mp he
  have hle := Nat.le_of_dvd hn hd
  omega

 theorem bits_separated_large (hL : 4 ≤ L) (b c : Bool) :
    (bit c : ZMod L) + 2 ≠ (bit b : ZMod L) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    simpa using cast_small_ne_zero (L := L) (n := 1) (by decide) (by omega)
  have h2 : (2 : ZMod L) ≠ 0 := by
    simpa using cast_small_ne_zero (L := L) (n := 2) (by decide) (by omega)
  have h3 : (3 : ZMod L) ≠ 0 := by
    simpa using cast_small_ne_zero (L := L) (n := 3) (by decide) (by omega)
  cases b <;> cases c <;> simp only [bit_false, bit_true, Nat.cast_zero, Nat.cast_one]
  · simpa using h2
  · intro he
    apply h3
    linear_combination he
  · intro he
    apply h1
    linear_combination he
  · intro he
    apply h2
    linear_combination he

 theorem bits_separated_three (b c : Bool) (hmono : bit c ≤ bit b) :
    (bit c : ZMod 3) + 2 ≠ (bit b : ZMod 3) := by
  cases b <;> cases c <;> norm_num [bit] at *
  all_goals decide

end RigidGHZ.Supplement.Affine
