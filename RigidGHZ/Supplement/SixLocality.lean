module

public import RigidGHZ.Partite
public import Mathlib.Data.ZMod.Basic

/-! Locality of the six formulas printed in Supplement S1. This file concerns
the original cyclic coordinate maps, independently of the alternative grafting
proof of six-at-every-size. In even size, conjugating the ordinary rotation by
the transposition of 1 and 2 is precisely the cycle with those entries exchanged. -/

@[expose] public section

namespace RigidGHZ.Supplement.SixCyclic

variable {m : ℕ} [NeZero m]

def tau : Equiv.Perm (ZMod m) :=
  if Odd m then Equiv.addRight 1 else
    (Equiv.swap 1 2).trans ((Equiv.addRight 1).trans (Equiv.swap 1 2))

theorem tau_odd (hodd : Odd m) (a : ZMod m) : tau a = a + 1 := by
  simp [tau, hodd]

theorem tau_even (hodd : ¬Odd m) (a : ZMod m) :
    tau a = Equiv.swap 1 2 (Equiv.swap 1 2 a + 1) := by
  simp [tau, hodd]

theorem natCast_ne_of_lt {a b : ℕ} (ha : a < m) (hb : b < m) (hab : a ≠ b) :
    (a : ZMod m) ≠ (b : ZMod m) := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  exact hab hv

/-- The modified cycle moves by one of the three printed modular offsets. -/
theorem tau_step (hm : 3 ≤ m) (a : ZMod m) :
    tau a = a - 1 ∨ tau a = a + 1 ∨ tau a = a + 2 := by
  by_cases hodd : Odd m
  · exact Or.inr (Or.inl (tau_odd hodd a))
  have hm4 : 4 ≤ m := by
    by_contra h
    have hm3 : m = 3 := by omega
    subst m
    exact hodd (by decide)
  have h01 : (0 : ZMod m) ≠ 1 := by
    simpa using (natCast_ne_of_lt (m := m) (a := 0) (b := 1) (by omega) (by omega) (by decide))
  have h02 : (0 : ZMod m) ≠ 2 := by
    simpa using (natCast_ne_of_lt (m := m) (a := 0) (b := 2) (by omega) (by omega) (by decide))
  have h31 : (3 : ZMod m) ≠ 1 := by
    simpa using (natCast_ne_of_lt (m := m) (a := 3) (b := 1) (by omega) (by omega) (by decide))
  have h32 : (3 : ZMod m) ≠ 2 := by
    simpa using (natCast_ne_of_lt (m := m) (a := 3) (b := 2) (by omega) (by omega) (by decide))
  by_cases ha0 : a = 0
  · subst a
    right; right
    rw [tau_even hodd, Equiv.swap_apply_of_ne_of_ne h01 h02, zero_add,
      Equiv.swap_apply_left, zero_add]
  by_cases ha1 : a = 1
  · subst a
    right; right
    rw [tau_even hodd, Equiv.swap_apply_left]
    have h3 : (2 : ZMod m) + 1 = 3 := by ring
    rw [h3, Equiv.swap_apply_of_ne_of_ne h31 h32]
    ring
  by_cases ha2 : a = 2
  · subst a
    left
    rw [tau_even hodd, Equiv.swap_apply_right, one_add_one_eq_two,
      Equiv.swap_apply_right]
    ring
  have ha1' : a + 1 ≠ 1 := by
    intro h
    apply ha0
    apply add_right_cancel (b := (1 : ZMod m))
    simpa only [zero_add] using h
  have ha2' : a + 1 ≠ 2 := by
    intro h
    apply ha1
    apply add_right_cancel (b := (1 : ZMod m))
    simpa only [one_add_one_eq_two] using h
  right; left
  rw [tau_even hodd, Equiv.swap_apply_of_ne_of_ne ha1 ha2,
    Equiv.swap_apply_of_ne_of_ne ha1' ha2']

def second (a : ZMod m) (o : Fin 3) : ZMod m := ![a - 1, a, a + 1] o

def thirdBase (a : ZMod m) (o : Fin 3) : ZMod m := ![a, a - 1, a + 1] o

/-- Offsets 0,1,2 mean minus, zero, plus; the Boolean is the printed exponent c. -/
def coordinates (i : Fin 3 × Bool) (j : Fin 3) (a : ZMod m) : ZMod m :=
  ![a, second a i.1, if i.2 then tau (thirdBase a i.1) else thirdBase a i.1] j

def windowStart (a : ZMod m) (o : Fin 3) : ZMod m := ![a - 1, a - 2, a] o

theorem thirdBase_eq_start (a : ZMod m) (o : Fin 3) :
    thirdBase a o = windowStart a o + 1 := by
  fin_cases o <;> dsimp [thirdBase, windowStart] <;> ring

theorem first_window (a : ZMod m) (o : Fin 3) :
    ∃ t : Fin 4, a = windowStart a o + (t.val : ZMod m) := by
  fin_cases o
  · exact ⟨1, by dsimp [windowStart]; ring⟩
  · exact ⟨2, by dsimp [windowStart]; ring⟩
  · exact ⟨0, by dsimp [windowStart]; ring⟩

theorem second_window (a : ZMod m) (o : Fin 3) :
    ∃ t : Fin 4, second a o = windowStart a o + (t.val : ZMod m) := by
  fin_cases o
  · exact ⟨0, by dsimp [windowStart, second]; ring⟩
  · exact ⟨2, by dsimp [windowStart, second]; ring⟩
  · exact ⟨1, by dsimp [windowStart, second]; ring⟩

theorem third_window (hm : 3 ≤ m) (c : Bool) (a : ZMod m) (o : Fin 3) :
    ∃ t : Fin 4, (if c then tau (thirdBase a o) else thirdBase a o) =
      windowStart a o + (t.val : ZMod m) := by
  cases c with
  | false =>
    refine ⟨1, ?_⟩
    simpa using thirdBase_eq_start a o
  | true =>
    rcases tau_step hm (thirdBase a o) with h | h | h
    · refine ⟨0, ?_⟩
      simpa using (show tau (thirdBase a o) = windowStart a o + 0 by
        rw [h, thirdBase_eq_start]
        ring)
    · refine ⟨2, ?_⟩
      simpa using (show tau (thirdBase a o) = windowStart a o + 2 by
        rw [h, thirdBase_eq_start]
        ring)
    · refine ⟨3, ?_⟩
      simpa using (show tau (thirdBase a o) = windowStart a o + 3 by
        rw [h, thirdBase_eq_start]
        ring)

/-- All three original path labels lie in one cyclic interval of at most four
consecutive residues, including wraparound. -/
theorem coordinates_locality (hm : 3 ≤ m) (i : Fin 3 × Bool) (a : ZMod m) :
    ∃ s : ZMod m, ∀ j : Fin 3, ∃ t : Fin 4,
      coordinates i j a = s + (t.val : ZMod m) := by
  refine ⟨windowStart a i.1, ?_⟩
  intro j
  fin_cases j
  · exact first_window a i.1
  · exact second_window a i.1
  · exact third_window hm i.2 a i.1

theorem second_difference (i : Fin 3 × Bool) (a : ZMod m) :
    coordinates i 1 a - a ∈ ({-1, 0, 1} : Finset (ZMod m)) := by
  rcases i with ⟨o, c⟩
  fin_cases o <;> dsimp [coordinates, second] <;> ring_nf <;> simp

theorem third_difference (hm : 3 ≤ m) (i : Fin 3 × Bool) (a : ZMod m) :
    coordinates i 2 a - a ∈ ({-2, -1, 0, 1, 2, 3} : Finset (ZMod m)) := by
  rcases i with ⟨o, c⟩
  obtain ⟨t, ht⟩ := third_window hm c a o
  change (if c then tau (thirdBase a o) else thirdBase a o) - a ∈ _
  rw [ht]
  fin_cases o <;> fin_cases t <;> dsimp [windowStart] <;> ring_nf <;> simp

/-- The hypergraph specified by the original six cyclic formulas. This file
proves its locality, without identifying it with a grafted existence witness. -/
def graph : Hypergraph (Fin 3 × ZMod m) := coordinateHypergraph coordinates

theorem graph_locality (hm : 3 ≤ m) {e : Finset (Fin 3 × ZMod m)} (he : e ∈ graph) :
    ∃ s : ZMod m, ∀ v ∈ e, ∃ t : Fin 4, v.2 = s + (t.val : ZMod m) := by
  obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨s, hs⟩ := coordinates_locality hm i a
  refine ⟨s, ?_⟩
  intro v hv
  have hv' : v.2 = coordinates i v.1 a :=
    (mem_tupleEdge (x := fun j => coordinates i j a)).mp hv
  obtain ⟨t, ht⟩ := hs v.1
  exact ⟨t, hv'.trans ht⟩

end RigidGHZ.Supplement.SixCyclic
