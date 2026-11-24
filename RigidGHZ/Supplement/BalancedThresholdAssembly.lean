module

public import RigidGHZ.Supplement.BoundedHelpers
public import Mathlib.Tactic.FinCases

/-! The numerical grafting arguments in Supplementary Theorem S7.1.
The concrete certified seed inputs are supplied in BalancedThresholds. -/

@[expose] public section

namespace RigidGHZ.Supplement.ThresholdAssembly

abbrev PairSeed (m d : ℕ) := BoundedRigid 3 m d (pairBounds d 2)

theorem eight (h5 : PairSeed 5 8) (h7 : PairSeed 7 8)
    (h8 : PairSeed 8 8) (h10 : PairSeed 10 8) (m : ℕ) (hm : 7 ≤ m) :
    PairSeed m 8 := by
  have h9 : PairSeed 9 8 := h5.graft h5 (by decide) (by decide) (by decide)
  have initial : ∀ i : Fin 4, PairSeed (7 + 1 * i.val) 8 := by
    intro i
    fin_cases i
    · exact h7
    · exact h8
    · exact h9
    · exact h10
  have h := BoundedRigid.stride_window (stride := 1) (base := 7)
    (by decide : 0 < 4) (by decide) (by decide) h5 initial (m - 7)
  have he : 7 + 1 * (m - 7) = m := by omega
  simpa only [he] using h

theorem ten_odd_progression (h11 : PairSeed 11 10) (h13 : PairSeed 13 10)
    (h17 : PairSeed 17 10) (h19 : PairSeed 19 10) (q : ℕ) :
    PairSeed (17 + 2 * q) 10 := by
  have h21 : PairSeed 21 10 := h11.graft h11 (by decide) (by decide) (by decide)
  have h23 : PairSeed 23 10 := h11.graft h13 (by decide) (by decide) (by decide)
  have h25 : PairSeed 25 10 := h13.graft h13 (by decide) (by decide) (by decide)
  apply BoundedRigid.stride_window (a := 5) (by decide) (by decide) (by decide) h11
    (q := q)
  intro i
  fin_cases i
  · exact h17
  · exact h19
  · exact h21
  · exact h23
  · exact h25

theorem ten_odd (h11 : PairSeed 11 10) (h13 : PairSeed 13 10)
    (h17 : PairSeed 17 10) (h19 : PairSeed 19 10)
    (m : ℕ) (hm : 17 ≤ m) (ho : Odd m) : PairSeed m 10 := by
  obtain ⟨u, hu⟩ := ho
  have h := ten_odd_progression h11 h13 h17 h19 (u - 8)
  have he : 17 + 2 * (u - 8) = m := by omega
  simpa only [he] using h

theorem ten_even_progression (h11 : PairSeed 11 10) (h13 : PairSeed 13 10)
    (h17 : PairSeed 17 10) (h19 : PairSeed 19 10)
    (h22 : PairSeed 22 10) (h26 : PairSeed 26 10) (q : ℕ) :
    PairSeed (32 + 2 * q) 10 := by
  have h32 : PairSeed 32 10 := h22.graft h11 (by decide) (by decide) (by decide)
  have h34 : PairSeed 34 10 := h22.graft h13 (by decide) (by decide) (by decide)
  have h36 : PairSeed 36 10 := h26.graft h11 (by decide) (by decide) (by decide)
  have h38 : PairSeed 38 10 := h22.graft h17 (by decide) (by decide) (by decide)
  have h40 : PairSeed 40 10 := h22.graft h19 (by decide) (by decide) (by decide)
  apply BoundedRigid.stride_window (a := 5) (by decide) (by decide) (by decide) h11
    (q := q)
  intro i
  fin_cases i
  · exact h32
  · exact h34
  · exact h36
  · exact h38
  · exact h40

theorem ten (h11 : PairSeed 11 10) (h13 : PairSeed 13 10)
    (h17 : PairSeed 17 10) (h19 : PairSeed 19 10)
    (h22 : PairSeed 22 10) (h26 : PairSeed 26 10) (m : ℕ) (hm : 31 ≤ m) :
    PairSeed m 10 := by
  have hd := Nat.mod_add_div m 2
  have hr := Nat.mod_lt m (by decide : 0 < 2)
  by_cases heven : m % 2 = 0
  · have h := ten_even_progression h11 h13 h17 h19 h22 h26 (m / 2 - 16)
    have he : 32 + 2 * (m / 2 - 16) = m := by omega
    simpa only [he] using h
  · exact ten_odd h11 h13 h17 h19 m (by omega) ⟨m / 2, by omega⟩

theorem twelve_odd_progression (h13 : PairSeed 13 12) (h19 : PairSeed 19 12)
    (h23 : PairSeed 23 12) (h29 : PairSeed 29 12) (h39 : PairSeed 39 12) (q : ℕ) :
    PairSeed (35 + 2 * q) 12 := by
  have h35 : PairSeed 35 12 := h13.graft h23 (by decide) (by decide) (by decide)
  have h37 : PairSeed 37 12 := h19.graft h19 (by decide) (by decide) (by decide)
  have h41 : PairSeed 41 12 := h13.graft h29 (by decide) (by decide) (by decide)
  have h43 : PairSeed 43 12 := (h13.graft h13 (by decide) (by decide) (by decide)).graft
    h19 (by decide) (by decide) (by decide)
  have h45 : PairSeed 45 12 := h23.graft h23 (by decide) (by decide) (by decide)
  apply BoundedRigid.stride_window (a := 6) (by decide) (by decide) (by decide) h13
    (q := q)
  intro i
  fin_cases i
  · exact h35
  · exact h37
  · exact h39
  · exact h41
  · exact h43
  · exact h45

theorem twelve_odd (h13 : PairSeed 13 12) (h19 : PairSeed 19 12)
    (h23 : PairSeed 23 12) (h29 : PairSeed 29 12) (h39 : PairSeed 39 12)
    (m : ℕ) (hm : 35 ≤ m) (ho : Odd m) : PairSeed m 12 := by
  obtain ⟨u, hu⟩ := ho
  have h := twelve_odd_progression h13 h19 h23 h29 h39 (u - 17)
  have he : 35 + 2 * (u - 17) = m := by omega
  simpa only [he] using h

theorem twelve_even_progression (h13 : PairSeed 13 12) (h19 : PairSeed 19 12)
    (h23 : PairSeed 23 12) (h29 : PairSeed 29 12)
    (h26 : PairSeed 26 12) (h46 : PairSeed 46 12) (h52 : PairSeed 52 12) (q : ℕ) :
    PairSeed (44 + 2 * q) 12 := by
  have h44 : PairSeed 44 12 := h26.graft h19 (by decide) (by decide) (by decide)
  have h48 : PairSeed 48 12 := h26.graft h23 (by decide) (by decide) (by decide)
  have h50 : PairSeed 50 12 := (h26.graft h13 (by decide) (by decide) (by decide)).graft
    h13 (by decide) (by decide) (by decide)
  have h54 : PairSeed 54 12 := h26.graft h29 (by decide) (by decide) (by decide)
  apply BoundedRigid.stride_window (a := 6) (by decide) (by decide) (by decide) h13
    (q := q)
  intro i
  fin_cases i
  · exact h44
  · exact h46
  · exact h48
  · exact h50
  · exact h52
  · exact h54

theorem twelve (h13 : PairSeed 13 12) (h19 : PairSeed 19 12)
    (h23 : PairSeed 23 12) (h29 : PairSeed 29 12) (h39 : PairSeed 39 12)
    (h26 : PairSeed 26 12) (h46 : PairSeed 46 12) (h52 : PairSeed 52 12)
    (m : ℕ) (hm : 43 ≤ m) : PairSeed m 12 := by
  have hd := Nat.mod_add_div m 2
  have hr := Nat.mod_lt m (by decide : 0 < 2)
  by_cases heven : m % 2 = 0
  · have h := twelve_even_progression h13 h19 h23 h29 h26 h46 h52 (m / 2 - 22)
    have he : 44 + 2 * (m / 2 - 22) = m := by omega
    simpa only [he] using h
  · exact twelve_odd h13 h19 h23 h29 h39 m (by omega) ⟨m / 2, by omega⟩

end RigidGHZ.Supplement.ThresholdAssembly
