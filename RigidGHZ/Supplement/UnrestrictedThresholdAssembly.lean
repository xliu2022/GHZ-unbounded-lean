module

public import RigidGHZ.Supplement.BalancedThresholdAssembly

/-! Unrestricted versions of the supplementary threshold arithmetic. -/

@[expose] public section

namespace RigidGHZ.Supplement.ThresholdAssembly

abbrev FreeSeed (m d : ℕ) := BoundedUnrestricted 3 m d (fun _ => d)
abbrev GraftSeed (m d : ℕ) := BoundedRigid 3 m d (fun _ => d)

theorem twelve_unrestricted_odd_progression
    (h3 : FreeSeed 3 12) (h13 : GraftSeed 13 12) (h19 : GraftSeed 19 12)
    (h23 : GraftSeed 23 12) (h29 : GraftSeed 29 12) (q : ℕ) :
    FreeSeed (19 + 2 * q) 12 := by
  have h21 : FreeSeed 21 12 := h3.graft h19 (by decide) (by decide) (by decide)
  have h25 : FreeSeed 25 12 := h3.graft h23 (by decide) (by decide) (by decide)
  have h27 : FreeSeed 27 12 := (h3.graft h13 (by decide) (by decide) (by decide)).graft
    h13 (by decide) (by decide) (by decide)
  apply BoundedUnrestricted.stride_window (a := 6) (by decide) (by decide) (by decide)
    h13 (q := q)
  intro i
  fin_cases i
  · exact h19.to_unrestricted
  · exact h21
  · exact h23.to_unrestricted
  · exact h25
  · exact h27
  · exact h29.to_unrestricted

theorem twelve_unrestricted_even_progression
    (h4 : FreeSeed 4 12) (h6 : FreeSeed 6 12)
    (h13 : GraftSeed 13 12) (h19 : GraftSeed 19 12)
    (h23 : GraftSeed 23 12) (h29 : GraftSeed 29 12) (q : ℕ) :
    FreeSeed (22 + 2 * q) 12 := by
  have h22 : FreeSeed 22 12 := h4.graft h19 (by decide) (by decide) (by decide)
  have h24 : FreeSeed 24 12 := h6.graft h19 (by decide) (by decide) (by decide)
  have h26 : FreeSeed 26 12 := h4.graft h23 (by decide) (by decide) (by decide)
  have h28 : FreeSeed 28 12 := h6.graft h23 (by decide) (by decide) (by decide)
  have h30 : FreeSeed 30 12 := (h6.graft h13 (by decide) (by decide) (by decide)).graft
    h13 (by decide) (by decide) (by decide)
  have h32 : FreeSeed 32 12 := h4.graft h29 (by decide) (by decide) (by decide)
  apply BoundedUnrestricted.stride_window (a := 6) (by decide) (by decide) (by decide)
    h13 (q := q)
  intro i
  fin_cases i
  · exact h22
  · exact h24
  · exact h26
  · exact h28
  · exact h30
  · exact h32

theorem twelve_unrestricted
    (h3 : FreeSeed 3 12) (h4 : FreeSeed 4 12) (h6 : FreeSeed 6 12)
    (h13 : GraftSeed 13 12) (h19 : GraftSeed 19 12)
    (h23 : GraftSeed 23 12) (h29 : GraftSeed 29 12) (m : ℕ) (hm : 21 ≤ m) :
    FreeSeed m 12 := by
  have hd := Nat.mod_add_div m 2
  have hr := Nat.mod_lt m (by decide : 0 < 2)
  by_cases heven : m % 2 = 0
  · have h := twelve_unrestricted_even_progression h4 h6 h13 h19 h23 h29 (m / 2 - 11)
    have he : 22 + 2 * (m / 2 - 11) = m := by omega
    simpa only [he] using h
  · have h := twelve_unrestricted_odd_progression h3 h13 h19 h23 h29 (m / 2 - 9)
    have he : 19 + 2 * (m / 2 - 9) = m := by omega
    simpa only [he] using h

/-- The ten base sizes 2 through 11, followed by grafts adding ten, give every
matching size at least two. -/
theorem ten_unrestricted (seed : GraftSeed 11 10)
    (initial : ∀ i : Fin 10, FreeSeed (2 + i.val) 10)
    (m : ℕ) (hm : 2 ≤ m) : FreeSeed m 10 := by
  have h := BoundedUnrestricted.stride_window (stride := 1) (base := 2)
    (by decide : 0 < 10) (by decide) (by decide) seed
    (by simpa only [Nat.one_mul] using initial) (m - 2)
  have he : 2 + 1 * (m - 2) = m := by omega
  simpa only [he] using h

end RigidGHZ.Supplement.ThresholdAssembly
