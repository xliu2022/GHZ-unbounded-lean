module

public import RigidGHZ.Supplement.Grafting
public import RigidGHZ.Supplement.MatchingRestriction

/-! The minimum-dimension consequences of the grafting theorem. -/

@[expose] public section

namespace RigidGHZ.Supplement

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

 theorem grafting_min {H : Hypergraph V} {S : Hypergraph W} {r m q d e : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) (hcard : Fintype.card V = r * m)
    (hH : Uniform H r) (hR : IsRigid H d) (hS : BalancedPartite S r q)
    (hRS : IsRigid S e) :
    ∃ G : Hypergraph (Fin (r * (m + q - 1))), Uniform G r ∧ IsRigid G (min d e) ∧
      ∀ j : ℕ, 1 ≤ j → maxDegree G j ≤ max (maxDegree H j) (maxDegree S j) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  obtain ⟨f, hf⟩ := hS.canonical
  letI : Nonempty W := ⟨f.symm (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨RH⟩ := hR
  obtain ⟨RS⟩ := hRS
  obtain ⟨K, hKH, ⟨RK⟩⟩ := RH.exists_restriction (d := min d e) (by simpa only [Fintype.card_fin] using Nat.min_le_left d e)
  obtain ⟨T, hTS, ⟨RT⟩⟩ := RS.exists_restriction (d := min d e) (by simpa only [Fintype.card_fin] using Nat.min_le_right d e)
  obtain ⟨G, hUG, ⟨RG⟩, hDG⟩ := grafting hr hm hq hcard (hH.mono hKH) RK (hS.mono hTS) RT
  refine ⟨G, hUG, ⟨RG⟩, ?_⟩
  intro j hj
  exact (hDG j hj).trans (max_le_max (maxDegree_mono hKH j) (maxDegree_mono hTS j))

 theorem grafting_balanced_min {H : Hypergraph V} {S : Hypergraph W} {r m q d e : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hH : BalancedPartite H r m) (hR : IsRigid H d)
    (hS : BalancedPartite S r q) (hRS : IsRigid S e) :
    ∃ G : Hypergraph (Fin r × Fin (m + q - 1)), Uniform G r ∧
      BalancedPartite G r (m + q - 1) ∧ IsRigid G (min d e) ∧
      ∀ j : ℕ, 1 ≤ j → maxDegree G j ≤ max (maxDegree H j) (maxDegree S j) := by
  classical
  obtain ⟨f, hf⟩ := hH.canonical
  obtain ⟨g, hg⟩ := hS.canonical
  letI : Nonempty V := ⟨f.symm (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  letI : Nonempty W := ⟨g.symm (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨RH⟩ := hR
  obtain ⟨RS⟩ := hRS
  obtain ⟨K, hKH, ⟨RK⟩⟩ := RH.exists_restriction (d := min d e) (by simpa only [Fintype.card_fin] using Nat.min_le_left d e)
  obtain ⟨T, hTS, ⟨RT⟩⟩ := RS.exists_restriction (d := min d e) (by simpa only [Fintype.card_fin] using Nat.min_le_right d e)
  obtain ⟨G, hUG, hPG, ⟨RG⟩, hDG⟩ := grafting_balanced hr hm hq
    (hH.mono hKH) RK (hS.mono hTS) RT
  refine ⟨G, hUG, hPG, ⟨RG⟩, ?_⟩
  intro j hj
  exact (hDG j hj).trans (max_le_max (maxDegree_mono hKH j) (maxDegree_mono hTS j))

end RigidGHZ.Supplement
