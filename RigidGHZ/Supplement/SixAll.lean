module

public import RigidGHZ.Supplement.SixSeeds
public import RigidGHZ.Supplement.GraftSemigroup

/-! Supplemental Theorem S1.4. We obtain the same existence and pair-codegree
conclusions by grafting the verified seeds of part sizes three and four, then
apply the proved dimension-doubling construction. -/

@[expose] public section

namespace RigidGHZ.Supplement

 theorem six_three_bounded : BoundedRigid 3 3 6 (pairBounds 6 2) := by
  apply boundedRigid_of_pair_bound Finite.six_uniform Finite.six_balanced_partite Finite.six_rigid
  apply maxDegree_le
  exact SixSeeds.three_pair_bound

 theorem six_four_bounded : BoundedRigid 3 4 6 (pairBounds 6 2) := by
  apply boundedRigid_of_pair_bound SixSeeds.four_uniform SixSeeds.four_balanced SixSeeds.four_rigid
  apply maxDegree_le
  exact SixSeeds.four_pair_bound

/-- Six rigid matching classes at every part size at least three, with maximum
pair codegree two. Grafting the size-three seed increases the part size by two. -/
theorem six_bounded (m : ℕ) (hm : 3 ≤ m) : BoundedRigid 3 m 6 (pairBounds 6 2) := by
  revert hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases h3 : m = 3
    · subst m; exact six_three_bounded
    by_cases h4 : m = 4
    · subst m; exact six_four_bounded
    have hm5 : 5 ≤ m := by omega
    have hb := ih (m - 2) (by omega) (by omega)
    have hg := hb.graft six_three_bounded (by decide) (by omega) (by decide)
    have he : m - 2 + 3 - 1 = m := by omega
    simpa only [he] using hg

 theorem six_at_every_size (m : ℕ) (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 6 ∧ H.card = 6 * m ∧ maxDegree H 2 ≤ 2 := by
  obtain ⟨H, hU, hP, ⟨R⟩, hD⟩ := six_bounded m hm
  refine ⟨H, hU, hP, ⟨R⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using R.card_edges hU (by decide : 0 < 3)
      (show Fintype.card (Fin 3 × Fin m) = 3 * m by simp)
  · simpa [pairBounds] using hD 2 (by decide)

 theorem six_doubled (k m : ℕ) (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin (k + 3) × Fin m), Uniform H (k + 3) ∧
      BalancedPartite H (k + 3) m ∧ IsRigid H (6 * 2 ^ k) := by
  induction k with
  | zero =>
    obtain ⟨H, hU, hP, hR, hc, hD⟩ := six_at_every_size m hm
    exact ⟨H, hU, hP, by simpa using hR⟩
  | succ k ih =>
    obtain ⟨H, hU, hP, hR⟩ := ih
    obtain ⟨G, hUG, hPG, hRG⟩ := doubling (by omega : 2 ≤ k + 3) (by omega : 2 ≤ m) hP hR
    have he : k + 3 + 1 = k + 1 + 3 := by omega
    have hd : 2 * (6 * 2 ^ k) = 6 * 2 ^ (k + 1) := by rw [pow_succ]; ring
    exact ⟨G, by simpa only [he] using hUG, by simpa only [he] using hPG,
      by simpa only [hd] using hRG⟩

/-- The general lower bound in Supplemental Theorem S1.4. -/
theorem six_general (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧
      IsRigid H (3 * 2 ^ (r - 2)) := by
  induction r, hr using Nat.le_induction with
  | base =>
    obtain ⟨H, hU, hP, hR, hc, hD⟩ := six_at_every_size m hm
    exact ⟨H, hU, hP, by simpa using hR⟩
  | succ r hr ih =>
    obtain ⟨H, hU, hP, hR⟩ := ih
    obtain ⟨G, hUG, hPG, hRG⟩ := doubling (by omega : 2 ≤ r) (by omega : 2 ≤ m) hP hR
    have hd : 2 * (3 * 2 ^ (r - 2)) = 3 * 2 ^ (r + 1 - 2) := by
      rw [show r + 1 - 2 = (r - 2) + 1 by omega, pow_succ]
      ring
    exact ⟨G, hUG, hPG, by simpa only [hd] using hRG⟩

end RigidGHZ.Supplement
