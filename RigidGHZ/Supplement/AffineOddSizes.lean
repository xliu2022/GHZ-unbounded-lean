module

public import RigidGHZ.Supplement.AffineSmallSeeds
public import RigidGHZ.Supplement.AffineDegrees
public import RigidGHZ.Supplement.GraftSemigroup

/-! The small affine seeds, doubled and grafted, supply the supplementary
six- and eight-matching inputs. Grafting gives eight at every odd part size >= 5,
a slightly stronger range than the printed coprime-to-six affine corollary. -/

@[expose] public section

namespace RigidGHZ.Supplement.Affine

 theorem six_at_three : BoundedRigid 3 3 6 (pairBounds 6 2) := by
  obtain ⟨H, hU, hP, hR, hD⟩ := seed3.doubling (by decide) (by decide) (1 : ZMod 3) isUnit_one
  have hR' : IsRigid H 6 := by simpa only [shifts3_card] using hR
  exact boundedRigid_of_pair_bound hU hP hR' hD

 theorem eight_at_five : BoundedRigid 3 5 8 (pairBounds 8 2) := by
  obtain ⟨H, hU, hP, hR, hD⟩ := seed5.doubling (by decide) (by decide) (1 : ZMod 5) isUnit_one
  have hR' : IsRigid H 8 := by simpa only [shifts5_card] using hR
  exact boundedRigid_of_pair_bound hU hP hR' hD

 theorem eight_at_seven : BoundedRigid 3 7 8 (pairBounds 8 2) := by
  obtain ⟨H, hU, hP, hR, hD⟩ := seed7.doubling (by decide) (by decide) (1 : ZMod 7) isUnit_one
  have hR' : IsRigid H 8 := by simpa only [shifts7_card] using hR
  exact boundedRigid_of_pair_bound hU hP hR' hD

 theorem eight_bounded_odd (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    BoundedRigid 3 m 8 (pairBounds 8 2) := by
  revert hm hodd
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hodd
    by_cases hsmall : m < 9
    · have hm57 : m = 5 ∨ m = 7 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hm57 with rfl | rfl
      · exact eight_at_five
      · exact eight_at_seven
    · have hm4 : 5 ≤ m - 4 := by omega
      have hodd4 : Odd (m - 4) := by
        obtain ⟨k, hk⟩ := hodd
        refine ⟨k - 2, ?_⟩
        omega
      have h := (ih (m - 4) (by omega) hm4 hodd4).graft eight_at_five
        (by decide) (by omega) (by decide)
      have heq : m - 4 + 5 - 1 = m := by omega
      simpa only [heq] using h

/-- Ordinary balanced eight-rigid triples with maximum pair codegree two. -/
 theorem eight_odd (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ maxDegree H 2 ≤ 2 := by
  obtain ⟨H, hU, hP, hR, hD⟩ := eight_bounded_odd m hm hodd
  exact ⟨H, hU, hP, hR, by simpa [pairBounds] using hD 2 (by decide)⟩

/-- The supplementary coprime-to-six size range follows in particular. -/
 theorem eight_coprime_six (m : ℕ) (hm : 5 ≤ m) (hcop : m.Coprime 6) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ maxDegree H 2 ≤ 2 := by
  apply eight_odd m hm
  exact (Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hcop).odd_of_right

end RigidGHZ.Supplement.Affine
