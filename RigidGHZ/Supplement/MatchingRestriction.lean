module

public import RigidGHZ.Supplement.DegreeRelabel

/-! Restricting the prescribed family preserves all upper codegree bounds. -/

@[expose] public section

namespace RigidGHZ

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

 theorem Uniform.mono {H K : Hypergraph V} {r : ℕ} (h : Uniform H r) (hK : K ⊆ H) : Uniform K r :=
  fun e he => h e (hK he)

 theorem BalancedPartite.mono {H K : Hypergraph V} {r m : ℕ}
    (h : BalancedPartite H r m) (hK : K ⊆ H) : BalancedPartite K r m := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨c, hc, fun e heK => he e (hK heK)⟩

 theorem RigidFamily.exists_restriction [Nonempty V] {H : Hypergraph V}
    (R : RigidFamily H I) {d : ℕ} (hd : d ≤ Fintype.card I) :
    ∃ K : Hypergraph V, K ⊆ H ∧ IsRigid K d := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ)
    (show d ≤ (Finset.univ : Finset I).card by simpa using hd)
  let e : Fin d ≃ ↥s := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  refine ⟨s.biUnion R.matching, ?_, ⟨(R.restrict s).reindex e⟩⟩
  intro f hf
  obtain ⟨i, hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact (R.perfect i).subset hfi

namespace Supplement

open UpperBounds

 theorem codegree_mono {H K : Hypergraph V} (hK : K ⊆ H) (X : Finset V) :
    codegree K X ≤ codegree H X := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨heK, hXe⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hK heK, hXe⟩

 theorem maxDegree_mono {H K : Hypergraph V} (hK : K ⊆ H) (j : ℕ) :
    maxDegree K j ≤ maxDegree H j := by
  apply maxDegree_le
  intro X hX
  have hb : codegree H X ≤ maxDegree H j := by simpa only [hX] using codegree_le_maxDegree H X
  exact (codegree_mono hK X).trans hb

end Supplement
end RigidGHZ
