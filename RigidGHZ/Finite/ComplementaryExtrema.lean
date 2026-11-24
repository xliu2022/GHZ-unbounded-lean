module

public import RigidGHZ.Finite.TwoEdgeCertificate
public import RigidGHZ.Construction.CyclicBaseline
public import RigidGHZ.Relabel
public import RigidGHZ.UpperBounds.Corollaries

/-! The exact elementary extrema at matching size two, for every uniformity.
The unrestricted witness is the complete uniform hypergraph: its perfect
matchings are precisely complementary pairs, whose number is half its edge
count. The balanced witness is the checked binary cyclic construction. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Finite

variable {V : Type*} [Fintype V] [DecidableEq V]

def completeUniform (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : Hypergraph V :=
  Finset.univ.powersetCard r

theorem mem_completeUniform {r : ℕ} {e : Finset V} :
    e ∈ completeUniform V r ↔ e.card = r := by
  simp [completeUniform]

theorem completeUniform_uniform (r : ℕ) : Uniform (completeUniform V r) r :=
  fun _ he => mem_completeUniform.mp he

theorem completeUniform_card (r : ℕ) :
    (completeUniform V r).card = (Fintype.card V).choose r := by
  simp [completeUniform]

theorem complement_pair_perfect {r : ℕ} (hV : Fintype.card V = 2 * r)
    {e : Finset V} (he : e.card = r) :
    PerfectMatching (completeUniform V r) {e, Finset.univ \ e} := by
  classical
  have hc : (Finset.univ \ e).card = r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ, hV, he]
    omega
  apply PerfectMatching.of_existsUnique
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact mem_completeUniform.mpr he
    · have hfe := Finset.mem_singleton.mp hf
      exact mem_completeUniform.mpr (hfe ▸ hc)
  · intro v
    by_cases hv : v ∈ e
    · refine ⟨e, ⟨by simp, hv⟩, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf.1 with hfe | hfe
      · exact hfe
      · have hfe := Finset.mem_singleton.mp hfe
        subst f
        exact ((Finset.mem_sdiff.mp hf.2).2 hv).elim
    · refine ⟨Finset.univ \ e, ⟨by simp, by simp [hv]⟩, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf.1 with hfe | hfe
      · subst f
        exact (hv hf.2).elim
      · exact Finset.mem_singleton.mp hfe

/-- A chosen edge determines its entire perfect matching at matching size two. -/
theorem two_matching_eq_complement_pair {H M : Hypergraph V} {r : ℕ}
    (hr : 0 < r) (hV : Fintype.card V = 2 * r) (hH : Uniform H r)
    (hM : PerfectMatching H M) {e : Finset V} (he : e ∈ M) :
    M = {e, Finset.univ \ e} := by
  have hm := hM.card_mul_eq hH
  rw [hV] at hm
  have hc : M.card = 2 := Nat.eq_of_mul_eq_mul_right hr hm
  obtain ⟨a, b, hab, hMab⟩ := Finset.card_eq_two.mp hc
  subst M
  have heab : e = a ∨ e = b := by simpa using he
  rcases heab with rfl | rfl
  · rw [second_edge_eq_complement hM hab]
  · have hba : PerfectMatching H {e, a} := by
      simpa only [Finset.pair_comm] using hM
    have ha := second_edge_eq_complement hba hab.symm
    rw [ha]
    exact Finset.pair_comm _ _

def allPerfectMatchings (H : Hypergraph V) : Finset (Hypergraph V) := by
  classical
  exact Finset.univ.filter (PerfectMatching H)

theorem mem_allPerfectMatchings {H M : Hypergraph V} :
    M ∈ allPerfectMatchings H ↔ PerfectMatching H M := by
  classical
  simp [allPerfectMatchings]

def completeComplementFamily (r : ℕ) (hr : 0 < r)
    (hV : Fintype.card V = 2 * r) :
    RigidFamily (completeUniform V r) (allPerfectMatchings (completeUniform V r)) where
  matching := fun i => i.val
  perfect := fun i => mem_allPerfectMatchings.mp i.property
  edge_disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hi := two_matching_eq_complement_pair hr hV (completeUniform_uniform r)
      (mem_allPerfectMatchings.mp i.property) hei
    have hj := two_matching_eq_complement_pair hr hV (completeUniform_uniform r)
      (mem_allPerfectMatchings.mp j.property) hej
    exact hij (Subtype.ext (hi.trans hj.symm))
  covers := by
    ext e
    constructor
    · intro he
      have hM := complement_pair_perfect hV (mem_completeUniform.mp he)
      let i : allPerfectMatchings (completeUniform V r) :=
        ⟨{e, Finset.univ \ e}, mem_allPerfectMatchings.mpr hM⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [i]⟩
    · intro he
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
      exact (mem_allPerfectMatchings.mp i.property).subset hei
  complete := fun M hM => ⟨⟨M, mem_allPerfectMatchings.mpr hM⟩, rfl⟩

theorem completeUniform_rigid {r : ℕ} (hr : 0 < r)
    (hV : Fintype.card V = 2 * r) :
    IsRigid (completeUniform V r) ((2 * r).choose r / 2) := by
  classical
  let R := completeComplementFamily (V := V) r hr hV
  have hc := R.card_edges (completeUniform_uniform r) hr
    (show Fintype.card V = r * 2 by omega)
  rw [completeUniform_card, hV] at hc
  have hdim : Fintype.card (allPerfectMatchings (completeUniform V r)) =
      (2 * r).choose r / 2 := by omega
  let e := Fintype.equivFin (allPerfectMatchings (completeUniform V r))
  have hR : IsRigid (completeUniform V r)
      (Fintype.card (allPerfectMatchings (completeUniform V r))) := ⟨R.reindex e.symm⟩
  simpa only [hdim] using hR

/-- Universal upper bound for an arbitrary ordinary rigid hypergraph on `2r` vertices. -/
theorem two_edge_upper {H : Hypergraph V} {r d : ℕ} (hr : 0 < r)
    (hV : Fintype.card V = 2 * r) (hH : Uniform H r) (hR : IsRigid H d) :
    d ≤ (2 * r).choose r / 2 := by
  have hsub : H ⊆ completeUniform V r := fun _ he => mem_completeUniform.mpr (hH _ he)
  have hc := Finset.card_le_card hsub
  rw [completeUniform_card, hV] at hc
  obtain ⟨R⟩ := hR
  have hcount := R.card_edges hH hr (show Fintype.card V = r * 2 by omega)
  simp only [Fintype.card_fin] at hcount
  omega

/-- `f_r(2r) = (1/2) * choose(2r,r)`, expressed by attainment and a universal bound. -/
theorem two_edge_exact (r : ℕ) (hr : 1 ≤ r) :
    (∃ H : Hypergraph (Fin (2 * r)), Uniform H r ∧ IsRigid H ((2 * r).choose r / 2)) ∧
    (∀ (H : Hypergraph (Fin (2 * r))) (d : ℕ), Uniform H r → IsRigid H d →
      d ≤ (2 * r).choose r / 2) := by
  constructor
  · exact ⟨completeUniform (Fin (2 * r)) r, completeUniform_uniform r,
      completeUniform_rigid (by omega) (by simp)⟩
  · intro H d hH hR
    exact two_edge_upper (by omega) (by simp) hH hR

theorem balanced_two_upper {H : Hypergraph V} {r d : ℕ} (hr : 2 ≤ r)
    (hP : BalancedPartite H r 2) (hR : IsRigid H d) : d ≤ 2 ^ (r - 1) := by
  have h := UpperBounds.balanced_partite_harmonic_bound hr hR hP
  rw [UpperBounds.beta_two, mul_one] at h
  exact_mod_cast h

/-- `g_r(2) = 2^(r-1)` on the canonical balanced vertex set. -/
theorem balanced_two_exact (r : ℕ) (hr : 2 ≤ r) :
    (∃ H : Hypergraph (Fin r × Fin 2), Uniform H r ∧ BalancedPartite H r 2 ∧
      IsRigid H (2 ^ (r - 1))) ∧
    (∀ (H : Hypergraph (Fin r × Fin 2)) (d : ℕ),
      BalancedPartite H r 2 → IsRigid H d → d ≤ 2 ^ (r - 1)) := by
  constructor
  · obtain ⟨H, hU, hP, hR⟩ := Cyclic.baseline r 2 hr (by decide)
    obtain ⟨f, hf⟩ := hP.canonical
    refine ⟨relabelHypergraph f H, hU.relabel f, ?_, hR.relabel f⟩
    simpa only [Fintype.card_fin] using balancedPartite_of_transversal _ hf
  · exact fun H d hP hR => balanced_two_upper hr hP hR

end RigidGHZ.Finite
