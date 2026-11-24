module

public import RigidGHZ.Basic

/-! The elementary exact value at matching size one. -/

@[expose] public section

namespace RigidGHZ.Finite

def singleGraph (r : ℕ) : Hypergraph (Fin r) := {Finset.univ}

theorem single_uniform (r : ℕ) : Uniform (singleGraph r) r := by
  intro e he
  have heq : e = Finset.univ := Finset.mem_singleton.mp he
  simp only [heq, Finset.card_univ, Fintype.card_fin]

theorem single_perfect (r : ℕ) : PerfectMatching (singleGraph r) (singleGraph r) := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro v
  simp [singleGraph, Finset.filter_singleton]

def singleFamily (r : ℕ) (hr : 1 ≤ r) : RigidFamily (singleGraph r) (Fin 1) where
  matching := fun _ => singleGraph r
  perfect := fun _ => single_perfect r
  edge_disjoint := by
    intro i j hne
    exact (hne (Subsingleton.elim i j)).elim
  covers := by simp
  complete := by
    intro M hM
    have hne : M.Nonempty := by
      obtain ⟨e, he, _⟩ := hM.existsUnique_edge (⟨0, by omega⟩ : Fin r)
      exact ⟨e, he.1⟩
    have heq : M = singleGraph r := by
      obtain ⟨e, he⟩ := hne
      have heu : e = Finset.univ := Finset.mem_singleton.mp (hM.subset he)
      apply Finset.Subset.antisymm hM.subset
      intro f hf
      have hfu : f = Finset.univ := Finset.mem_singleton.mp hf
      simpa only [hfu, heu] using he
    exact ⟨0, heq⟩

theorem single_rigid (r : ℕ) (hr : 1 ≤ r) : IsRigid (singleGraph r) 1 :=
  ⟨singleFamily r hr⟩

theorem single_vertex_size_upper {r d : ℕ} (hr : 1 ≤ r)
    {H : Hypergraph (Fin r)} (hU : Uniform H r) (hR : IsRigid H d) : d ≤ 1 := by
  have hsub : H ⊆ singleGraph r := by
    intro e he
    apply Finset.mem_singleton.mpr
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ e)
    simpa using (hU e he).ge
  obtain ⟨R⟩ := hR
  have hdeg := R.regular (⟨0, by omega⟩ : Fin r)
  have hle : degree H (⟨0, by omega⟩ : Fin r) ≤ H.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard : H.card ≤ 1 := by
    simpa [singleGraph] using Finset.card_le_card hsub
  simpa only [Fintype.card_fin, hdeg] using hle.trans hcard

theorem single_edge_exact (r : ℕ) (hr : 1 ≤ r) :
    (∃ H : Hypergraph (Fin r), Uniform H r ∧ IsRigid H 1) ∧
    (∀ (H : Hypergraph (Fin r)) (d : ℕ), Uniform H r → IsRigid H d → d ≤ 1) :=
  ⟨⟨singleGraph r, single_uniform r, single_rigid r hr⟩,
    fun _ _ hU hR => single_vertex_size_upper hr hU hR⟩

end RigidGHZ.Finite
