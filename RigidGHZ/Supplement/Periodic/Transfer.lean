module

public import RigidGHZ.Supplement.Periodic.Basic

/-! Exact correspondence between ordinary perfect matchings and compatible
local configurations, including the period-one case. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
  [DecidableEq V] [DecidableEq E] [DecidableEq L]
  (D : Scheme V E) (σ : Equiv.Perm L) {A : L → Finset E}

 theorem incident_cases {v : V} {j : L} {g : Finset (V × L)}
    (hg : g ∈ D.selection σ A) (hv : (v, j) ∈ g) :
    (∃ e ∈ A j, v ∈ D.localPart e ∧ g = D.liftEdge σ e j) ∨
      (∃ e ∈ A (σ.symm j), v ∈ D.outgoing e ∧ g = D.liftEdge σ e (σ.symm j)) := by
  obtain ⟨k, e, he, rfl⟩ := (D.mem_selection σ A g).mp hg
  obtain ⟨hve, hj⟩ := (D.mem_liftEdge σ e k j v).mp hv
  by_cases ho : v ∈ D.outgoing e
  · have hjk : j = σ k := by simpa only [if_pos ho] using hj
    have hk : k = σ.symm j := by rw [hjk]; simp
    subst k
    exact Or.inr ⟨e, he, ho, rfl⟩
  · have hjk : j = k := by simpa only [if_neg ho] using hj
    subst k
    exact Or.inl ⟨e, he, (D.mem_localPart e v).mpr ⟨hve, ho⟩, rfl⟩

variable (hP : PerfectMatching (D.graph σ) (D.selection σ A))
include hP

 theorem matching_local_disjoint (j : L) :
    ∀ e ∈ A j, ∀ f ∈ A j, e ≠ f → Disjoint (D.localPart e) (D.localPart f) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have heP := (D.liftEdge_mem_selection σ A e j).mpr he
  have hfP := (D.liftEdge_mem_selection σ A f j).mpr hf
  have hsame := hP.edge_eq_of_vertex heP hfP
    (D.local_mem_liftEdge σ e j hve) (D.local_mem_liftEdge σ f j hvf)
  exact hef (D.edge_eq_of_lift_eq σ hsame)

 theorem matching_outgoing_disjoint (j : L) :
    ∀ e ∈ A j, ∀ f ∈ A j, e ≠ f → Disjoint (D.outgoing e) (D.outgoing f) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have heP := (D.liftEdge_mem_selection σ A e j).mpr he
  have hfP := (D.liftEdge_mem_selection σ A f j).mpr hf
  have hsame := hP.edge_eq_of_vertex heP hfP
    (D.outgoing_mem_liftEdge σ e j hve) (D.outgoing_mem_liftEdge σ f j hvf)
  exact hef (D.edge_eq_of_lift_eq σ hsame)

 theorem matching_state_eq (j : L) : D.output (A j) = D.input (A (σ j)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := (D.mem_output (A j) v).mp hv
    apply (D.mem_input (A (σ j)) v).mpr
    intro f hf hvf
    have hsame := hP.edge_eq_of_vertex
      ((D.liftEdge_mem_selection σ A e j).mpr he)
      ((D.liftEdge_mem_selection σ A f (σ j)).mpr hf)
      (D.outgoing_mem_liftEdge σ e j hve) (D.local_mem_liftEdge σ f (σ j) hvf)
    have hef : e = f := D.edge_eq_of_lift_eq σ hsame
    subst f
    exact ((D.mem_localPart e v).mp hvf).2 hve
  · intro hv
    obtain ⟨g, hg, hu⟩ := hP.existsUnique_edge (v, σ j)
    rcases D.incident_cases σ hg.1 hg.2 with ⟨e, he, hve, hge⟩ | ⟨e, he, hve, hge⟩
    · exact ((D.mem_input (A (σ j)) v).mp hv e he hve).elim
    · exact (D.mem_output (A j) v).mpr ⟨e, by simpa using he, hve⟩

 theorem matching_periodic : D.PeriodicConfig σ A := by
  refine ⟨?_, D.matching_state_eq σ hP⟩
  intro j
  refine ⟨D.matching_local_disjoint σ hP j, D.matching_outgoing_disjoint σ hP j, ?_⟩
  intro v hv
  have heq : D.output (A (σ.symm j)) = D.input (A j) := by
    simpa only [Equiv.apply_symm_apply] using D.matching_state_eq σ hP (σ.symm j)
  rw [← heq] at hv
  obtain ⟨e, he, hve⟩ := (D.mem_output _ _).mp hv
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hve⟩

omit hP

 theorem periodic_matching (hA : D.PeriodicConfig σ A) :
    PerfectMatching (D.graph σ) (D.selection σ A) := by
  classical
  apply PerfectMatching.of_existsUnique (D.selection_subset σ A)
  rintro ⟨v, j⟩
  have hprev : D.output (A (σ.symm j)) = D.input (A j) := by
    simpa only [Equiv.apply_symm_apply] using hA.2 (σ.symm j)
  by_cases hi : v ∈ D.input (A j)
  · have hout : v ∈ D.output (A (σ.symm j)) := by rwa [hprev]
    obtain ⟨e, he, hve⟩ := (D.mem_output _ _).mp hout
    refine ⟨D.liftEdge σ e (σ.symm j), ⟨?_, ?_⟩, ?_⟩
    · exact (D.liftEdge_mem_selection σ A e (σ.symm j)).mpr he
    · simpa only [Equiv.apply_symm_apply] using D.outgoing_mem_liftEdge σ e (σ.symm j) hve
    · intro g hg
      rcases D.incident_cases σ hg.1 hg.2 with ⟨f, hf, hvf, hgf⟩ | ⟨f, hf, hvf, hgf⟩
      · exact ((D.mem_input _ _).mp hi f hf hvf).elim
      · have hfe : f = e := by
          by_contra hne
          exact Finset.disjoint_left.mp ((hA.1 (σ.symm j)).2.1 f hf e he hne) hvf hve
        simpa only [hfe] using hgf
  · have hex : ∃ e ∈ A j, v ∈ D.localPart e := by
      by_contra hn
      push_neg at hn
      exact hi ((D.mem_input _ _).mpr hn)
    obtain ⟨e, he, hve⟩ := hex
    refine ⟨D.liftEdge σ e j, ⟨(D.liftEdge_mem_selection σ A e j).mpr he,
      D.local_mem_liftEdge σ e j hve⟩, ?_⟩
    intro g hg
    rcases D.incident_cases σ hg.1 hg.2 with ⟨f, hf, hvf, hgf⟩ | ⟨f, hf, hvf, hgf⟩
    · have hfe : f = e := by
        by_contra hne
        exact Finset.disjoint_left.mp ((hA.1 j).1 f hf e he hne) hvf hve
      simpa only [hfe] using hgf
    · have hout : v ∈ D.output (A (σ.symm j)) := (D.mem_output _ _).mpr ⟨f, hf, hvf⟩
      rw [hprev] at hout
      exact (hi hout).elim

 theorem perfect_iff_periodic :
    PerfectMatching (D.graph σ) (D.selection σ A) ↔ D.PeriodicConfig σ A :=
  ⟨D.matching_periodic σ, D.periodic_matching σ⟩

/-- The transfer correspondence is an equivalence of actual finite types. -/
noncomputable def configEquivMatching :
    {A : L → Finset E // D.PeriodicConfig σ A} ≃
      {M : Hypergraph (V × L) // PerfectMatching (D.graph σ) M} where
  toFun A := ⟨D.selection σ A.val, D.periodic_matching σ A.property⟩
  invFun M := ⟨D.take σ M.val, D.matching_periodic σ (by
    rw [D.selection_take σ M.property.subset]
    exact M.property)⟩
  left_inv := by
    intro A
    apply Subtype.ext
    exact D.take_selection σ A.val
  right_inv := by
    intro M
    apply Subtype.ext
    exact D.selection_take σ M.property.subset

end RigidGHZ.Supplement.Periodic.Scheme
