module

public import RigidGHZ.Supplement.GraftProjection

/-! Exhaustiveness of the grafted perfect matchings. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Graft.Data

variable {V A W I : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq W]
  [Fintype A] [Fintype W] [Fintype I]
  {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)} (D : Data (I := I) H S)
  {P : Hypergraph (V ⊕ (A × W))} (hP : PerfectMatching D.graph P)

include hP

 theorem rightProjection_fibers {i : I} (hM : D.leftProjection P = D.left.matching i) (a : A) :
    matchingFiber (D.rightProjection P) a = Finset.univ.erase (D.special i a) := by
  ext w
  constructor
  · intro hw
    obtain ⟨e, he, hu⟩ := (D.left.perfect i).existsUnique_edge (Sum.inr a)
    have heM : e ∈ D.leftProjection P := by rw [hM]; exact he.1
    have hn := D.inherited_avoids_internal hP heM he.2
    have hsel := congrFun (D.selector_on_matching he.1) a
    rw [hsel] at hn
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hweq
    exact hn (by simpa only [hweq] using hw)
  · intro hw
    have hne := (Finset.mem_erase.mp hw).1
    obtain ⟨e, he, hu⟩ := hP.existsUnique_edge (Sum.inr (a, w))
    rcases Finset.mem_union.mp (hP.subset he.1) with heH | heS
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heH
      have hfM : f ∈ D.left.matching i := by
        rw [← hM]
        exact Finset.mem_filter.mpr ⟨hf, he.1⟩
      have hval := ((D.mem_lifted_right f a w).mp he.2).2
      rw [D.selector_on_matching hfM] at hval
      exact (hne hval).elim
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
      exact (mem_matchingFiber _ _ _).mpr ⟨f, Finset.mem_filter.mpr ⟨hf, he.1⟩,
        (mem_internal_right f a w).mp he.2⟩

 theorem rightProjection_complete {i : I} (hM : D.leftProjection P = D.left.matching i) :
    D.rightProjection P = (D.right.matching i).erase (tupleEdge (D.special i)) := by
  have hN : PerfectMatching S (insert (tupleEdge (D.special i)) (D.rightProjection P)) :=
    perfectMatching_insert_of_fibers (D.special i) D.rightProjection_subset
      ((D.right.perfect i).subset (D.special_mem i)) (D.rightProjection_disjoint hP)
      (D.rightProjection_fibers hP hM)
  obtain ⟨j, hj⟩ := D.right.complete _ hN
  have hij : i = j := D.right.eq_of_shared_edge (D.special_mem i) (by
    rw [← hj]
    exact Finset.mem_insert_self _ _)
  subst j
  have hn : tupleEdge (D.special i) ∉ D.rightProjection P := by
    intro h
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2 (D.special_contains_root i)
  have he := congrArg (fun N => N.erase (tupleEdge (D.special i))) hj
  simpa only [Finset.erase_insert hn] using he

 theorem prescribed_complete : ∃ i, P = D.matching i := by
  obtain ⟨i, hi⟩ := D.left.complete _ (D.leftProjection_perfect hP)
  refine ⟨i, ?_⟩
  rw [D.projection_decomposition hP, hi, D.rightProjection_complete hP hi]
  rfl

omit hP

/-- The graft is rigid as an ordinary finite simple hypergraph. -/
noncomputable def rigidFamily : RigidFamily D.graph I where
  matching := D.matching
  perfect := D.prescribed_perfect
  edge_disjoint := D.prescribed_disjoint
  covers := D.prescribed_covers
  complete := fun P hP => D.prescribed_complete hP

end RigidGHZ.Supplement.Graft.Data
