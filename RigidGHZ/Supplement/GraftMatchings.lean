module

public import RigidGHZ.Supplement.GraftData

/-! The prescribed grafted perfect matchings are edge-disjoint and exhaustive
as an edge decomposition. -/

@[expose] public section

namespace RigidGHZ.Supplement.Graft.Data

variable {V A W I : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq W]
  [Fintype A] [Fintype W] [Fintype I]
  {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)} (D : Data (I := I) H S)

 theorem prescribed_perfect (i : I) : PerfectMatching D.graph (D.matching i) := by
  apply PerfectMatching.of_existsUnique (D.matching_subset i)
  intro v
  cases v with
  | inl v =>
    obtain ⟨e, he, hu⟩ := (D.left.perfect i).existsUnique_edge (Sum.inl v)
    refine ⟨D.lifted e, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he.1, rfl⟩)
    · exact (D.mem_lifted_left e v).mpr he.2
    · intro f hf
      rcases Finset.mem_union.mp hf.1 with hfi | hfj
      · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfi
        exact congrArg D.lifted (hu e' ⟨he', (D.mem_lifted_left e' v).mp hf.2⟩)
      · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfj
        exact (mem_internal_left e' v hf.2).elim
  | inr aw =>
    rcases aw with ⟨a, w⟩
    by_cases hw : w = D.special i a
    · obtain ⟨e, he, hu⟩ := (D.left.perfect i).existsUnique_edge (Sum.inr a)
      refine ⟨D.lifted e, ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he.1, rfl⟩)
      · apply (D.mem_lifted_right e a w).mpr
        exact ⟨he.2, by rw [D.selector_on_matching he.1]; exact hw⟩
      · intro f hf
        rcases Finset.mem_union.mp hf.1 with hfi | hfj
        · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfi
          exact congrArg D.lifted (hu e' ⟨he', ((D.mem_lifted_right e' a w).mp hf.2).1⟩)
        · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfj
          obtain ⟨hne, he'⟩ := Finset.mem_erase.mp he'
          have hv : (a, w) ∈ e' := (mem_internal_right e' a w).mp hf.2
          have hs : (a, w) ∈ tupleEdge (D.special i) := mem_tupleEdge.mpr hw
          exact (hne ((D.right.perfect i).edge_eq_of_vertex he' (D.special_mem i) hv hs)).elim
    · obtain ⟨e, he, hu⟩ := (D.right.perfect i).existsUnique_edge (a, w)
      have hne : e ≠ tupleEdge (D.special i) := by
        intro heq
        rw [heq] at he
        exact hw (mem_tupleEdge.mp he.2)
      refine ⟨internalEdge e, ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨e, Finset.mem_erase.mpr ⟨hne, he.1⟩, rfl⟩)
      · exact (mem_internal_right e a w).mpr he.2
      · intro f hf
        rcases Finset.mem_union.mp hf.1 with hfi | hfj
        · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfi
          have hval := ((D.mem_lifted_right e' a w).mp hf.2).2
          rw [D.selector_on_matching he'] at hval
          exact (hw hval).elim
        · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hfj
          exact congrArg internalEdge (hu e' ⟨(Finset.mem_erase.mp he').2,
            (mem_internal_right e' a w).mp hf.2⟩)

 theorem prescribed_disjoint : Pairwise (fun i j => Disjoint (D.matching i) (D.matching j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  rcases Finset.mem_union.mp hei with hi | hi <;> rcases Finset.mem_union.mp hej with hj | hj
  · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hi
    obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp hj
    have hfg := D.lifted_injective (hfe.trans hge.symm)
    exact Finset.disjoint_left.mp (D.left.edge_disjoint hij) hf (by simpa only [hfg] using hg)
  · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hi
    obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp hj
    exact D.lifted_ne_internal f (D.mem_internal_of_erased hg) (hfe.trans hge.symm)
  · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hi
    obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp hj
    exact D.lifted_ne_internal g (D.mem_internal_of_erased hf) (hge.trans hfe.symm)
  · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hi
    obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp hj
    have hfg := internalEdge_injective (hfe.trans hge.symm)
    exact Finset.disjoint_left.mp (D.right.edge_disjoint hij) (Finset.mem_erase.mp hf).2
      (by simpa only [hfg] using (Finset.mem_erase.mp hg).2)

 theorem prescribed_covers : D.graph = Finset.univ.biUnion D.matching := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨i, hi⟩ := D.left.mem_iff.mp hf
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, hi, rfl⟩)⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hfS, hn⟩ := Finset.mem_filter.mp hf
      obtain ⟨i, hi⟩ := D.right.mem_iff.mp hfS
      have hne : f ≠ tupleEdge (D.special i) := by
        intro h; exact hn (h ▸ D.special_contains_root i)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨f, Finset.mem_erase.mpr ⟨hne, hi⟩, rfl⟩)⟩
  · intro he
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    exact D.matching_subset i he

end RigidGHZ.Supplement.Graft.Data
