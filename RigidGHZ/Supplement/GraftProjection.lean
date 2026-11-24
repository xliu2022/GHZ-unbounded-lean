module

public import RigidGHZ.Supplement.GraftMatchings
public import RigidGHZ.Supplement.PartitePartial

/-! Projecting an arbitrary graft matching back to the original hypergraph. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Graft.Data

variable {V A W I : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq W]
  [Fintype A] [Fintype W] [Fintype I]
  {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)} (D : Data (I := I) H S)

noncomputable def leftProjection (P : Hypergraph (V ⊕ (A × W))) : Hypergraph (V ⊕ A) :=
  H.filter (fun e => D.lifted e ∈ P)

def rightProjection (P : Hypergraph (V ⊕ (A × W))) : Hypergraph (A × W) :=
  D.internal.filter (fun e => internalEdge e ∈ P)

variable {P : Hypergraph (V ⊕ (A × W))} (hP : PerfectMatching D.graph P)

 theorem rightProjection_subset : D.rightProjection P ⊆ S := by
  intro e he
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1

include hP

 theorem rightProjection_disjoint : ∀ e ∈ D.rightProjection P,
    ∀ f ∈ D.rightProjection P, e ≠ f → Disjoint e f := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  rintro ⟨a, w⟩ hve hvf
  have heP := (Finset.mem_filter.mp he).2
  have hfP := (Finset.mem_filter.mp hf).2
  have heq := hP.edge_eq_of_vertex heP hfP
    ((mem_internal_right e a w).mpr hve) ((mem_internal_right f a w).mpr hvf)
  exact hef (internalEdge_injective heq)

 theorem rightProjection_fiber_card (a : A) :
    (matchingFiber (D.rightProjection P) a).card = (D.rightProjection P).card := by
  apply matchingFiber_card _ _ (D.rightProjection_disjoint hP) a
  intro e he
  exact D.transversal e (D.rightProjection_subset he)

 theorem rightProjection_root :
    matchingFiber (D.rightProjection P) D.a0 = Finset.univ.erase D.w0 := by
  ext w
  constructor
  · intro hw
    obtain ⟨e, he, hwe⟩ := (mem_matchingFiber _ _ _).mp hw
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    exact hn (by simpa only [h] using hwe)
  · intro hw
    have hne := (Finset.mem_erase.mp hw).1
    obtain ⟨e, he, hu⟩ := hP.existsUnique_edge (Sum.inr (D.a0, w))
    rcases Finset.mem_union.mp (hP.subset he.1) with heH | heS
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heH
      have hval := ((D.mem_lifted_right f D.a0 w).mp he.2).2
      exact (hne (hval.trans (D.selector_root f))).elim
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
      exact (mem_matchingFiber _ _ _).mpr ⟨f, Finset.mem_filter.mpr ⟨hf, he.1⟩,
        (mem_internal_right f D.a0 w).mp he.2⟩

/-- There are precisely `|W|-1` internal edges in every graft matching. -/
theorem rightProjection_card : (D.rightProjection P).card = Fintype.card W - 1 := by
  rw [← D.rightProjection_fiber_card hP D.a0, D.rightProjection_root hP]
  simp

 theorem leftover_unique (a : A) : ∃! w : W, w ∉ matchingFiber (D.rightProjection P) a := by
  have hc : (Finset.univ \ matchingFiber (D.rightProjection P) a).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      D.rightProjection_fiber_card hP, D.rightProjection_card hP]
    have hp : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨D.w0⟩
    omega
  obtain ⟨w, hw, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hc
  refine ⟨w, (Finset.mem_sdiff.mp hw).2, ?_⟩
  intro z hz
  exact hu z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩)

 theorem inherited_avoids_internal {e : Finset (V ⊕ A)} (he : e ∈ D.leftProjection P)
    {a : A} (ha : Sum.inr a ∈ e) : D.selector e a ∉ matchingFiber (D.rightProjection P) a := by
  intro hmem
  obtain ⟨f, hf, hfv⟩ := (mem_matchingFiber _ _ _).mp hmem
  have heP := (Finset.mem_filter.mp he).2
  have hfP := (Finset.mem_filter.mp hf).2
  have hsame := hP.edge_eq_of_vertex heP hfP
    ((D.mem_lifted_right e a (D.selector e a)).mpr ⟨ha, rfl⟩)
    ((mem_internal_right f a (D.selector e a)).mpr hfv)
  exact D.lifted_ne_internal e (Finset.mem_filter.mp hf).1 hsame

 theorem inherited_of_uncovered (a : A) (w : W)
    (hw : w ∉ matchingFiber (D.rightProjection P) a) :
    ∃ e ∈ D.leftProjection P, Sum.inr a ∈ e ∧ w = D.selector e a := by
  obtain ⟨e, he, hu⟩ := hP.existsUnique_edge (Sum.inr (a, w))
  rcases Finset.mem_union.mp (hP.subset he.1) with heH | heS
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heH
    exact ⟨f, Finset.mem_filter.mpr ⟨hf, he.1⟩, (D.mem_lifted_right f a w).mp he.2⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
    exact (hw ((mem_matchingFiber _ _ _).mpr ⟨f, Finset.mem_filter.mpr ⟨hf, he.1⟩,
      (mem_internal_right f a w).mp he.2⟩)).elim

/-- Contracting the inherited edges gives an ordinary perfect matching of H. -/
theorem leftProjection_perfect : PerfectMatching H (D.leftProjection P) := by
  apply PerfectMatching.of_existsUnique (Finset.filter_subset _ _)
  intro v
  cases v with
  | inl v =>
    obtain ⟨e, he, hu⟩ := hP.existsUnique_edge (Sum.inl v)
    rcases Finset.mem_union.mp (hP.subset he.1) with heH | heS
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heH
      refine ⟨f, ⟨Finset.mem_filter.mpr ⟨hf, he.1⟩, (D.mem_lifted_left f v).mp he.2⟩, ?_⟩
      intro g hg
      apply D.lifted_injective
      exact hu (D.lifted g) ⟨(Finset.mem_filter.mp hg.1).2,
        (D.mem_lifted_left g v).mpr hg.2⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
      exact (mem_internal_left f v he.2).elim
  | inr a =>
    obtain ⟨w, hw, hu⟩ := D.leftover_unique hP a
    obtain ⟨e, he, hea, hew⟩ := D.inherited_of_uncovered hP a w hw
    refine ⟨e, ⟨he, hea⟩, ?_⟩
    intro f hf
    have hfw : D.selector f a = w := hu _ (D.inherited_avoids_internal hP hf.1 hf.2)
    apply D.lifted_injective
    exact hP.edge_eq_of_vertex (Finset.mem_filter.mp hf.1).2 (Finset.mem_filter.mp he).2
      ((D.mem_lifted_right f a w).mpr ⟨hf.2, hfw.symm⟩)
      ((D.mem_lifted_right e a w).mpr ⟨hea, hew⟩)

 theorem projection_decomposition : P =
    (D.leftProjection P).image D.lifted ∪ (D.rightProjection P).image internalEdge := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp (hP.subset he) with heH | heS
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heH
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, he⟩, rfl⟩)
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, he⟩, rfl⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he <;>
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he <;>
      exact (Finset.mem_filter.mp hf).2

end RigidGHZ.Supplement.Graft.Data
