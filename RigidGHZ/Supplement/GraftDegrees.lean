module

public import RigidGHZ.Supplement.GraftComplete
public import RigidGHZ.UpperBounds.ShadowCombinatorics

/-! The graft preserves every positive-order maximum codegree bound. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement

open UpperBounds

/-- Maximum number of edges containing a set of `j` vertices; zero if there
is no such vertex set. -/
def maxDegree {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph V) (j : ℕ) : ℕ :=
  (Finset.univ.powersetCard j).sup (codegree H)

 theorem codegree_le_maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (X : Finset V) : codegree H X ≤ maxDegree H X.card := by
  apply Finset.le_sup
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩

 theorem maxDegree_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (j d : ℕ) (h : ∀ X : Finset V, X.card = j → codegree H X ≤ d) :
    maxDegree H j ≤ d := by
  apply Finset.sup_le
  intro X hX
  exact h X (Finset.mem_powersetCard.mp hX).2

namespace Graft

variable {V A W I : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq W]
  [Fintype A] [Fintype W] [Fintype I]
  {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)}

 theorem contract_injOn_inherit (z : A → W) (e : Finset (V ⊕ A)) :
    Set.InjOn contractVertex (inheritEdge z e : Set (V ⊕ (A × W))) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
  have hleft : ∀ w : V ⊕ A, contractVertex (inheritVertex z w) = w := by
    intro w; cases w <;> rfl
  simp only [hleft] at hxy
  rw [hxy]

namespace Data

variable (D : Data (I := I) H S)

 theorem codegree_with_retained {X : Finset (V ⊕ (A × W))} {v : V}
    (hv : Sum.inl v ∈ X) (hne : (D.graph.filter (fun e => X ⊆ e)).Nonempty) :
    (contractEdge X).card = X.card ∧ codegree D.graph X ≤ codegree H (contractEdge X) := by
  classical
  have inherited : ∀ e ∈ D.graph.filter (fun e => X ⊆ e), ∃ f ∈ H, e = D.lifted f := by
    intro e he
    obtain ⟨heG, hXe⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_union.mp heG with heH | heS
    · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp heH
      exact ⟨f, hf, hfe.symm⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp heS
      exact (mem_internal_left f v (hXe hv)).elim
  obtain ⟨e, he⟩ := hne
  obtain ⟨f, hf, hfe⟩ := inherited e he
  have hinjX : Set.InjOn contractVertex (X : Set (V ⊕ (A × W))) :=
    (contract_injOn_inherit (D.selector f) f).mono (by
      intro x hx
      change x ∈ D.lifted f
      rw [← hfe]
      exact (Finset.mem_filter.mp he).2 hx)
  refine ⟨Finset.card_image_of_injOn hinjX, ?_⟩
  apply Finset.card_le_card_of_injOn contractEdge
  · intro e he
    obtain ⟨f, hf, rfl⟩ := inherited e he
    apply Finset.mem_filter.mpr
    refine ⟨by simpa only [lifted, contract_inherit] using hf, ?_⟩
    exact Finset.image_subset_image (Finset.mem_filter.mp he).2
  · intro e he f hf hef
    obtain ⟨u, hu, rfl⟩ := inherited e he
    obtain ⟨v, hv, rfl⟩ := inherited f hf
    have huv : u = v := by simpa only [lifted, contract_inherit] using hef
    rw [huv]

/-- An internal edge remembers itself; an inherited edge remembers the deleted
right edge of its matching color. -/
def SourceRel (g : Finset (V ⊕ (A × W))) (e : Finset (A × W)) : Prop :=
  (g = internalEdge e ∧ e ∈ D.internal) ∨
    ∃ i f, f ∈ D.left.matching i ∧ g = D.lifted f ∧ e = tupleEdge (D.special i)

 theorem sourceRel_exists {g : Finset (V ⊕ (A × W))} (hg : g ∈ D.graph) :
    ∃ e ∈ S, D.SourceRel g e := by
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨i, hi⟩ := D.left.mem_iff.mp hf
    exact ⟨tupleEdge (D.special i), (D.right.perfect i).subset (D.special_mem i),
      Or.inr ⟨i, f, hi, rfl, rfl⟩⟩
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl ⟨rfl, he⟩⟩

 theorem sourceRel_contains {Y : Finset (A × W)} {g : Finset (V ⊕ (A × W))}
    {e : Finset (A × W)} (hY : internalEdge Y ⊆ g) (h : D.SourceRel g e) : Y ⊆ e := by
  intro y hy
  rcases y with ⟨a, w⟩
  rcases h with ⟨rfl, he⟩ | ⟨i, f, hf, rfl, rfl⟩
  · exact (mem_internal_right e a w).mp (hY ((mem_internal_right Y a w).mpr hy))
  · have hv := ((D.mem_lifted_right f a w).mp (hY ((mem_internal_right Y a w).mpr hy))).2
    rw [D.selector_on_matching hf] at hv
    exact mem_tupleEdge.mpr hv

 theorem sourceRel_injective {X : Finset (V ⊕ (A × W))} (hX : X.Nonempty)
    {g h : Finset (V ⊕ (A × W))} {e : Finset (A × W)}
    (hg : X ⊆ g) (hh : X ⊆ h) (hge : D.SourceRel g e) (hhe : D.SourceRel h e) : g = h := by
  rcases hge with ⟨rfl, he⟩ | ⟨i, f, hf, rfl, hei⟩ <;>
    rcases hhe with ⟨rfl, he'⟩ | ⟨j, f', hf', rfl, hej⟩
  · rfl
  · exact ((Finset.mem_filter.mp he).2 (hej ▸ D.special_contains_root j)).elim
  · exact ((Finset.mem_filter.mp he').2 (hei ▸ D.special_contains_root i)).elim
  · have hij : i = j := D.right.eq_of_shared_edge (D.special_mem i) (by
      rw [← hei, hej]
      exact D.special_mem j)
    subst j
    obtain ⟨x, hx⟩ := hX
    apply (D.prescribed_perfect i).edge_eq_of_vertex
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, hf, rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f', hf', rfl⟩))
      (hg hx) (hh hx)

 theorem codegree_internal (Y : Finset (A × W)) (hY : Y.Nonempty) :
    codegree D.graph (internalEdge Y) ≤ codegree S Y := by
  classical
  let L := D.graph.filter (fun e => internalEdge Y ⊆ e)
  let R := S.filter (fun e => Y ⊆ e)
  have hex : ∀ g : ↥L, ∃ e : ↥R, D.SourceRel g.val e.val := by
    intro g
    obtain ⟨e, he, hrel⟩ := D.sourceRel_exists (Finset.mem_filter.mp g.property).1
    exact ⟨⟨e, Finset.mem_filter.mpr ⟨he,
      D.sourceRel_contains (Finset.mem_filter.mp g.property).2 hrel⟩⟩, hrel⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f := f)
  intro g h heq
  apply Subtype.ext
  exact D.sourceRel_injective (hY.map) (Finset.mem_filter.mp g.property).2
    (Finset.mem_filter.mp h.property).2 (hf g) (by simpa only [heq] using hf h)

 theorem positive_degree_bound {j d : ℕ} (hj : 1 ≤ j)
    (hH : ∀ X : Finset (V ⊕ A), X.card = j → codegree H X ≤ d)
    (hS : ∀ X : Finset (A × W), X.card = j → codegree S X ≤ d)
    (X : Finset (V ⊕ (A × W))) (hc : X.card = j) : codegree D.graph X ≤ d := by
  classical
  by_cases hi : (D.graph.filter (fun e => X ⊆ e)).Nonempty
  · by_cases hleft : ∃ v : V, Sum.inl v ∈ X
    · obtain ⟨v, hv⟩ := hleft
      obtain ⟨hcard, hle⟩ := D.codegree_with_retained hv hi
      exact hle.trans (hH _ (hcard.trans hc))
    · let Y : Finset (A × W) := Finset.univ.filter (fun y => Sum.inr y ∈ X)
      have hXY : internalEdge (V := V) Y = X := by
        ext x
        cases x with
        | inl v => simp only [mem_internal_left, false_iff]; exact fun h => hleft ⟨v, h⟩
        | inr y => rcases y with ⟨a, w⟩; simp [Y]
      have hYcard : Y.card = j := by rw [← internalEdge_card (V := V) Y, hXY, hc]
      have hYpos : Y.Nonempty := Finset.card_pos.mp (by omega)
      rw [← hXY]
      exact (D.codegree_internal Y hYpos).trans (hS Y hYcard)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hi
    change (D.graph.filter (fun e => X ⊆ e)).card ≤ d
    rw [hempty]
    exact Nat.zero_le _

 theorem maxDegree_le [Fintype V] (j : ℕ) (hj : 1 ≤ j) :
    maxDegree D.graph j ≤ max (maxDegree H j) (maxDegree S j) := by
  apply Supplement.maxDegree_le
  apply D.positive_degree_bound hj
  · intro X hX
    have h : codegree H X ≤ maxDegree H j := by simpa only [hX] using codegree_le_maxDegree H X
    exact h.trans (Nat.le_max_left _ _)
  · intro X hX
    have h : codegree S X ≤ maxDegree S j := by simpa only [hX] using codegree_le_maxDegree S X
    exact h.trans (Nat.le_max_right _ _)

end Data
end Graft
end RigidGHZ.Supplement
