module

public import RigidGHZ.Supplement.GraftBalanced

/-! Supplemental Theorem S3.1 on arbitrary finite simple hypergraphs. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement

variable {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
  [DecidableEq V] [DecidableEq W]

/-- Grafting an ordinary rigid hypergraph with a balanced rigid hypergraph,
including all positive-order maximum codegree bounds. -/
theorem grafting {H : Hypergraph V} {S : Hypergraph W} {r m q : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) (hcard : Fintype.card V = r * m)
    (hH : Uniform H r) (L : RigidFamily H I) (hS : BalancedPartite S r q)
    (R : RigidFamily S I) :
    ∃ G : Hypergraph (Fin (r * (m + q - 1))), Uniform G r ∧
      Nonempty (RigidFamily G I) ∧
      ∀ j : ℕ, 1 ≤ j → maxDegree G j ≤ max (maxDegree H j) (maxDegree S j) := by
  classical
  have hcount : Fintype.card V = Fintype.card (Fin (r * (m - 1)) ⊕ Fin r) := by
    simp only [Fintype.card_sum, Fintype.card_fin, hcard]
    have he : m - 1 + 1 = m := by omega
    nlinarith
  let f : V ≃ (Fin (r * (m - 1)) ⊕ Fin r) := Fintype.equivOfCardEq hcount
  obtain ⟨g, hg⟩ := hS.canonical
  have hSunif : Uniform (relabelHypergraph g S) r := by
    intro e he
    obtain ⟨x, rfl⟩ := hg e he
    simpa only [Fintype.card_fin] using tupleEdge_card x
  obtain ⟨D⟩ := Graft.data_nonempty (L.relabel f) (R.relabel g)
    (⟨0, by omega⟩ : Fin r) (⟨0, by omega⟩ : Fin q) hg
  have hnew : Fintype.card (Fin (r * (m - 1)) ⊕ (Fin r × Fin q)) = r * (m + q - 1) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hmq : m + q - 1 = (m - 1) + q := by omega
    rw [hmq]
    ring
  let e := Fintype.equivFinOfCardEq hnew
  refine ⟨relabelHypergraph e D.graph, (D.graph_uniform (hH.relabel f) hSunif).relabel e,
    ⟨D.rigidFamily.relabel e⟩, ?_⟩
  intro j hj
  rw [maxDegree_relabel]
  have hd := D.maxDegree_le j hj
  simpa only [maxDegree_relabel] using hd

/-- The balanced version of grafting, with the same degree estimate. -/
theorem grafting_balanced {H : Hypergraph V} {S : Hypergraph W} {r m q : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hH : BalancedPartite H r m) (L : RigidFamily H I)
    (hS : BalancedPartite S r q) (R : RigidFamily S I) :
    ∃ G : Hypergraph (Fin r × Fin (m + q - 1)), Uniform G r ∧
      BalancedPartite G r (m + q - 1) ∧ Nonempty (RigidFamily G I) ∧
      ∀ j : ℕ, 1 ≤ j → maxDegree G j ≤ max (maxDegree H j) (maxDegree S j) := by
  classical
  obtain ⟨f, hf⟩ := hH.canonical
  obtain ⟨g, hg⟩ := hS.canonical
  let t : Fin m ≃ Option (Fin (m - 1)) := Fintype.equivOfCardEq (by simp; omega)
  let t' := Equiv.prodCongr (Equiv.refl (Fin r)) t
  have ht := ground_relabel_transversal t (relabelHypergraph f H) hf
  obtain ⟨G, hUG, hPG, ⟨RG⟩, hDG⟩ := Graft.balanced_family
    ((L.relabel f).relabel t') (R.relabel g)
    (⟨0, by omega⟩ : Fin r) (⟨0, by omega⟩ : Fin q) ht hg
  have hP : BalancedPartite G r (m + q - 1) := by
    have hc : m - 1 + q = m + q - 1 := by omega
    simpa only [Fintype.card_fin, hc] using hPG
  obtain ⟨e, he⟩ := hP.canonical
  refine ⟨relabelHypergraph e G, ?_, ?_, ⟨RG.relabel e⟩, ?_⟩
  · simpa only [Fintype.card_fin] using hUG.relabel e
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal _ he
  · intro j hj
    rw [maxDegree_relabel]
    simpa only [maxDegree_relabel] using hDG j hj

end RigidGHZ.Supplement
