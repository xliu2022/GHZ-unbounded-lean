module

public import RigidGHZ.Basic

@[expose] public section

namespace RigidGHZ.Finite

/-- In a perfect matching with three distinct edges, one edge is the complement
of the other two. This supplies the bridge from a finite pair certificate to
ordinary perfect-matching completeness. -/
theorem third_edge_eq_complement {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {e f g : Finset V}
    (hM : PerfectMatching H {e, f, g}) (heg : e ≠ g) (hfg : f ≠ g) :
    g = Finset.univ \ (e ∪ f) := by
  have heg' : Disjoint e g := hM.disjoint_edges (by simp) (by simp) heg
  have hfg' : Disjoint f g := hM.disjoint_edges (by simp) (by simp) hfg
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
  constructor
  · intro hg
    exact ⟨fun he => Finset.disjoint_left.mp heg' he hg,
      fun hf => Finset.disjoint_left.mp hfg' hf hg⟩
  · rintro ⟨he, hf⟩
    obtain ⟨a, ha, _⟩ := hM.existsUnique_edge v
    have ham : a = e ∨ a = f ∨ a = g := by simpa using ha.1
    rcases ham with rfl | rfl | rfl
    · exact False.elim (he ha.2)
    · exact False.elim (hf ha.2)
    · exact ha.2

/-- A three-edge-completion certificate proves exhaustiveness for a list of
matchings in a uniform hypergraph on three times the edge size vertices. -/
theorem complete_of_pair_certificate {V : Type*} [Fintype V] [DecidableEq V]
    {I : Type*} {H : Hypergraph V} {r : ℕ} (hr : 0 < r)
    (hV : Fintype.card V = 3 * r) (hH : Uniform H r)
    (F : I → Hypergraph V)
    (cert : ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
      (Finset.univ \ (e ∪ f)) ∈ H →
      ∃ i, ({e, f, Finset.univ \ (e ∪ f)} : Hypergraph V) = F i) :
    ∀ M, PerfectMatching H M → ∃ i, M = F i := by
  intro M hM
  have hmul := hM.card_mul_eq hH
  rw [hV] at hmul
  have hcard : M.card = 3 := Nat.eq_of_mul_eq_mul_right hr hmul
  obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := Finset.card_eq_three.mp hcard
  have he : e ∈ H := hM.1 (by simp)
  have hf : f ∈ H := hM.1 (by simp)
  have hg : g ∈ H := hM.1 (by simp)
  have hc := third_edge_eq_complement hM heg hfg
  have hg' : (Finset.univ \ (e ∪ f)) ∈ H := by rwa [← hc]
  obtain ⟨i, hi⟩ := cert e he f hf (hM.disjoint_edges (by simp) (by simp) hef) hg'
  exact ⟨i, by simpa only [← hc] using hi⟩

end RigidGHZ.Finite
