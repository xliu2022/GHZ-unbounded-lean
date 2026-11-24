module

public import RigidGHZ.Basic

@[expose] public section
namespace RigidGHZ.Finite

/-- The second edge of a two-edge perfect matching is the complement of the first. -/
theorem second_edge_eq_complement {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {e f : Finset V}
    (hM : PerfectMatching H {e, f}) (hef : e ≠ f) :
    f = Finset.univ \ e := by
  have hd : Disjoint e f := hM.disjoint_edges (by simp) (by simp) hef
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hf he
    exact Finset.disjoint_left.mp hd he hf
  · intro he
    obtain ⟨a, ha, _⟩ := hM.existsUnique_edge v
    have ham : a = e ∨ a = f := by simpa using ha.1
    rcases ham with rfl | rfl
    · exact False.elim (he ha.2)
    · exact ha.2

/-- Complementary-edge certificates imply complete enumeration of two-edge
perfect matchings in a uniform hypergraph. -/
theorem complete_of_complement_certificate {V : Type*} [Fintype V] [DecidableEq V]
    {I : Type*} {H : Hypergraph V} {r : ℕ} (hr : 0 < r)
    (hV : Fintype.card V = 2 * r) (hH : Uniform H r)
    (F : I → Hypergraph V)
    (cert : ∀ e ∈ H, ∃ i, ({e, Finset.univ \ e} : Hypergraph V) = F i) :
    ∀ M, PerfectMatching H M → ∃ i, M = F i := by
  intro M hM
  have hmul := hM.card_mul_eq hH
  rw [hV] at hmul
  have hcard : M.card = 2 := Nat.eq_of_mul_eq_mul_right hr hmul
  obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hcard
  have hc := second_edge_eq_complement hM hef
  obtain ⟨i, hi⟩ := cert e (hM.1 (by simp))
  exact ⟨i, by simpa only [← hc] using hi⟩

end RigidGHZ.Finite
