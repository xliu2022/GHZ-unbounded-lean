module

public import RigidGHZ.Finite.PairNormalization

@[expose] public section

namespace RigidGHZ.Finite

theorem relabel_triple (f : Equiv.Perm (Fin 9)) (a b c : Fin 9) :
    relabelEdge f ({a, b, c} : Finset (Fin 9)) = {f a, f b, f c} := by
  simp [relabelEdge]

theorem relabel_triple_mem (H : Hypergraph (Fin 9)) (f : Equiv.Perm (Fin 9)) (a b c : Fin 9) :
    ({f a, f b, f c} : Finset (Fin 9)) ∈ relabelHypergraph f H ↔
      ({a, b, c} : Finset (Fin 9)) ∈ H := by
  rw [← relabel_triple, relabelEdge_mem_relabelHypergraph]

theorem pairCompletions_relabel (H : Hypergraph (Fin 9)) (f : Equiv.Perm (Fin 9)) (a b : Fin 9) :
    pairCompletions (relabelHypergraph f H) (f a) (f b) =
      (pairCompletions H a b).map f.toEmbedding := by
  ext x
  obtain ⟨y, rfl⟩ := f.surjective x
  constructor
  · intro h
    simp only [pairCompletions, Finset.mem_filter, Finset.mem_univ, true_and] at h
    apply Finset.mem_map.mpr
    refine ⟨y, ?_, rfl⟩
    simp only [pairCompletions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hy => h.1 (congrArg f hy), fun hy => h.2.1 (congrArg f hy),
      (relabel_triple_mem H f a b y).mp h.2.2⟩
  · intro h
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp h
    have he : z = y := f.injective hzy
    subst z
    simp only [pairCompletions, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨fun hy => hz.1 (f.injective hy), fun hy => hz.2.1 (f.injective hy),
      (relabel_triple_mem H f a b y).mpr hz.2.2⟩

theorem pairCompletions_card_relabel (H : Hypergraph (Fin 9)) (f : Equiv.Perm (Fin 9))
    (a b : Fin 9) :
    (pairCompletions (relabelHypergraph f H) a b).card =
      (pairCompletions H (f.symm a) (f.symm b)).card := by
  have h := congrArg Finset.card (pairCompletions_relabel H f (f.symm a) (f.symm b))
  simpa only [Equiv.apply_symm_apply, Finset.card_map] using h

theorem pair_bound_relabel {H : Hypergraph (Fin 9)} {k : ℕ}
    (hmax : ∀ a b : Fin 9, a ≠ b → (pairCompletions H a b).card ≤ k)
    (f : Equiv.Perm (Fin 9)) :
    ∀ a b : Fin 9, a ≠ b → (pairCompletions (relabelHypergraph f H) a b).card ≤ k := by
  intro a b hab
  rw [pairCompletions_card_relabel]
  exact hmax _ _ (fun h => hab (f.symm.injective h))

theorem normalized_pair_transport {H : Hypergraph (Fin 9)} {k : ℕ}
    (hnorm : ∀ x : Fin 9, x ≠ 0 → x ≠ 1 →
      (({0, 1, x} : Finset (Fin 9)) ∈ H ↔ 2 ≤ x.val ∧ x.val < 2 + k))
    (f : Equiv.Perm (Fin 9)) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hpres : ∀ x : Fin 9, (2 ≤ x.val ∧ x.val < 2 + k) ↔
      (2 ≤ (f x).val ∧ (f x).val < 2 + k)) :
    ∀ x : Fin 9, x ≠ 0 → x ≠ 1 →
      (({0, 1, x} : Finset (Fin 9)) ∈ relabelHypergraph f H ↔
        2 ≤ x.val ∧ x.val < 2 + k) := by
  intro x hx0 hx1
  have hy0 : f.symm x ≠ 0 := by
    intro h
    apply hx0
    rw [← h0, ← h, Equiv.apply_symm_apply]
  have hy1 : f.symm x ≠ 1 := by
    intro h
    apply hx1
    rw [← h1, ← h, Equiv.apply_symm_apply]
  have he := relabel_triple_mem H f 0 1 (f.symm x)
  rw [h0, h1, Equiv.apply_symm_apply] at he
  rw [he, hnorm _ hy0 hy1]
  simpa only [Equiv.apply_symm_apply] using hpres (f.symm x)

end RigidGHZ.Finite
