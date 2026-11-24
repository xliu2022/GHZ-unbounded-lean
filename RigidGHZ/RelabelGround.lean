module

public import RigidGHZ.Relabel

/-! Coordinate-preserving relabeling of the common ground set. -/

@[expose] public section

namespace RigidGHZ

variable {A V W : Type*} [Fintype A] [DecidableEq A] [DecidableEq V] [DecidableEq W]

@[simp] theorem relabelEdge_ground (f : V ≃ W) (x : A → V) :
    relabelEdge (Equiv.prodCongr (Equiv.refl A) f) (tupleEdge x) = tupleEdge (f ∘ x) := by
  ext z
  rcases z with ⟨a, w⟩
  simp only [mem_relabelEdge, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, mem_tupleEdge, Function.comp_apply]
  exact f.symm_apply_eq

 theorem ground_relabel_transversal (f : V ≃ W) (H : Hypergraph (A × V))
    (htrans : ∀ e ∈ H, ∃ x : A → V, e = tupleEdge x) :
    ∀ e ∈ relabelHypergraph (Equiv.prodCongr (Equiv.refl A) f) H,
      ∃ x : A → W, e = tupleEdge x := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨x, rfl⟩ := htrans e0 he0
  exact ⟨f ∘ x, relabelEdge_ground f x⟩

 theorem ground_relabel_support (f : V ≃ W) (H : Hypergraph (Fin 3 × V)) (U : Finset V)
    (hsupport : ∀ x : Fin 3 → V, tupleEdge x ∈ H →
      (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) :
    ∀ x : Fin 3 → W,
      tupleEdge x ∈ relabelHypergraph (Equiv.prodCongr (Equiv.refl (Fin 3)) f) H →
      (x 0 ∈ relabelEdge f U ∧ x 1 ∈ relabelEdge f U) ∨
        (x 0 = x 1 ∧ x 0 ∉ relabelEdge f U) := by
  intro x hx
  have he : relabelEdge (Equiv.prodCongr (Equiv.refl (Fin 3)) f)
      (tupleEdge (f.symm ∘ x)) = tupleEdge x := by
    rw [relabelEdge_ground]
    congr 1
    funext a
    exact f.apply_symm_apply (x a)
  have hback : tupleEdge (f.symm ∘ x) ∈ H :=
    (relabelEdge_mem_relabelHypergraph _ _ H).mp (by rwa [he])
  have hs := hsupport (f.symm ∘ x) hback
  simp only [Function.comp_apply] at hs
  simp only [mem_relabelEdge]
  rcases hs with hs | hs
  · exact Or.inl hs
  · exact Or.inr ⟨f.symm.injective hs.1, hs.2⟩

end RigidGHZ
